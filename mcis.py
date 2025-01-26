# Hacked version for bigraphs!

# Original version: https://github.com/networkx/networkx/pull/4221

"""Maximum common induced subgraph algorithms

A common induced subgraph of graphs $G$ and $H$ is an induced subgraph of $G$
that is isomorphic to an induced subgraph of $H$.  A `maximum common induced
subgraph`_ is a common induced subgraph with as many nodes as possible.

The function :func:`max_common_induced_subgraph` finds the maximum common
induced subgraph of two graphs using a variant of the McSplit algorithm. [1]_
The function :func:`common_induced_subgraph` solves the decision problem: for a
given `target`, it finds a common induced subgraph with at least `target` nodes,
if one exists.  Both of these functions can optionally be called with the
restriction that the common subgraph be connected.

The function :func:`weak_modular_product_mcis` provides an alternative approach to
solving the optimisation problem: it finds a maximum clique in the weak modular
product graph. [2]_

The function :func:`ismags_mcis` is a wrapper for convienience around
:func:`networkx.algorithms.isomorphism.ISMAGS.largest_common_subgraph`; this
provides another alternative approach to solving the optimisation problem.

.. _`maximum common induced subgraph`: https://en.wikipedia.org/wiki/Maximum_common_induced_subgraph
.. [1] McCreesh, C., Prosser, P., & Trimble, J. (2017). A partitioning
   algorithm for maximum common subgraph problems. In Proceedings of the 26th
   International Joint Conference on Artificial Intelligence (pp. 712-719).
   https://www.ijcai.org/Proceedings/2017/0099.pdf
.. [2] Levi, G. (1973), "A note on the derivation of maximal common subgraphs
   of two directed or undirected graphs", Calcolo, 9 (4): 341–352,
   doi:10.1007/BF02575586.
"""

import itertools

import networkx as nx

__all__ = [
    "max_common_induced_subgraph",
    "weak_modular_product_mcis",
    "ismags_mcis",
    "common_induced_subgraph",
]


def _label_function(label):
    """Returns a function that returns the label of a node or edge.

    In general, maximum common induced subgraph functions should call this
    function twice: once to create a node label function and once to create
    an edge label function.

    Parameters
    ----------
    G : NetworkX graph.

    label : string, function or None
        If it is callable, `label` itself is returned. If it is None, a
        function that simply returns the value 1 is returned.  If `label` is a
        string, it is assumed to be the name of the node or edge attribute that
        represents the label of a node or edge. In that case, a function is
        returned that gets the node or edge label according to the specified
        node or edge attribute.

    Returns
    -------
    function
        This function returns a callable that accepts exactly one input:
        a node or edge.  That function returns the label of the given node
        or edge.  Each label must be hashable, and edge labels must not be
        None.
    """
    if label is None:
        return lambda data: 1
    if callable(label):
        return label
    return lambda data: data[label]


def get_edge_label(G, edge_label_fun, node_a, node_b, directed):
    """Return the label of an edge, or None if the two nodes are not adjacent"""
    if G.has_edge(node_a, node_b):
        return edge_label_fun(G.edges[node_a, node_b])
    elif directed and G.has_edge(node_b, node_a):
        return edge_label_fun(G.edges[node_b, node_a])*2
    else:
        return None

class LabelClass:
    """A label class, used by the McSplit algorithm.

    A label class contains a list of nodes from graph G and a list of nodes
    from graph H to which these may be mapped.  The `is_adjacent` member is
    a boolean which is true if and only if the nodes in the label class are
    adjacent to at least one node of the current subgraph.
    """

    __slots__ = ["G_nodes", "H_nodes", "is_adjacent", "is_port", "transitive_G_nodes", "transitive_H_nodes"]

    def __init__(self, is_adjacent, is_port):
        self.G_nodes = []
        self.H_nodes = []
        self.is_adjacent = is_adjacent
        self.is_port = is_port
        self.transitive_G_nodes = []
        self.transitive_H_nodes = []
    def __repr__(self):
        return f"{self.G_nodes}, {self.H_nodes}"


class PartitioningMCISFinder:
    """A class implementing a variant of the McSplit algorithm"""

    __slots__ = ["G", "H", "connected", "directed", "bigraph", "LTS", "node_label_fun", "edge_label_fun", "all_instances_soln_set", "g_transitive_matrix", \
                 "h_transitive_matrix", "forbid_pairs_matrix"]

    def __init__(self, G, H, connected, directed, bigraph, LTS, node_label_fun, edge_label_fun):
        self.G = G
        self.H = H
        self.connected = connected
        self.directed = directed
        self.bigraph = bigraph
        self.LTS = LTS
        self.node_label_fun = node_label_fun
        self.edge_label_fun = edge_label_fun
        self.all_instances_soln_set = []

        if(bigraph):
            self.g_transitive_matrix = build_transitive_matrix(G)
            self.h_transitive_matrix = build_transitive_matrix(H)

        if(bigraph and LTS):
            self.forbid_pairs_matrix = build_forbidden_pairs_matrix(G, H)

    def all_parents_assigned(self, v, G, assignments):
        for p in G.pred[v]:
            if p not in assignments:
                return False
        return True
    
    def all_entity_children_assigned(self, v, G, assignments):
        for p in G.succ[v]:
            if type(G.nodes[p]) == int and p not in assignments:
                return False
        return True
    
    def check_LTS_solution(self, assignments):
        region_lock = {}
        face_lock = {}
        for v in assignments:
            if(type(v) == int):
                parents = list(self.G.pred[v])
                if(len(parents) == 1):
                    parent = parents[0]
                    if(parent not in assignments.keys() and self.H.nodes[assignments[v]]['root_adj'] == None):
                        return False # no region exists for composing minimal context onto
                if(self.H.nodes[assignments[v]]['root_adj'] != None):
                    compose = None
                    if(len(parents) == 1):
                        compose = parents[0]
                    elif self.G.nodes[v]['root_adj'] != None:
                        compose = "open"
                    else:
                        compose = "close"
                    if self.H.nodes[assignments[v]]['root_adj'] not in region_lock:
                        region_lock[self.H.nodes[assignments[v]]['root_adj']] = compose
                    else:
                        if compose != region_lock[self.H.nodes[assignments[v]]['root_adj']]:
                            return False # trying to compose two multiple elements onto one region slot
            elif(v[:5] == "link-"):
                children = list(self.G.succ[v])
                if(len(children) == 1):
                    child = children[0]
                    if(child not in assignments.keys() and len(self.H.succ[child]) > 0):
                        return False # cannot compose closure onto an already closed port
                if(type(self.H.nodes[assignments[v]]['face']) == str):
                    compose = None
                    if(len(children) == 1):
                        compose = children[0]
                    else:
                        compose = "open"
                    if self.H.nodes[assignments[v]]['face'] not in face_lock:
                        face_lock[self.H.nodes[assignments[v]]['face']] = compose
                    else:
                        if compose != face_lock[self.H.nodes[assignments[v]]['face']]:
                            return False # trying to compose multiple closures onto one face 
        return True

    def refine_label_classes(self, label_classes, v, w, assignments):
        new_label_classes = []
        for lc in label_classes:
            label_to_new_lc = {}
            for u in lc.G_nodes:
                edge_label = get_edge_label(self.G, self.edge_label_fun, v, u, (self.directed or self.bigraph))
                if edge_label not in label_to_new_lc:
                    is_adjacent = lc.is_adjacent or self.G.has_edge(v, u) or ((self.directed or self.bigraph) and self.G.has_edge(u, v))
                    label_to_new_lc[edge_label] = LabelClass(is_adjacent, lc.is_port)
                label_to_new_lc[edge_label].G_nodes.append(u)
            for u in lc.transitive_G_nodes:
                edge_label = get_edge_label(self.G, self.edge_label_fun, v, u, (self.directed or self.bigraph))
                if edge_label not in label_to_new_lc:
                    is_adjacent = lc.is_adjacent or self.G.has_edge(v, u) or ((self.directed or self.bigraph) and self.G.has_edge(u, v))
                    label_to_new_lc[edge_label] = LabelClass(is_adjacent, lc.is_port)
                label_to_new_lc[edge_label].transitive_G_nodes.append(u)                
            for u in lc.H_nodes:
                edge_label = get_edge_label(self.H, self.edge_label_fun, w, u, (self.directed or self.bigraph))
                if edge_label in label_to_new_lc:
                    label_to_new_lc[edge_label].H_nodes.append(u)
            for u in lc.transitive_H_nodes:
                edge_label = get_edge_label(self.H, self.edge_label_fun, w, u, (self.directed or self.bigraph))
                if edge_label in label_to_new_lc:
                    label_to_new_lc[edge_label].transitive_H_nodes.append(u)
            for new_lc in label_to_new_lc.values():
                if new_lc.H_nodes or new_lc.transitive_H_nodes:
                    if self.bigraph:
                        closed_label = (type([new_lc.G_nodes + new_lc.transitive_G_nodes][0][0]) == str) and \
                            ("closure" in [new_lc.G_nodes + new_lc.transitive_G_nodes][0][0])
                        if new_lc.is_adjacent and not closed_label:
                            new_lc.H_nodes = new_lc.H_nodes + new_lc.transitive_H_nodes
                            new_lc.transitive_H_nodes = []
                            if not self.LTS:
                                new_lc.G_nodes = new_lc.G_nodes + new_lc.transitive_G_nodes
                                new_lc.transitive_G_nodes = []
                            else:
                                for u in new_lc.transitive_G_nodes:
                                    if self.all_entity_children_assigned(u, self.G, assignments.keys()):
                                        new_lc.G_nodes.append(u)
                                        new_lc.transitive_G_nodes.remove(u) 
                        elif closed_label:
                            for u in new_lc.transitive_G_nodes:
                                if self.all_parents_assigned(u, self.G, assignments.keys()):
                                    new_lc.G_nodes.append(u)
                                    new_lc.transitive_G_nodes.remove(u)
                            for u in new_lc.transitive_H_nodes:
                                if self.all_parents_assigned(u, self.H, assignments.values()):
                                    new_lc.H_nodes.append(u)
                                    new_lc.transitive_H_nodes.remove(u)
                        elif type([new_lc.G_nodes + new_lc.transitive_G_nodes][0][0]) == int and self.G.nodes[v]['arity'] >= 0:
                            for u in new_lc.G_nodes:
                                if self.g_transitive_matrix[self.G.nodes[u]['index']][self.G.nodes[v]['index']] == 1 or \
                                    self.g_transitive_matrix[self.G.nodes[v]['index']][self.G.nodes[u]['index']] == 1:
                                        new_lc.transitive_G_nodes.append(u)
                                        new_lc.G_nodes.remove(u)
                            for u in new_lc.H_nodes:
                                if self.h_transitive_matrix[self.H.nodes[u]['index']][self.H.nodes[w]['index']] == 1 or \
                                    self.h_transitive_matrix[self.H.nodes[w]['index']][self.H.nodes[u]['index']] == 1:
                                        new_lc.transitive_H_nodes.append(u)
                                        new_lc.H_nodes.remove(u)
                    new_label_classes.append(new_lc)
        return new_label_classes

    def select_label_class(self, label_classes, assignment_count, arity_countdown):
        if self.connected and assignment_count > 0:
            candidates = [lc for lc in label_classes if lc.is_adjacent]
        elif self.bigraph:
            if arity_countdown > 0:
                candidates = [lc for lc in label_classes if (len(lc.G_nodes) > 0 and lc.is_adjacent and lc.is_port)]
            else:
                candidates = [lc for lc in label_classes if len(lc.G_nodes) > 0]
        else:
            candidates = label_classes
        if not candidates:
            return None
        return min(candidates, key=lambda lc: max(len(lc.G_nodes), len(lc.H_nodes)))

    def calculate_bound(self, label_classes):
        return sum(min(len(lc.G_nodes)+len(lc.transitive_G_nodes), len(lc.H_nodes)+len(lc.transitive_H_nodes)) for lc in label_classes if not lc.is_port)

    def search(self, label_classes, assignments, target, search_all, score=0, arity_countdown=0):
        if score == target and arity_countdown == 0:
            if search_all:
                self.all_instances_soln_set.append(assignments.copy())
                return None
            else:
                return assignments
        if score + self.calculate_bound(label_classes) < target:
            return None
        label_class = self.select_label_class(label_classes, len(assignments), arity_countdown)
        if label_class is None:
            return None 
        v = label_class.G_nodes.pop()
        H_nodes = label_class.H_nodes[:]
        
        new_score = None
        new_arity_countdown = None
        if label_class.is_port:
            new_arity_countdown = arity_countdown - 1
            new_score = score
        else:
            new_score = score + 1
            arity = self.G.nodes[v]['arity']
            if arity > 0:
                new_arity_countdown = arity
            else:
                new_arity_countdown = 0

        for w in H_nodes:
            label_class.H_nodes[:] = [u for u in H_nodes if u != w]
            assignments[v] = w
            new_label_classes = self.refine_label_classes(label_classes, v, w, assignments)
            search_result = self.search(new_label_classes, assignments, target, search_all, new_score, new_arity_countdown)
            if search_result is not None and not search_all:
                return search_result
            del assignments[v]
        label_class.H_nodes[:] = H_nodes
        new_label_classes = [lc for lc in label_classes if lc.G_nodes or lc.transitive_G_nodes]
        return self.search(new_label_classes, assignments, target, search_all, score, arity_countdown)
    
    # Finds maximal instead of maximum, i.e. all partial mappings which don't have a larger superset
    def search_LTS(self, label_classes, assignments, arity_countdown=0):
        label_class = self.select_label_class(label_classes, len(assignments), arity_countdown)
        if label_class is None:
            if arity_countdown == 0 and self.check_LTS_solution(assignments):
                self.all_instances_soln_set.append(assignments.copy())
                return True
            return False
        
        v = label_class.G_nodes.pop()
        H_nodes = label_class.H_nodes[:]
        
        new_arity_countdown = None
        if label_class.is_port:
            new_arity_countdown = arity_countdown - 1
        else:
            arity = self.G.nodes[v]['arity']
            if arity > 0:
                new_arity_countdown = arity
            else:
                new_arity_countdown = 0

        future_solution_exists = False
        for w in H_nodes:
            if type(v) == int and self.forbid_pairs_matrix[self.G.nodes[v]['index']][self.H.nodes[w]['index']] == 1:
                continue # site degree constraint
            label_class.H_nodes[:] = [u for u in H_nodes if u != w]
            assignments[v] = w
            new_label_classes = self.refine_label_classes(label_classes, v, w, assignments)
            future_solution_exists = self.search_LTS(new_label_classes, assignments, new_arity_countdown) or future_solution_exists
            del assignments[v]

        label_class.H_nodes[:] = H_nodes
        new_label_classes = [lc for lc in label_classes if lc.G_nodes or lc.transitive_G_nodes]
        future_solution_exists = self.search_LTS(new_label_classes, assignments, arity_countdown) or future_solution_exists

        if not future_solution_exists:
            if arity_countdown == 0 and self.check_LTS_solution(assignments):
                self.all_instances_soln_set.append(assignments.copy())
                return True
            return False
        return future_solution_exists
    
    def get_node_labels(self, G):
        return (self.node_label_fun(G.nodes[node]) for node in G.nodes())

    def find_common_subgraph(self, target, all_instances=False):
        """Find a common subgraph with at least `target` nodes using a variant
        of McSplit
        """
        G_labels = set(self.get_node_labels(self.G))
        H_labels = set(self.get_node_labels(self.H))
        label_classes = {label: LabelClass(False, False) for label in G_labels & H_labels}
        for v in self.G.nodes():
            label = self.node_label_fun(self.G.nodes[v])
            if label in label_classes:
                if(label == "*PORT*" or "*CLOSURE" in label):
                    if(label == "*PORT*"):
                        label_classes[label].is_port = True
                    label_classes[label].transitive_G_nodes.append(v)
                elif self.LTS and len([c for c in self.G.succ[v] if type(c) == int]) > 0:
                    label_classes[label].transitive_G_nodes.append(v)
                else:
                    label_classes[label].G_nodes.append(v)
        for v in self.H.nodes():
            label = self.node_label_fun(self.H.nodes[v])
            if label in label_classes:
                if(label == "*PORT*" or "*CLOSURE" in label):
                    if(label == "*PORT*"):
                        label_classes[label].is_port = True
                    label_classes[label].transitive_H_nodes.append(v)
                else:
                    label_classes[label].H_nodes.append(v)
        
        if(all_instances):
            self.all_instances_soln_set = []

            if(self.LTS):
                self.search_LTS(label_classes.values(), {})
            else:
                self.search(label_classes.values(), {}, target, True)
            solutions = self.all_instances_soln_set
            self.all_instances_soln_set = []

            if(1 == 0 and self.LTS):
                filtered = []
                for i, d in enumerate(solutions):
                    is_subset = False
                    for larger_dict in filtered:
                        if d.items() <= larger_dict.items(): 
                            is_subset = True
                            break
                    if not is_subset:
                        filtered.append(d)
                return filtered
            else:
                return solutions
        else:
            return self.search(label_classes.values(), {}, target, False)


def check_valid_graph_types(G, H):
    if G.is_multigraph() or H.is_multigraph():
        msg = "not implemented for multigraphs"
        raise nx.NetworkXNotImplemented(msg)
    if nx.number_of_selfloops(G) or nx.number_of_selfloops(H):
        msg = "not implemented for graphs with self-loops"
        raise nx.NetworkXNotImplemented(msg)


def check_valid_labels(G, H, node_label, edge_label):
    """Raise an exception if labels are invalid

    An exception is raised if any edge label is None or if accessing any label
    raises an exception.
    """
    for graph in G, H:
        for edge in graph.edges():
            if edge_label(graph.edges[edge]) is None:
                raise ValueError(f"Edge {edge} has label None")
        for node in graph.nodes():
            # Make sure that accessing the node does not raise an exception
            node_label(graph.nodes[node])


def common_induced_subgraph(
    G, H, target, connected=False, directed=False, node_label=None, edge_label=None, all_instances=False, bigraph=False, LTS=False
):
    """
    Find a common induced subgraph with at least a given number of nodes


    This is the decision version of the :func:`max_common_induced_subgraph`
    function.

    Optionally, nodes and/or edges can be labelled using the `node_label` and
    `edge_label` parameters.  If these are used, the algorithm will search for
    subgraphs of G and H that have identical labels.

    If the `connected` parameter is set to True, the function finds a maximum
    common connected induced subgraph.


    Parameters
    ----------
    G : NetworkX graph
        An undirected graph.
    H : NetworkX graph
        An undirected graph.
    target : int
        The found subgraph must have at least `target` nodes
    node_label : None, string or function, optional (default=None)
        If this is None, nodes are unlabelled.

        If this is a string, then node labels will be accessed via the node
        attribute with this key (that is, the label of node `v` will be
        `G.nodes[v][node_label]`).

        If this is a function, the label of a node is the value returned by
        the function. The function must accept exactly one positional
        argument: the dictionary of node attributes for that node. The
        label returned by the function must be hashable.

    edge_label : None, string or function, optional (default=None)
        If this is None, edges are unlabelled.

        If this is a string, then edge labels will be accessed via the edge
        attribute with this key (that is, the label of the edge joining `u`
        to `v` will be `G.edges[u, v][edge_label]`).

        If this is a function, the label of an edge is the value returned by
        the function. The function must accept exactly one positional
        argument: the dictionary of edge attributes for that edge. The
        label returned by the function must be hashable and must not be None.

    connected : boolean, optional (default=False)
        If this is True, the algorithm will search for a maximum common
        *connected* induced subgraph.

    all_instances : boolean, optional (default=False)
        If this is True, the algorithm will search for all maximum common
        induced subgraphs.

    Returns
    -------
    map : dict or list [map : dict] or None
        A dictionary whose keys are a subset of the node set of G, and whose
        values are a subset of the node set of H.  The subgraph of G induced by
        the keys is a maximum common subgraph of G and H.  This is isomorphic
        to the subgraph of H induced by the dictionary's values.  The mapping
        given by the dictionary is an isomorphism from the first of these
        subgraphs to the second.

        If searching for all solution instances, returns a list of these
        dictionary instances instead.

        If no common subgraph with at least `target` nodes is found, None is
        returned.


    Raises
    ------
    NetworkXNotImplemented
        If G or H is directed or a multigraph

    NetworkXNotImplemented
        If G or H has self-loops


    Notes
    -----
    The algorithm used is a simplified variant of McSplit. [1]_  The McSplit
    algorithm builds up a partial map from the node set of G to the node
    set of H, and keeps track of possible additional node-node assignments
    using a partitioning procedure.  For simplicity, the NetworkX version
    creates new lists when partitioning, rather than modifying lists
    in-place as in the original McSplit implementation.

    The implementation currently does not support directed graphs, multigraphs,
    or graphs with self-loops.


    See also
    --------
    max_common_induced_subgraph()


    References
    ----------
    .. [1] McCreesh, C., Prosser, P., & Trimble, J. (2017). A partitioning
       algorithm for maximum common subgraph problems. In Proceedings of the 26th
       International Joint Conference on Artificial Intelligence (pp. 712-719).
       https://www.ijcai.org/Proceedings/2017/0099.pdf
    """
    check_valid_graph_types(G, H)
    node_label = _label_function(node_label)
    edge_label = _label_function(edge_label)
    check_valid_labels(G, H, node_label, edge_label)
    return PartitioningMCISFinder(
        G, H, connected, directed, bigraph, LTS, node_label, edge_label
    ).find_common_subgraph(target, all_instances)


def max_common_induced_subgraph(
    G, H, node_label=None, edge_label=None, connected=False, directed=False, bigraph=False, all_instances=False, LTS=False
):
    """
    Find a maximum common induced subgraph


    Optionally, nodes and/or edges can be labelled using the `node_label` and
    `edge_label` parameters.  If these are used, the algorithm will search for
    isomorphic subgraphs of G and H that have identical labels.

    If the `connected` parameter is set to True, the function finds a maximum
    common connected induced subgraph.


    Parameters
    ----------
    G : NetworkX graph
        An undirected graph.
    H : NetworkX graph
        An undirected graph.
    node_label : None, string or function, optional (default=None)
        If this is None, nodes are unlabelled.

        If this is a string, then node labels will be accessed via the node
        attribute with this key (that is, the label of node `v` will be
        `G.nodes[v][node_label]`).

        If this is a function, the label of a node is the value returned by
        the function. The function must accept exactly one positional
        argument: the dictionary of node attributes for that node. The
        label returned by the function must be hashable.

    edge_label : None, string or function, optional (default=None)
        If this is None, edges are unlabelled.

        If this is a string, then edge labels will be accessed via the edge
        attribute with this key (that is, the label of the edge joining `u`
        to `v` will be `G.edges[u, v][edge_label]`).

        If this is a function, the label of an edge is the value returned by
        the function. The function must accept exactly one positional
        argument: the dictionary of edge attributes for that edge. The
        label returned by the function must be hashable and must not be None.

    connected : boolean, optional (default=False)
        If this is True, the algorithm will search for a maximum common
        *connected* induced subgraph.

    all_instances : boolean, optional (default=False)
        If this is True, the algorithm will search for all maximum common
        induced subgraphs.


    Returns
    -------
    map : dict or list [map : dict] or None
        A dictionary whose keys are a subset of the node set of G, and whose
        values are a subset of the node set of H.  The subgraph of G induced by
        the keys is a maximum common subgraph of G and H.  This is isomorphic
        to the subgraph of H induced by the dictionary's values.  The mapping
        given by the dictionary is an isomorphism from the first of these
        subgraphs to the second.

        If searching for all solution instances, returns a list of these
        dictionary instances instead.


    Raises
    ------
    NetworkXNotImplemented
        If G or H is directed or a multigraph

    NetworkXNotImplemented
        If G or H has self-loops


    Notes
    -----
    The algorithm used is a simplified variant of McSplit. [1]_  The McSplit
    algorithm builds up a partial map from the node set of G to the node
    set of H, and keeps track of possible additional node-node assignments
    using a partitioning procedure.  For simplicity, the NetworkX version
    creates new lists when partitioning, rather than modifying lists
    in-place as in the original McSplit implementation.

    The implementation currently does not support directed graphs, multigraphs,
    or graphs with self-loops.


    See also
    --------
    weak_modular_product_mcis()
    ismags_mcis()
    common_induced_subgraph()


    References
    ----------
    .. [1] McCreesh, C., Prosser, P., & Trimble, J. (2017). A partitioning
       algorithm for maximum common subgraph problems. In Proceedings of the 26th
       International Joint Conference on Artificial Intelligence (pp. 712-719).
       https://www.ijcai.org/Proceedings/2017/0099.pdf
    """
    check_valid_graph_types(G, H)
    min_n = None
    if bigraph:
        min_n = min(len([g for g in G.nodes if G.nodes[g]['label'] != "*PORT*"]), len([h for h in H.nodes if H.nodes[h]['label'] != "*PORT*"]))
    else:
        min_n = min(G.number_of_nodes(), H.number_of_nodes())
    for target in range(min_n, -1, -1):
        search_result = common_induced_subgraph(
            G, H, target, connected, directed, node_label, edge_label, all_instances, bigraph, LTS
        )
        if not all_instances and search_result is not None:
            return search_result
        if all_instances and len(search_result) > 0:
            return search_result


def weak_modular_product_graph(G, H, node_label=None, edge_label=None):
    check_valid_graph_types(G, H)
    node_label = _label_function(node_label)
    edge_label = _label_function(edge_label)
    check_valid_labels(G, H, node_label, edge_label)
    mp_graph = nx.Graph()
    for v in G.nodes():
        for w in H.nodes():
            if node_label(G.nodes[v]) == node_label(H.nodes[w]):
                mp_graph.add_node((v, w))
    for (v, w), (v_, w_) in itertools.combinations(mp_graph.nodes(), 2):
        if v != v_ and w != w_:
            G_label = get_edge_label(G, edge_label, v, v_, False)
            H_label = get_edge_label(H, edge_label, w, w_, False)
            if G_label == H_label:
                mp_graph.add_edge((v, w), (v_, w_))
    return mp_graph


def weak_modular_product_mcis(G, H, node_label=None, edge_label=None):
    """
    Find a maximum common induced subgraph using a maximum clique algorithm


    Optionally, nodes and/or edges can be labelled using the `node_label` and
    `edge_label` parameters.  If these are used, the algorithm will search for
    subgraphs of G and H that have identical labels.

    The current implementation does not support finding a maximum common
    *connected* induced subgraph.


    Parameters
    ----------
    G : NetworkX graph
        An undirected graph.
    H : NetworkX graph
        An undirected graph.
    node_label : None, string or function, optional (default=None)
        If this is None, nodes are unlabelled.

        If this is a string, then node labels will be accessed via the node
        attribute with this key (that is, the label of node `v` will be
        `G.nodes[v][node_label]`).

        If this is a function, the label of a node is the value returned by
        the function. The function must accept exactly one positional
        argument: the dictionary of node attributes for that node. The
        label returned by the function must be hashable.

    edge_label : None, string or function, optional (default=None)
        If this is None, edges are unlabelled.

        If this is a string, then edge labels will be accessed via the edge
        attribute with this key (that is, the label of the edge joining `u`
        to `v` will be `G.edges[u, v][edge_label]`).

        If this is a function, the label of an edge is the value returned by
        the function. The function must accept exactly one positional
        argument: the dictionary of edge attributes for that edge. The
        label returned by the function must be hashable and must not be None.


    Returns
    -------
    map : dict
        A dictionary whose keys are a subset of the node set of G, and whose
        values are a subset of the node set of H.  The subgraph of G induced by
        the keys is a maximum common subgraph of G and H.  This is isomorphic
        to the subgraph of H induced by the dictionary's values.  The mapping
        given by the dictionary is an isomorphism from the first of these
        subgraphs to the second.


    Raises
    ------
    NetworkXNotImplemented
        If G or H is directed or a multigraph

    NetworkXNotImplemented
        If G or H has self-loops


    Notes
    -----
    The algorithm creates the weak modular product graph, and uses a maximum
    clique algorithm on this to find a maximum common induced subgraph.  This
    approach was first applied to the *maximal* common subgraph problem by
    Levi. [1]_  McCreesh et al. [2]_ conduct extensive experiments using a modern
    maximum clique solver to solve the *maximum* common subgraph problem; they
    find that this approach is very effective for labelled graphs.

    The implementation currently does not support directed graphs, multigraphs,
    or graphs with self-loops.


    See also
    --------
    max_common_induced_subgraph()
    ismags_mcis()
    common_induced_subgraph()


    References
    ----------
    .. [1] Levi, G. (1973), "A note on the derivation of maximal common subgraphs
       of two directed or undirected graphs", Calcolo, 9 (4): 341–352,
       doi:10.1007/BF02575586.
    .. [2] McCreesh C., Ndiaye S.N., Prosser P., Solnon C. (2016) Clique and
       Constraint Models for Maximum Common (Connected) Subgraph Problems. In:
       Rueher M. (eds) Principles and Practice of Constraint Programming. CP
       2016.  Lecture Notes in Computer Science, vol 9892. Springer, Cham.
       https://doi.org/10.1007/978-3-319-44953-1_23
    """
    mp_graph = weak_modular_product_graph(G, H, node_label, edge_label)
    return dict(nx.max_weight_clique(mp_graph, None)[0])


def ismags_mcis(G, H, node_label=None, edge_label=None):
    """
    Find a maximum common induced subgraph using the ISMAGS algorithm


    Optionally, nodes and/or edges can be labelled using the `node_label` and
    `edge_label` parameters.  If these are used, the algorithm will search for
    subgraphs of G and H that have identical labels.

    This is a small wrapper for convenience around
    :func:`networkx.algorithms.isomorphism.ISMAGS.largest_common_subgraph`.

    This function does not support finding a maximum common *connected* induced
    subgraph.


    Parameters
    ----------
    G : NetworkX graph
        An undirected graph.
    H : NetworkX graph
        An undirected graph.
    node_label : None, string or function, optional (default=None)
        If this is None, nodes are unlabelled.

        If this is a string, then node labels will be accessed via the node
        attribute with this key (that is, the label of node `v` will be
        `G.nodes[v][node_label]`).

        If this is a function, the label of a node is the value returned by
        the function. The function must accept exactly one positional
        argument: the dictionary of node attributes for that node. The
        label returned by the function must be hashable.

    edge_label : None, string or function, optional (default=None)
        If this is None, edges are unlabelled.

        If this is a string, then edge labels will be accessed via the edge
        attribute with this key (that is, the label of the edge joining `u`
        to `v` will be `G.edges[u, v][edge_label]`).

        If this is a function, the label of an edge is the value returned by
        the function. The function must accept exactly one positional
        argument: the dictionary of edge attributes for that edge. The
        label returned by the function must be hashable and must not be None.


    Returns
    -------
    map : dict
        A dictionary whose keys are a subset of the node set of G, and whose
        values are a subset of the node set of H.  The subgraph of G induced by
        the keys is a maximum common subgraph of G and H.  This is isomorphic
        to the subgraph of H induced by the dictionary's values.  The mapping
        given by the dictionary is an isomorphism from the first of these
        subgraphs to the second.


    Raises
    ------
    NetworkXNotImplemented
        If G or H is directed or a multigraph

    NetworkXNotImplemented
        If G or H has self-loops


    See also
    --------
    networkx.algorithms.isomorphism.ISMAGS.largest_common_subgraph()
    max_common_induced_subgraph()
    weak_modular_product_mcis()
    common_induced_subgraph()
    """
    check_valid_graph_types(G, H)
    node_label_fun = _label_function(node_label)
    edge_label_fun = _label_function(edge_label)
    check_valid_labels(G, H, node_label_fun, edge_label_fun)

    if node_label is None:
        node_match = None
    else:
        node_match = lambda node1_attrs, node2_attrs: node_label_fun(
            node1_attrs
        ) == node_label_fun(node2_attrs)

    if edge_label is None:
        edge_match = None
    else:
        edge_match = lambda edge1_attrs, edge2_attrs: edge_label_fun(
            edge1_attrs
        ) == edge_label_fun(edge2_attrs)

    try:
        return next(
            nx.isomorphism.ISMAGS(
                G, H, node_match=node_match, edge_match=edge_match
            ).largest_common_subgraph(False)
        )
    except StopIteration:
        return {}

# For bigraphs only!
def build_transitive_matrix(G):
    G_place_nodes = [g for g in G.nodes if type(g) == int]
    matrix = [[0 for x in range(len(G_place_nodes))] for y in range(len(G_place_nodes))]
    for g in G_place_nodes:
        matrix[G.nodes[g]['index']][G.nodes[g]['index']] = 1
    check_nodes = [n for n in G_place_nodes if G.out_degree(n) == 0]
    while len(check_nodes) > 0:
        c = check_nodes.pop()
        for g in G.nodes:
            if(G.has_edge(g, c)):
                matrix[G.nodes[g]['index']] = [matrix[G.nodes[g]['index']][i] | matrix[G.nodes[c]['index']][i] for i in range(len(matrix))]
                check_nodes = [g] + check_nodes
    return matrix

# For bigraphs (with LTS) only! (degree constraints)
def build_forbidden_pairs_matrix(G, H):
    G_place_nodes = [g for g in G.nodes if type(g) == int]
    H_place_nodes = [h for h in H.nodes if type(h) == int]
    matrix = [[0 for x in range(len(H_place_nodes))] for y in range(len(G_place_nodes))]

    for g in G_place_nodes:
        for h in H_place_nodes:
            if G.nodes[g]['site_adj'] == False and len(G.succ[g]) != len(H.succ[h]):
                matrix[G.nodes[g]['index']][H.nodes[h]['index']] = 1      
    return matrix