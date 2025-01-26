import networkx as nx
import sys
import mcis
import time
from copy import deepcopy

class Bigraph:

    def __init__(self, place_graph, link_graph):
        self.place_graph = place_graph
        self.link_graph = link_graph

    def to_string(self):
        num_regions = 0
        num_nodes = 0
        num_sites = 0
        big_string = "{"
        for g in self.place_graph.nodes:
            if self.place_graph.nodes[g]['label'] == "*ROOT*":
                num_regions += 1
            elif self.place_graph.nodes[g]['label'] == "*SITE*":
                num_sites += 1
            else:
                num_nodes += 1
                big_string += '(' + str(self.place_graph.nodes[g]['index']) + ', ' + self.place_graph.nodes[g]['label'] + ':' + str(self.place_graph.nodes[g]['arity']) + '),' 
        big_string = big_string[:-1] + '}\n' + str(num_regions) + ' ' + str(num_nodes) + ' ' + str(num_sites) + '\n'

        node_ord = [r for r in self.place_graph.nodes() if self.place_graph.nodes[r]['label'] == "*ROOT*"]
        node_ord += [r for r in self.place_graph.nodes() if self.place_graph.nodes[r]['label'] not in ["*ROOT*", "*SITE*"]]
        node_ord += [r for r in self.place_graph.nodes() if self.place_graph.nodes[r]['label'] == "*SITE*"]
        for x in range(num_regions+num_nodes):
            for y in range(num_regions, num_regions+num_nodes+num_sites):
                if(self.place_graph.has_edge(node_ord[x], node_ord[y])):
                    big_string += '1'
                else:
                    big_string += '0'
            big_string += '\n'

        hyperedges = set([e for l in self.link_graph for e in l])
        for e in hyperedges:
            big_string += '({}, {'
            if type(e) == str:
                big_string += e
            big_string += '}, {'
            for l in range(len(self.link_graph)):
                count = 0
                for p in range(len(self.link_graph[l])):
                    if self.link_graph[l][p] == e:
                        count += 1
                if count > 0:
                    big_string += '(' + str(l) + ', ' + str(count) + '), '
            big_string = big_string[:-2] + '})\n'
        return big_string[:-1]
    

def read_bigraph(file):
    with open(file, "r") as f:
        big_string = f.readlines()
    place_graph = nx.DiGraph()
    link_graph = []
    st = big_string[0].split("(")[1:]
    num_regions = int(big_string[1].split(" ")[0])
    num_nodes = int(big_string[1].split(" ")[1])
    num_sites = int(big_string[1].split(" ")[2])
    for n in range(num_regions):
        place_graph.add_node(n, index=n, label="*ROOT*", arity=-1)
    for n in range(num_nodes):
        substr = st[n].split(" ")[1]
        arity = int(substr[substr.index(':')+1:substr.index(')')])
        place_graph.add_node(num_regions + n, index=n, label=substr[:substr.index(':')], arity=arity)
        link_graph.append([])
    for n in range(num_sites):
        place_graph.add_node(num_regions + num_nodes + n, index=n, label="*SITE*", arity=-1)
    for x in range(2, num_regions+num_nodes+2):
        for y in range(num_nodes+num_sites):
            if big_string[x][y] == "1":
                place_graph.add_edge(x-2, num_regions+y)

    big_string = big_string[2+num_regions+num_nodes:]
    edge_count = 0
    for l in big_string:
        link_info = ''.join(a for a in l.strip('\n').split('{')[3][:-2] if a in ",0123456789").split(',')
        name = l.split('{')[2][:l.split('{')[2].find('}')]
        if name == '':
            name = edge_count
            edge_count += 1
        for n in range(0, len(link_info), 2):
            for x in range(int(link_info[n+1])):
                link_graph[int(link_info[n])].append(name)
    return Bigraph(place_graph, link_graph)


def place_RPO(G, H, mapping, LTS=False):

    RPO = deepcopy(G)
    RPO.remove_nodes_from([r for r in RPO.nodes if (RPO.nodes[r]['label'] in ["*SITE*", "*ROOT*"]) or r not in mapping.keys()])
    if(len(RPO.nodes)) == 0:
        return RPO
    
    regions_for_adding = []
    sites_for_adding = []
    for r in RPO.nodes:
        if len(RPO.pred[r]) == 0 and (len(H.pred[mapping[r]]) > 0 or len(G.pred[r]) > 0):
            regions_for_adding.append([r])
        if not LTS:
            if len(G.succ[r]) > len(RPO.succ[r]) or len(H.succ[mapping[r]]) > len(RPO.succ[r]):
                sites_for_adding.append(r)

    i = 0
    j = 1
    while(i < len(regions_for_adding)-1):
        i_g_parents = [*G.pred[regions_for_adding[i][0]]]
        j_g_parents = [*G.pred[regions_for_adding[j][0]]]
        i_h_parents = [*H.pred[mapping[regions_for_adding[i][0]]]]
        j_h_parents = [*H.pred[mapping[regions_for_adding[j][0]]]]
        if len(i_g_parents) > 0 and len(j_g_parents) > 0 and len(i_h_parents) > 0 and len(j_h_parents) > 0: 
            if(i_g_parents[0] == j_g_parents[0] and i_h_parents[0] == j_h_parents[0]):
                regions_for_adding[i] = regions_for_adding[i] + regions_for_adding[j]
                del regions_for_adding[j]
                j -= 1
        if(j+1 == len(regions_for_adding)):
            i += 1
            j = i+1
        else:
            j += 1

    index = max(RPO.nodes)+1
    i = 0
    for r in regions_for_adding:
        RPO.add_node(index+i, index=i, label="*ROOT*", arity=-1)
        for e in r:
            RPO.add_edge(index+i, e)
        i += 1

    if not LTS:
        i = 0
        for s in sites_for_adding:
            RPO.add_node(index+len(regions_for_adding)+i, index=i, label="*SITE*", arity=-1)
            RPO.add_edge(s, index+len(regions_for_adding)+i)
            i += 1
    return RPO


def link_RPO(G, H, mapping):
    RPO = deepcopy(G)
    assigned = []
    assignments = [m.split('-') for m in mapping if type(m) == str]
    for a in assignments:
        if a[0] == 'link' and int(a[1]) not in assigned:
            assigned.append(int(a[1]))
    for g in range(len(G)-1, -1, -1):
        if g not in assigned:
            RPO[g] = [None]
    
    index = 97
    for r in range(len(RPO)):
        for l in range(len(RPO[r])):
            if RPO[r][l] != None and (type(RPO[r][l]) == str or ['closure', str(RPO[r][l])] not in assignments):
                RPO[r][l] = chr(index)
                index += 1

    for ll in range(len(RPO)):
        for le in range(len(RPO[ll])):
            if type(RPO[ll][le]) == str:
                lstring = "link-" + str(ll) + '-' + str(le)
                lmatch = mapping[lstring].split('-')[1:]
                for rl in range(ll, len(RPO)):
                    for re in range(len(RPO[rl])):
                        if type(RPO[rl][re]) == str and (rl > ll or re > le):
                            rstring = "link-" + str(rl) + '-' + str(re)
                            rmatch = mapping[rstring].split('-')[1:]
                            if G[ll][le] == G[rl][re] and H[int(lmatch[0])][int(lmatch[1])] == H[int(rmatch[0])][int(rmatch[1])]:
                                RPO[rl][re] = RPO[ll][le]

    for l in range(len(RPO)-1, -1, -1):
        if RPO[l] == [None]:
            del RPO[l]

    return RPO


def max_common_bigraph(G, H, all_instances, RPO, LTS):  
    g_remove = [n for n in G.place_graph.nodes if (G.place_graph.nodes[n]['label'] == "*SITE*" or G.place_graph.nodes[n]['label'] == "*ROOT*")]
    g_free = G.place_graph.copy()
    g_free.remove_nodes_from(g_remove)

    h_remove = [n for n in H.place_graph.nodes if (H.place_graph.nodes[n]['label'] == "*SITE*" or H.place_graph.nodes[n]['label'] == "*ROOT*")]
    h_free = H.place_graph.copy()
    h_free.remove_nodes_from(h_remove)

    if LTS:
        g_site_adjacents = [j for sub in [list(G.place_graph.pred[n]) for n in G.place_graph.nodes if (G.place_graph.nodes[n]['label']) == "*SITE*"] for j in sub]
        g_region_adjacents = [j for sub in [list(G.place_graph.succ[n]) for n in G.place_graph.nodes if (G.place_graph.nodes[n]['label']) == "*ROOT*"] for j in sub]

        h_site_adjacents = [j for sub in [list(H.place_graph.pred[n]) for n in H.place_graph.nodes if (H.place_graph.nodes[n]['label']) == "*SITE*"] for j in sub]
        h_region_adjacents = [j for sub in [list(H.place_graph.succ[n]) for n in H.place_graph.nodes if (H.place_graph.nodes[n]['label']) == "*ROOT*"] for j in sub]

        for g in g_free:
            if g in g_region_adjacents:
                g_free.nodes[g]['root_adj'] = list(G.place_graph.pred[g])[0]
            else:
                g_free.nodes[g]['root_adj'] = None
            if g in g_site_adjacents:
                g_free.nodes[g]['site_adj'] = True
            else:
                g_free.nodes[g]['site_adj'] = False
            
        for h in h_free:
            if h in h_region_adjacents:
                h_free.nodes[h]['root_adj'] = list(H.place_graph.pred[h])[0]
            else:
                h_free.nodes[h]['root_adj'] = None
            if h in h_site_adjacents:
                h_free.nodes[h]['site_adj'] = True
            else:
                h_free.nodes[h]['site_adj'] = False

    edges = {}
    for l in range(len(G.link_graph)):
        for p in range(len(G.link_graph[l])):
            g_free.add_node("link-" + str(l) + "-" + str(p), label="*PORT*", arity=-1, face=G.link_graph[l][p])
            g_free.add_edge(list(g_free.nodes)[l], "link-" + str(l) + "-" + str(p))
            if type(G.link_graph[l][p]) == int:
                if G.link_graph[l][p] not in edges.keys():
                    edges[G.link_graph[l][p]] = ["link-" + str(l) + "-" + str(p)]
                else:
                    edges[G.link_graph[l][p]].append("link-" + str(l) + "-" + str(p))
    for e in edges:
        g_free.add_node("closure-" + str(e), label="*CLOSURE" + str(len(edges[e])) + "*", arity=-1)
        for l in edges[e]:
            g_free.add_edge(l, "closure-" + str(e))

    edges = {}
    for l in range(len(H.link_graph)):
        for p in range(len(H.link_graph[l])):
            h_free.add_node("link-" + str(l) + "-" + str(p), label="*PORT*", arity=-1, face=H.link_graph[l][p])
            h_free.add_edge(list(h_free.nodes)[l], "link-" + str(l) + "-" + str(p))
            if type(H.link_graph[l][p]) == int:
                if H.link_graph[l][p] not in edges.keys():
                    edges[H.link_graph[l][p]] = ["link-" + str(l) + "-" + str(p)]
                else:
                    edges[H.link_graph[l][p]].append("link-" + str(l) + "-" + str(p))
    for e in edges:
        h_free.add_node("closure-" + str(e), label="*CLOSURE" + str(len(edges[e])) + "*", arity=-1)
        for l in edges[e]:
            h_free.add_edge(l, "closure-" + str(e))


    print(h_free.size())
    return {'solutions': []}
    time_start = time.time()
    results = mcis.max_common_induced_subgraph(g_free, h_free, bigraph=True, all_instances=all_instances, node_label='label', LTS=LTS)
    if not all_instances:
        results = [results]
    time_end = time.time()
    search_time = time_end-time_start
    result_output = {'solutions': []}
    if len(results) > 0:
        result_output['max'] = len([i for i in results[0].keys() if type(i) == int or (type(i) == str and 'closure' in i)])
    else: 
        result_output['max'] = 0
    result_output['search_time'] = search_time

    for r in results:
        solution = {'entity_mapping': {}, 'link_mapping': {}}
        entity_assignments = [x for x in r.keys() if type(x) == int]
        for i in entity_assignments:
            solution['entity_mapping'][G.place_graph.nodes[i]['index']] = H.place_graph.nodes[r[i]]['index']
        edge_assignments = [x for x in r.keys() if type(x) == str and 'closure' in x]
        for i in edge_assignments:
            solution['link_mapping'][int(i[8:])] = int(r[i][8:])
        if RPO:
            time_start = time.time()
            solution['RPO'] = Bigraph(place_RPO(G.place_graph, H.place_graph, r), link_RPO(G.link_graph, H.link_graph, r))
            time_end = time.time()
            RPO_time = time_end-time_start
            result_output['RPO_time'] = RPO_time
        result_output['solutions'].append(solution)
    return result_output


if __name__ == "__main__":
    results = max_common_bigraph(read_bigraph(sys.argv[1]), read_bigraph(sys.argv[2]), (len(sys.argv) > 3 and "all" in sys.argv), (len(sys.argv) > 3 and "rpo" in sys.argv), (len(sys.argv) > 3 and "lts" in sys.argv))
    print("Solutions:", str(len(results['solutions'])))
    if((len(sys.argv) > 3 and "rpo" in sys.argv)):
        print("Total Time: ", str(round(results['search_time']*1000, 3) + round(results['RPO_time']*1000, 3)) + "ms")
    print("Search Time:", str(round(results['search_time']*1000, 3)) + "ms")
    if((len(sys.argv) > 3 and "rpo" in sys.argv)):
        print("RPO Time:", str(round(results['RPO_time']*1000, 3)) + "ms")
    if(len(results['solutions']) <= 30):
        for s in results['solutions']:
           print(s)