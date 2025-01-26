# MaximumCommonBigraph
An implementation of a Maximum Common Bigraph algorithm through adapting McSplit for MCIS

Based on James Trimble's Python implementation of McSplit for NetworkX:
https://github.com/networkx/networkx/pull/4221/files

### Usage:

python3 mcb.py <pattern> <target> 

Optional additional parameters:

all: return all solutions rather than just the first found solution

rpo: build the relative pushout of the (G1, G2, GM) bound for each solution

lts: find all partial matches where the addition of a minimal context would permit a full match - used to build minimal contextual labelled transition systems (G1 -> pattern, G2 -> target)
