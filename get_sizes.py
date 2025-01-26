import mcb

test_sets = ["conference_no_sharing"]

for ts in test_sets:
    tests = []
    with open("instances/" + ts + '_instances.txt', 'r') as f:
        tests = f.readlines()
    for t in tests:
        if "2000" in t[2]:
            break
        t = t.strip('\n').split(' ')
        G = mcb.read_bigraph("instances/" + t[1])
        H = mcb.read_bigraph("instances/" + t[2])
        result = mcb.max_common_bigraph(G, H, True, True, False)
