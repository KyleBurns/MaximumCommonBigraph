import mcb

test_sets = ["conference_no_sharing"]

for ts in test_sets:
    tests = []
    with open("instances/" + ts + "_instances.txt", 'r') as f:
        tests = f.readlines()
    for t in tests:
        t = t.strip('\n').split(' ')
        print(t)
        G = mcb.read_bigraph("instances/" + t[1])
        H = mcb.read_bigraph("instances/" + t[2])

        print("Begin search 1: " + t[0])
        result1 = mcb.max_common_bigraph(G, H, True, False, False)
        print("Begin search 2: " + t[0])
        result2 = mcb.max_common_bigraph(H, G, True, False, False)
        print("Done searching")

        if(result1['max'] != result2['max']):
            print("ERROR: " + t[0] + ", different maximums")
            quit()

        if(len(result1['solutions']) != len(result2['solutions'])):
            print("ERROR: " + t[0] + ", different no. solutions")
            quit()

        for s in result1['solutions']:
            found_match = False
            inverted_entity_map = {v : k for k, v in s['entity_mapping'].items()}
            inverted_link_map = {v : k for k, v in s['link_mapping'].items()}
            inverted_solution = {'entity_mapping': inverted_entity_map, 'link_mapping': inverted_link_map}
            for s2 in result2['solutions']:
                if s2 == inverted_solution:
                    found_match = True
                    break
            if not found_match:
                print("ERROR: " + t[0] + ", different solution set")
                quit()
        print(True)