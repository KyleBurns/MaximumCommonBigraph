import mcb
import os

count = 0
with os.scandir('results') as it:
    for entry in it:
        with open('results/' + entry.name) as f:
            solution_set = []
            count += 1
            print(entry.name, str(count))
            mapping = f.readline().split("mapping = {")
            if len(mapping) > 1:
                mapping = mapping[1:-1]
                for x in mapping[1:]:
                    solution = {'entity_mapping': {}, 'link_mapping': {}}
                    link_map = x.split('} -- {')[1][:-2].replace(')', '').replace('(', '').replace(' ', '').split(',')
                    entity_map = x.split('} -- {')[0].replace(')', '').replace('(', '').replace(' ', '').split(',')
                    if len(entity_map) > 1:
                        for e in range(0, len(entity_map), 2):
                            solution['entity_mapping'][int(entity_map[e])] = int(entity_map[e+1])
                    if len(link_map) > 1:
                        for e in range(0, len(link_map), 2):
                            solution['link_mapping'][int(link_map[e])] = int(link_map[e+1])
                    solution_set.append(solution)
            
            split = entry.name.split('_')
            G = mcb.read_bigraph("instances/conference_no_sharing/" + split[0] + '_' + split[1])
            H = mcb.read_bigraph("instances/conference_no_sharing/" + split[2] + '_' + split[3][:-4])
            result = mcb.max_common_bigraph(G, H, True, False, True)
            mcb_sols = result['solutions']
            for s in solution_set:
                if s not in mcb_sols:
                    print("ERROR: solution not found:\n" + str(s))
                    quit()