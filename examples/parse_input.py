#!/usr/bin/env python3.8

import re

pat = re.compile(r" [A-Z] ")


if __name__ == '__main__':
    unique_nodes = set()
    left = set()
    right = set()
    edges = []

    with open('./advent_of_code_2018_day_7_input.txt') as f:
        for l in f:
            (src, dst) = [x.strip() for x in pat.findall(l)]
            unique_nodes.add(src)
            unique_nodes.add(dst)
            edges.append((src, dst))
            left.add(src)
            right.add(dst)

    for i, n in enumerate(sorted(unique_nodes)):
        print('let {0} = g.add_node({1}, Some("{2}"));'.format(
            n.lower(),
            i,
            n))

    for edge in edges:
        print('g.add_edge({0}, {1}, None);'.format(
            edge[0].lower(),
            edge[1].lower()))

    print('starting edges (no dependencies): {0}'.format([e for e in left if e not in right]))
