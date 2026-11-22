"""Finite matching, palette, and universal-core checks from the research note."""
from itertools import combinations, product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from witness import role_edge


def four_matchings(edges):
    colors = [set() for _ in range(4)]
    endpoints = [set() for _ in colors]

    def assign(i):
        if i == len(edges):
            return True
        edge = edges[i]
        for matching, used in zip(colors, endpoints):
            if used.isdisjoint(edge):
                matching.add(edge)
                used.update(edge)
                if assign(i + 1):
                    return True
                used.difference_update(edge)
                matching.remove(edge)
        return False

    if not assign(0):
        raise ValueError("Could not factor the bipartite layer")
    return colors


m = 7
outside = [(1,2),(3,),(4,),(5,),(6,)]
half = pow(2,-1,m)


def check_grouping(four):
    assigned = set()
    hosts = pairs_tested = perfect_without_safe_role = 0
    for a,b in combinations(range(3),2):
        edges = [(i,k) for i,k in product(range(5*a,5*a+5),range(5*b,5*b+5)) if role_edge(i,k)]
        assert len(edges) == 18
        if four:
            groups = four_matchings(edges)
        else:
            groups = [[(i,k) for i,k in edges if (k-i)%5 == d] for d in range(5)]
        for group in groups:
            roles = set(v for edge in group for v in edge)
            assert len(roles) == 2*len(group)
            if len(group) == 5 and all(any(role_edge(r,v) for v in roles) for r in range(15)):
                perfect_without_safe_role += 1
            for U in outside:
                for c in range(m):
                    hosts += 1
                    palette = set()
                    for i,k in sorted(group):
                        for u in U:
                            x = (i,(c-(b-a)*half*u)%m)
                            y = (k,(c+(b-a)*half*u)%m)
                            assert x not in palette and y not in palette
                            assert (x,y) not in assigned
                            palette.update((x,y))
                            assigned.add((x,y))
                    for (i,x),(k,y) in combinations(sorted(palette),2):
                        # Direction zero is exactly equality of positions.
                        assert not (role_edge(i,k) and x == y)
                        pairs_tested += 1
    expected = {((i,x),(k,y)) for i,k in combinations(range(15),2) if role_edge(i,k)
                for x,y in product(range(m),repeat=2) if x != y}
    assert assigned == expected
    return dict(hosts=hosts, exterior_pairs=len(assigned), palette_pairs_tested=pairs_tested,
                perfect_groups_without_a_safe_role=perfect_without_safe_role)


def check_universal(x,d):
    assert x >= d
    new = range(x)
    expected = set(combinations(new,2))
    expected.update(product(new,range(x,x+3*d)))
    fibers = {}
    def put(key,u,v):
        assert (u,v) in expected
        expected.remove((u,v))
        used = fibers.setdefault(key,set())
        assert used.isdisjoint((u,v))
        used.update((u,v))
    for u,v in combinations(new,2):
        put((0,(u+v)%(x+d)),u,v)
    for i in range(3):
        for u,r in product(new,range(d)):
            modulus = x+d if i == 0 else x
            code = x+r if i == 0 else r
            put((i,(u+code)%modulus),u,x+i*d+r)
    assert not expected
    assert len(fibers) <= 3*x+d
    return dict(universal_vertices=x, old_vertices_per_part=d, used_matchings=len(fibers),
                new_pairs=x*(x-1)//2+3*x*d)


print(json.dumps(dict(five=check_grouping(False),four=check_grouping(True),
                      universal=[check_universal(35,35),check_universal(40,35)]),indent=2))
