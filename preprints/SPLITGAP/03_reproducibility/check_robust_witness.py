"""Reconstruct the j=1, m=3 witness from its edge list and check the host certificate."""
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, product
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parent
ORDER = 4620
M = 3
T = M*M
CORE = 15*T
points = list(product(range(M), repeat=2))
deleted = [(2,2,2),(1,2,1),(3,1,4),(0,3,1),(0,4,0),(2,3,0),(4,0,3)]


def adjacent_roles(i,k):
    a,r = divmod(i,5)
    b,s = divmod(k,5)
    return a != b and not any(q[a] == r and q[b] == s for q in deleted)


def in_support(u):
    x,y = (Fraction(z,M) for z in u)
    eps = Fraction(7,1080)
    return (x >= Fraction(1,2) and Fraction(2,3) < x+y <= Fraction(7,6) or
            Fraction(7,6)+eps <= x+y <= Fraction(17,12) and
            (x >= Fraction(1,2) > y or x < Fraction(1,2) <= y and 2*x+y >= Fraction(3,2)+eps))


with TemporaryDirectory() as tmp:
    edge_file = Path(tmp) / "example.edges"
    result = subprocess.check_output([sys.executable,str(ROOT/"witness.py"),"--dimension","1",
        "--modulus","3","--order",str(ORDER),"--edges",str(edge_file)], text=True)
    data = json.loads(result)
    host_neighbors = [set() for _ in range(ORDER-CORE)]
    seen = set()
    for line in edge_file.read_text(encoding="ascii").splitlines():
        v,h = map(int,line.split())
        assert 0 <= v < h < ORDER and v < CORE and (v,h) not in seen
        seen.add((v,h))
        if h >= CORE:
            host_neighbors[h-CORE].add(v)
    assert all(pair in seen for pair in combinations(range(CORE),2))
    assert len(seen) == data["edges"]
    digest = sha256(edge_file.read_bytes()).hexdigest()

support = [u for u in points if in_support(u)]
assert len(support) == 1
outside = [u for u in points if u not in support]
# The eight exterior points lie in distinct sign/parity classes in this example.
# Check the emitted incidence sets against their complete mathematical description.
first = {}
idx = 0
for i,k in combinations_with_replacement(range(15),2):
    safe = next(s for s in range(15) if not adjacent_roles(s,i) and not adjacent_roles(s,k))
    full = {safe*T+p for p in range(T)}
    terms = outside if adjacent_roles(i,k) else [None]
    for u in terms:
        for c in points:
            first[i,k,u,c] = idx
            expected = set(full)
            if u is None:
                expected.update(r*T+p for r in (i,k) for p in range(T))
            else:
                step = (k//5-i//5)*pow(2,-1,M)
                for r,sign in ((i,-1),(k,1)):
                    p = tuple((a+sign*step*b)%M for a,b in zip(c,u))
                    expected.add(r*T+points.index(p))
            assert expected == host_neighbors[idx]
            idx += 1
assert len(host_neighbors)-idx == 3
assert all(h == set(range(T)) for h in host_neighbors[idx:])
used = [set() for _ in host_neighbors]
residual = set()
for a,b in combinations(range(CORE),2):
    i,p = divmod(a,T)
    k,q = divmod(b,T)
    p,q = points[p], points[q]
    c = tuple(((x+y)*pow(2,-1,M))%M for x,y in zip(p,q))
    u = None
    if adjacent_roles(i,k):
        inv = pow(k//5-i//5,-1,M)
        u = tuple(((y-x)*inv)%M for x,y in zip(p,q))
        if u in support:
            residual.add((a,b))
            continue
    h = first[i,k,u,c]
    assert {a,b} <= host_neighbors[h] and used[h].isdisjoint((a,b))
    used[h].update((a,b))
for palette in host_neighbors:
    assert all(pair not in residual for pair in combinations(sorted(palette),2))
assert len(residual) == 54*T
assert min(map(len,host_neighbors)) == T
# The certified support has one direction. A constant potential has zero
# range and the nonconstant midpoint condition is vacuous, so Lemma 4.1
# yields 2*tau/9 on this graph.
tau = T*len(support)
data.update(residual_blocks=tau, gap_lower_bound=str(Fraction(2*tau,9)), residual_edges=len(residual), assigned_pairs=CORE*(CORE-1)//2-len(residual),
            verified_vertex_connectivity=T, edge_list_sha256=digest)
expected = json.loads((ROOT/"robust-example.json").read_text(encoding="utf-8"))
if data != expected:
    raise ValueError("The example differs from its recorded certificate")
print(json.dumps(data,indent=2))
