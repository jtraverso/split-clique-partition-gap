"""Generate the split witness as a deterministic, zero-based edge list."""

import argparse
from itertools import combinations, combinations_with_replacement, product
import json
from pathlib import Path


DELETED = ((2, 2, 2), (1, 2, 1), (3, 1, 4), (0, 3, 1), (0, 4, 0), (2, 3, 0), (4, 0, 3))


def role_edge(i, k):
    a, r = divmod(i, 5)
    b, s = divmod(k, 5)
    return a != b and all((triple[a], triple[b]) != (r, s) for triple in DELETED)


def parameters(n):
    # Compare j^2 log(24/7) with log n using integers.
    j = 0
    while 24 ** ((j + 1) ** 2) <= n * 7 ** ((j + 1) ** 2):
        j += 1
    budget = n // (255 + 1049760 * j)
    if j == 0 or budget < 1:
        raise ValueError("Order below the range of the asymptotic parameter selection")
    lo, hi = 1, budget + 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** (2 * j) <= budget:
            lo = mid
        else:
            hi = mid
    return j, lo if lo % 2 else lo - 1


def grid_class(x, y, m, j):
    # Scale all boundary tests by a positive denominator; epsilon = 7/(1080j).
    d = 1080 * j
    z = x + y
    forms = (2*x-m, 2*y-m, 3*z-2*m, 6*z-7*m, d*(6*z-7*m)-42*m,
             12*z-17*m, d*(4*x+2*y-3*m)-14*m)
    a, b, low, high, shifted, top, slope = forms
    inside = (a >= 0 and low > 0 and high <= 0 or
              shifted >= 0 and top <= 0 and
              (a >= 0 and b < 0 or a < 0 and b >= 0 and slope >= 0))
    if inside:
        return None
    return tuple((v > 0) - (v < 0) for v in forms) + (x % 2, y % 2)


def witness(j, m, n=None):
    if j < 1 or m < 1 or m % 2 == 0:
        raise ValueError("A positive dimension and a positive odd modulus are required")
    t = m ** (2*j)
    if n is not None and 81*t > n:
        raise ValueError("The order is too small even for the fixed host types")
    points = list(product(range(m), repeat=2*j))
    index = {p: i for i, p in enumerate(points)}
    grid = {(x,y): grid_class(x,y,m,j) for x,y in product(range(m), repeat=2)}
    classes = {}
    for u in points:
        for r in range(j):
            key = grid[u[2*r], u[2*r+1]]
            if key is not None:
                classes.setdefault((r,key), []).append(u)
                break
    order = (81 + 54*len(classes))*t
    if n is None:
        n = order
    if n < order:
        raise ValueError(f"The installed hosts require {order} vertices")
    half = (m+1)//2

    def full(role):
        return range(role*t, (role+1)*t)

    def neighbors():
        for i,k in combinations_with_replacement(range(15),2):
            safe = next(s for s in range(15) if not role_edge(s,i) and not role_edge(s,k))
            if not role_edge(i,k):
                palette = sorted(set(full(i)).union(full(k),full(safe)))
                for _ in points:
                    yield palette
                continue
            step = (k//5 - i//5)*half
            for group in classes.values():
                for center in points:
                    palette = set(full(safe))
                    for u in group:
                        for role, sign in ((i,-1),(k,1)):
                            p = tuple((a + sign*step*b) % m for a,b in zip(center,u))
                            palette.add(role*t + index[p])
                    yield sorted(palette)
        for _ in range(n-order):
            yield full(0)

    summary = dict(dimension=j, modulus=m, support_per_factor=sum(v is None for v in grid.values()),
                   exterior_classes=len(classes), order=n, core_order=15*t,
                   installed_order=order, padding_hosts=n-order, certified_cut_bound=t)
    return summary, neighbors()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int)
    parser.add_argument("--dimension", type=int)
    parser.add_argument("--modulus", type=int)
    parser.add_argument("--edges", type=Path, help="Write each edge once as two space-separated vertex IDs")
    args = parser.parse_args()
    if args.dimension is None and args.modulus is None and args.order is not None:
        j, m = parameters(args.order)
    elif args.dimension is not None and args.modulus is not None:
        j, m = args.dimension, args.modulus
    else:
        parser.error("Supply --order or both --dimension and --modulus")
    data, palettes = witness(j,m,args.order)
    if args.edges is not None:
        core = data["core_order"]
        edge_count = core*(core-1)//2
        with args.edges.open("w",encoding="ascii",newline="\n") as out:
            for a,b in combinations(range(core),2):
                out.write(f"{a} {b}\n")
            for h,palette in enumerate(palettes,core):
                for v in palette:
                    out.write(f"{v} {h}\n")
                edge_count += len(palette)
        data["edges"] = edge_count
    print(json.dumps(data,indent=2))


if __name__ == "__main__":
    main()
