"""Check the Appendix A packing against Section 3 and test whether 17 triangles fit."""

from itertools import product
from pathlib import Path
import re


def displayed_triples(text, anchor):
    block = text.split(anchor, 1)[1].split("$$", 2)[1]
    return [tuple(map(int, triple)) for triple in re.findall(r"\((\d),(\d),(\d)\)", block)]


def edges(triangle):
    a, b, c = triangle
    return {(0, a, b), (1, b, c), (2, a, c)}


def fits(cells, choices, index, used, needed):
    if needed == 0:
        return True
    if len(cells) - index < needed:
        return False
    a, b = cells[index]
    for c in choices[a, b]:
        other_edges = {(1, b, c), (2, a, c)}
        if used.isdisjoint(other_edges) and fits(cells, choices, index + 1, used | other_edges, needed - 1):
            return True
    return fits(cells, choices, index + 1, used, needed)


manuscript = Path(__file__).resolve().parents[1] / "01_manuscript/split-gap-en.md"
text = manuscript.read_text(encoding="utf-8")
deleted = displayed_triples(text, "Delete the edges of the seven triangles")
witness = displayed_triples(text, "An integral packing of size 16 is given below")
roles = range(5)
all_edges = set(product(range(3), roles, roles))
surviving = all_edges - set().union(*(edges(t) for t in deleted))
triangles = [t for t in product(roles, repeat=3) if edges(t) <= surviving]
used = set().union(*(edges(t) for t in witness))
if (len(deleted), len(surviving), len(triangles), len(witness), len(used)) != (7, 54, 45, 16, 48):
    raise ValueError("Unexpected size of the graph or the displayed witness")
if not set(witness) <= set(triangles):
    raise ValueError("The displayed packing uses a missing edge")
# Each surviving 01 edge is used at most once. Try all feasible third roles
# and the option of leaving that edge unused.
choices = {(a, b): [c for c in roles if (a, b, c) in triangles] for i, a, b in surviving if i == 0}
cells = sorted(choices, key=lambda pair: (len(choices[pair]), pair))
if fits(cells, choices, 0, set(), 17):
    raise ValueError("Found a packing of 17 triangles")
print("PASS: 54 edges, 45 triangles, 16 displayed triangles on 48 distinct edges; no packing of 17.")
