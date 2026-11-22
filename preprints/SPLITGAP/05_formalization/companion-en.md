# Companion to *Nearly Quadratic Additive Gaps for Edge-Clique Partitions of Split Graphs*

*Preprint 1.0 · November 21, 2026*

## What the formal statement says

For each real $\eta>0$, the earlier universal theorem (now Corollary 1.2) supplies a threshold $N$. For every integer $n\ge N$ it gives a finite vertex type of cardinality $n$ and a connected split graph on it. The lower bound concerns the difference between the minimum size of an exact edge partition and the minimum cost of an exact fractional edge partition. The two optimizations range over cliques of every size at least two. The theorem has no hypothesis about an auxiliary graph, a packing, or a set of large density. [Corollary 1.2 in Lean](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/UniversalR434.lean) · [Gap](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/GapExtremal/Defs.lean) · [Partition numbers](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/GraphBase/Clique/Partition.lean)

## The quantitative and structural bounds

Theorem 1.1 gives one absolute $k>0$ and one threshold $N$. For every $n\ge N$, the Lean theorem constructs a connected split graph of order exactly $n$ whose physical gap is at least $k n^2(\log n)^{-5/2}\exp[-2\sqrt{\log(24/7)\log n}]$. It takes $\epsilon=7/(1080j)$. The verified grid count gives density at least $7/24-30\epsilon$ when $\epsilon m\ge43$ and $3\epsilon\le1/12$. This one-sided count suffices for Theorem 1.1. Lemma 6.1 gives the two-sided geometric estimate used in the manuscript. [Endpoint theorem](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/PolylogGap.lean) · [Quantitative order estimate](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/PolylogOrder.lean) · [Grid count](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/DensityThreshold.lean)

In Lemma 4.1, the upper bound of 16 local triangles and the example attaining it are both checked. The manuscript uses parity. Lean projects a packing onto the three color-pair layers. If 17 triangles were packed, each layer would lack one edge. A signed sum of role indices shows that the three missing edges have compatible endpoints, so they would complete a forbidden decomposition. Counting local triangles across all blocks gives $6\tau\le |X|+3z$. The formal energy estimate has numerator $6\tau$ and denominator $27(1+2R/\delta)$, which is the fraction in Lemma 4.1. The factor six also enters the finite graph bound used by the endpoint theorem. [Local packing](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/LocalPacking.lean) · [Block count and defect](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/CoreDefect.lean) · [Finite graph bound](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/FiniteR434.lean)

The main endpoint for Theorems 1.1 and 1.4 is `universal_R434_linear`. It gives a split graph of order exactly $n$, with the gap bound and `SurvivesCuts G ((n+4)/5)` on the same graph. The latter predicate requires the graph to remain connected after deleting any set of fewer than $\lceil n/5\rceil$ vertices. After constructing the residual graph, we add isolated vertices to it. In the split graph those vertices enter the clique core and every host neighborhood. The Lean bridge transports the upper bound on integral residual scores by projection and transports the specific fractional witness by extension. These two certificates suffice for the gap lower bound. [Residual isolates](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/ResidualIsolates.lean) · [Universal hosts](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/UniversalHosts.lean) · [Joint theorem](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/PolylogGap.lean)

The endpoint `universal_R434_compact` uses the same 24-class coloring with the full-role neighborhood enlargement. It gives a cut bound of order $n/\sqrt{\log n}$. For the gap bound alone, `universal_R434_grouped` assigns each role edge to one of four matchings in its layer, then uses a common midpoint host for all pairs in a matching class. The Lean proof checks that the larger palettes are independent in the residual graph and the assignments still form matchings. There are 66 always-missing role pairs and $12\cdot24j$ geometric labels per position. With the 15 core roles, the base graph uses $(81+288j)m^{2j}$ vertices. [Compact exterior coloring](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/EHPSCompactExterior.lean) · [Role matchings](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/RoleMatchings.lean) · [Grouped hosts](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/GroupedHosts.lean) · [Graph order](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/GroupedGap.lean)

Corollary 1.3 is a written deduction using split containment and the external uniform rounding theorem [2, Theorem 1.10]. The Lean root checks the constructive lower bounds on split graphs. The two limits for the chordal maximum also use the published upper bound.

## The mixed packing corollary

The endpoint `universal_R434_linear_mixed` supplies the same asymptotic bound and cut guarantee with `gapWithFracFour`. This is the minimum unrestricted integral partition cost minus the minimum fractional cost with pieces of order at most four. The proof retains the size-three support bound of the affine fractional witness through the addition of isolated residual vertices and the fractional host completion. Passing from unrestricted to order-four integral pieces can only increase the gap. Corollary 7.2 uses the written identity between exact order-four partitions and mixed packing gains to express that lower bound in the notation of Paper IV. [Main endpoint](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/PolylogGap.lean) · [Bounded fractional cost](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/GapExtremal/Completion.lean) · [Host completion](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/GapExtremal/Bridge.lean)

## Two calculations behind the proof

**Why shared vertices matter.** Each affine block has 54 edges. The 36 triangles in the local table have weight $1/2$ each and use every edge to capacity. Since each triangle saves two pieces, these triangles contribute 36 to the residual score in one block. Edges have unique owners, so this calculation scales exactly with the number of blocks. The obstruction to an integral decomposition within one block does not scale by itself. For example, fix an intercept $x$ and distinct directions $a,b$ with $(a+b)/2$ also available. The positions $x,x+a,x+a+b$ have the three allowed directions. For a surviving triple of roles they form a triangle whose edges come from three different blocks. Section 4 deals with precisely this possibility. [Local certificate](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/LocalH54.lean) · [Direction calculation](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/CoreDirections.lean)

**Where the coefficient comes from.** Write $\rho$ for the density of one planar factor and $c=-\log\rho$. The loss from taking $j$ factors is $\rho^j$. The scaled potential costs another factor of order $jm^2$, where $m$ is the grid modulus and $2j\log m$ is approximately $\log n$. To leading order the negative logarithm of the relative gap is therefore bounded by $cj+(\log n)/j$. The two terms agree at $j=\sqrt{(\log n)/c}$. The planar density can approach $7/24$ from below, which gives $2\sqrt{\log(24/7)}$. The earlier proof of Corollary 1.2 fixes the planar support before taking $n$ large. Theorem 1.1 varies it with $j$ and keeps the endpoint coefficient. Nothing in this optimization determines the best possible coefficient for split graphs. [Density threshold](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/DensityThreshold.lean) · [Choice of parameters](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/UniformOrder.lean)

**Explicit multipliers.** Put $c=\log(24/7)$ and $K=200(1080/7)^2$. The gap prefactor at each endpoint is
$$
 k(A)=\frac{2c^{5/2}e^{-2-2c}}{27A^2(1+K)}.
$$
Theorem 1.4 uses $A=78375$ and $k(A)\approx4.9144\cdot10^{-20}$. The compact endpoint uses $A=3135$ and $k(A)\approx3.0715\cdot10^{-17}$, with cut bound at least $\sqrt c\,n/(Ae\sqrt{\log n})$. The grouped endpoint uses $A=369$ and $k(A)\approx2.2170\cdot10^{-15}$ for connected split graphs. All three estimates use $\epsilon=7/(1080j)$. For $\epsilon=y/j$, the leading multiplier from the density and potential estimates is proportional to $y^2(1-30y/(7/24))$, maximized at $y=7/1080$. [Parameter calculation](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/PolylogOrder.lean)

The offset in the signed-edge estimate admits a two-constraint linear program. Normalize $0\le f\le R$ and write $g=f-u$. An upper bound $M$ on the magnitude of a negative edge price must satisfy $M\ge u$ and $M\ge 2R-2u$ if only this range is used. Weighting those inequalities by $2/3$ and $1/3$ gives $M\ge2R/3$. The choice $u=2R/3$ attains equality. A better price bound would therefore have to exploit information beyond a uniform shift and the range of $f$.

## Reading the proof alongside Lean

| Manuscript | Formal counterpart | What to check |
|---|---|---|
| §2, transfer to a split graph | [Exact-order transfer](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/ExactGraphTransfer.lean) | Given a feasible fractional score and an upper bound on every integral score, their difference bounds the physical graph gap from below. The manuscript also derives an identity between the two optimal savings. |
| §3 and Appendix A, the local obstruction | [Local graph and prices](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/LocalH54.lean) | There are 45 triangles, 36 in the fractional support. Check the order of edge types in the code when translating a price from the appendix. |
| §4, nearly optimal pieces | [Tripartite slack](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/TripartiteSlack.lean) · [Tight triangles](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/TightTriangles.lean) | A zero-slack piece can be partitioned into triangles. Positive slack bounds the number of edges set aside. |
| §4, affine blocks and energy | [Core defect](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/CoreDefect.lean) · [Fractional score](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/CoreFractional.lean) | The integral estimate allows mixed triangles. The fractional witness uses only triangles in their own blocks. |
| §5, host count and padding | [Midpoint hosts](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/MidpointHosts.lean) · [Product host bound](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/EHPSHostTransfer.lean) | The compact budget is $255+2880j$ per position. The full construction of Theorem 1.4 uses $25(255+2880j)$ to leave room for the universal vertices and their hosts. |
| §6, the planar input | [Region](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/EHPSRegion.lean) · [Potential](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/EHPSPotential.lean) · [Grid density](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/EHPSDensity.lean) | The proof develops the particular density and midpoint inequalities used here inside Lean. |
| §6, final bound | [Finite graph](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/FiniteR434.lean) · [Corollary 1.2](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/UniversalR434.lean) · [Theorem 1.1](https://github.com/jtraverso/split-clique-partition-gap/blob/ccb5444b2ecdff9de1d6221133633a25a224953d/R434/PolylogGap.lean) | The proof chooses an odd modulus and pads to exactly the prescribed order. |
| §1 and §7, consequences | [Manuscript](../01_manuscript/split-gap-en.md) | The chordal upper bound uses the cited rounding theorem. The triangle and mixed packing statements follow by completion, using the bounded fractional witness for the latter. |

The Appendix A example can also be checked with the Python standard library. The verifier reads the seven deleted triangles and the displayed packing directly from the manuscript, then exhausts all assignments that could cover 17 distinct edges of the first color pair.

```sh
python 03_reproducibility/check_local_packing.py
```

## Generating a graph

Run the following from the edition’s `03_reproducibility` directory. The first command writes a complete edge list with zero-based vertex IDs. The second reconstructs the finite example, checks every assigned nonedge, checks each matching and independent neighborhood, and computes the edge-list hash.

~~~sh
python witness.py --dimension 1 --modulus 3 --order 4620 --edges example.edges
python check_robust_witness.py
~~~

The generator and finite example use the construction with enlarged role neighborhoods. The example has 135 core vertices, three padding hosts, and 64,962 edges. Each host has at least nine neighbors in the core, and deleting the nine neighbors of a padding host isolates it. There is one direction and hence nine blocks. Taking a constant potential of range zero in Lemma 4.1 gives $\Delta(G)\ge2$ on this example. This small example checks the construction; the asymptotic theorem has a sufficiently-large-order hypothesis. For automatic parameter selection use `python witness.py --order N --edges graph.edges` with a sufficiently large integer in place of `N`. Omitting `--edges` prints the parameters and counts. [Generator](../03_reproducibility/witness.py) · [Example certificate](../03_reproducibility/robust-example.json)

## Reproducing the formal check

The [source archive](split-gap-lean-v1.0.zip) contains a portable Lean project. In its `lean` directory, run:

```sh
lake exe cache get
lake build SplitGap
lake build +R434.CheckStrengthenings
```

The package pins Lean and all external dependencies. The final build record binds the checked sources, proof revision, build targets and axiom output. The checker covers the original gap, the joint cut guarantee, the compact and grouped bounds, and the mixed lower bound. [Source-bound audit](../02_validation/v1.0/lean/status.json) · [Axiom queries](../02_validation/v1.0/lean/checking-axioms.log) · [Reproduction instructions](../03_reproducibility/README.md)


## Provenance and attribution

The fractional split-profile calculation of Paper I and the chordal extremal result of Paper II motivated comparing integral and fractional optima on the same graph. Paper III gives the integral split upper bound and poses Problem 12.1. The exact transfer in Section 2 builds on the host assignments of Paper V. The closest cited precedents for repeating finite obstructions are the lower bounds for covers and packings in §5 of Balogh et al. The arithmetic density, potential and the corresponding coefficient in the progression-free setting are due to Elsholtz, Hunter, Proske and Sauermann. Here the direction set retains its progressions. The graph argument estimates their cost in an integral packing. [Paper III](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/3cbd90eed41af7e86ac6f1f4b8c796e20a5e661f/preprints/PAPER_III) · [Paper V](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/3cbd90eed41af7e86ac6f1f4b8c796e20a5e661f/preprints/PAPER_V) · [Balogh et al.](https://arxiv.org/html/2412.05522v3) · [Elsholtz et al.](https://arxiv.org/html/2406.12290v1)


The files imported from the earlier formalization retain their copyright headers. For files marked Apache 2.0, the [license text](LICENSE-Apache-2.0.txt) is included.



Certo-Math v0.40.0 checked the fifteen-vertex certificate. [R419 certificate](https://github.com/jtraverso/certo-math/blob/0590da36a2af900b9f23d9d292aac62eb6b06ca9/research/R419/NOTE.md).
