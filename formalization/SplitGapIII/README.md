# Split Gap III formalization for Palomar

This project provides an independent statement interface for two results used in Sections 3–4 of the preprint. The statements use a clique core and an independent set of hosts.

* In a bipartite block, a proper midpoint labeling bounds the degrees of its request graph. Lists of surviving hosts with at least this many colors admit a proper assignment. Each triangle uses its two physical crossing edges.
* If the host system has a complete assignment initially and sufficiently large surviving lists imply another complete assignment, an explicit finite tail sum bounds the probability that the two clique partition gaps differ. The shared comparison is the residual packing gap.

For the proof, see `SplitGapIII/Reassignment.lean` and `SplitGapIII/RecoveryProbability.lean`. `Challenge.lean` imports only Mathlib and states the compared results. The original sources and their provenance accompany `Solution.lean`. The preprint gives the random construction and statistical asymptotics in the written proof. See [the public preprint and freeze](../../preprints/SPLITGAPIII/README.md). The Apache 2.0 licence applies to the Lean sources. The manuscripts and figures carry the edition licence.
