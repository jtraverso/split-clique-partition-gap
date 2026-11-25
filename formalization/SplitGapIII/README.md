# Split Gap III formalization for Palomar

This project provides an independent statement interface for a result extending the first preprint and a bipartite list-recovery lemma used in its proof.

* At logarithmic two-incidence supply, an indexed split graph of order \(n\) has a clique-partition gap of order at least \((pn)^{3/2}\). With probability at least \(1-2n^{-8}\), the surviving graph has a complete physical reassignment and exactly the original gap.
* In a bipartite block, a proper midpoint labeling bounds the degrees of its request graph. Lists of surviving hosts with at least this many colors admit a proper assignment with each chosen host in the list of its request.

For the proofs, see `SplitGapIV/QuantitativeRecovery.lean` and `Solution.lean`. `Challenge.lean` imports only Mathlib. The [first preprint](../../preprints/SPLITGAPIII/README.md) treats fixed survival probability and gives the proofs of the near-quadratic bound and statistical asymptotics. The Apache 2.0 licence applies to the Lean sources. The manuscripts and figures carry the edition licence.
