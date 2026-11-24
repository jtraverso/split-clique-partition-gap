# Formalization companion for Recovering Host-Triangle Decompositions after Random Deletions in Split Graphs

## Reading the formal statements

The English preprint uses the source archive dated November 24, 2026 that accompanied drafts 0.4 and 0.5. Section 7 gives its SHA-256 and the main declaration names. The supplementary ZIP is also embedded in the manuscript PDF. The audit driver prints axiom dependencies for 77 declarations in the namespace `SplitGapIII`.

The selected-support theorem is Theorem 1 in the preprint (Theorem 5 in the supplement's original numbering). The lemma `hosted_clique_deficit_mem` converts integer zero-margin corrections into a statement about the physical triangle lattice under its switch-availability hypotheses. The lemma `selected_hinge_condition` turns counts of ordered completions into the edge-set condition H4. The concentration estimates and cut argument producing a single suitable random support appear in §5 and Appendix B.

Theorem 2 (formerly Theorem 6) compares statistics on two scales. The lemma `hosted_pasch_one_block` identifies a block from the four hosted triangles and the ownership conditions. Given the selected seed, the physical hypotheses and the bounds comparing seed and reference targets, `selected_decomposition_with_reference_targets` yields a common decomposition. Section 6 establishes the target comparison in the random construction and derives both asymptotic coefficients. Theorem 3 (formerly Theorem 1) is the gap application. The all-orders development in Lean uses extra host copies. Section 2 proves the sharp threshold for a single pool analytically.

## Reproducing the declaration audit

Extract the source ZIP into an empty directory. The toolchain file specifies Lean 4.35.0-rc3, and the Lake manifest pins Mathlib and the physical absorption library. From the extracted root run

```sh
lake exe cache get
lake build SplitGapIII
lake env lean SplitGapIIIAudit.lean
```

Compare the declaration names and their axiom lists with `AUDIT.txt` in the ZIP. Line endings may differ. The preprint validation directory includes a replay against previously compiled dependencies. The full archive checksum also identifies the exact sources and the historical record.

## Edition concordance

| Review draft 0.5 | Preprint 1.0 |
|---|---|
| Theorem 5, balanced support | Theorem 1 |
| Theorem 6, statistical recovery | Theorem 2 |
| Theorem 1, gap and connectivity | Theorem 3 |
| Theorem 2, random host lists | Theorem 4 |
| Lemma 3, two coordinate orders | Lemma 5 |
| Proposition 4, deterministic budgets | Proposition 6 |
| Lemma 6.1, localization of Pasch configurations | Lemma 7 |

All thirteen numbered displays retain their draft numbering. The manuscript and the source archive are available in the series repository. <https://github.com/jtraverso/split-clique-partition-gap/tree/main/preprints/SPLITGAPIII>
