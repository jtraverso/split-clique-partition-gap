# Reproduction

## Manuscript and companion

Install Pandoc and Tectonic. From the edition directory, run:

```sh
python 03_reproducibility/build_preprint.py --logs build-logs
```

The builder regenerates the delivered LaTeX from each English and Spanish Markdown source and runs the engine three times. To compile the LaTeX directly, run Tectonic from the directory of the relevant file. The manuscript has a local figures directory.

## Lean

Unzip the source archive in `05_formalization` and enter the `lean` directory. With Elan and the toolchain in `lean-toolchain`, run:

```sh
lake exe cache get
lake build SplitGap
lake build +R434.CheckStrengthenings
lake env lean Audit/AllAxioms.lean
```

The dependency revisions are fixed in `lake-manifest.json`. The root `SplitGap` exposes the quantitative and structural endpoints. The separate checker prints the axioms. The clean-build record in `02_validation/v1.0/lean` gives the proof revision and the toolchain used. The audit reused caches for the locked external dependencies and rebuilt the project modules.

## Finite certificates

From a checkout of the official repository, run:

```sh
python -B audit/check_local_packing.py
python -B audit/host-compression/check.py
python -B audit/check_robust_witness.py
```

The three programs check the local packing optimum, the finite host-matching constructions, and the explicit witness described in the companion. Their output is recorded in the [finite-check log index](../02_validation/v1.0/FINITE_CHECKS.json).

## Integrity

From the repository root, run `python scripts/verify_preprint.py`. The edition manifest can also be checked with `sha256sum -c 04_integrity/SHA256SUMS` from the edition directory.
