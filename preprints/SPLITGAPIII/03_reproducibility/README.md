# Reproducing the bilingual edition

From the extracted edition root, with Python 3.12 and PyMuPDF 1.28.2, run

```sh
python 03_reproducibility/verify_edition.py
```

Add `--archive PATH` to compare the distribution ZIP against every sealed file. Its checksum is stored next to the ZIP in the series repository. The verifier checks all internal hashes in the Lean archive, the 77 declaration reports, equation, statement and URL parity, the hinge and finite arithmetic, the canonical supplement link and the bytes of the PDF attachment.

## Regenerating the PDF files

The source typesets with Pandoc 3.12.1, Tectonic 0.17.0 and the series preamble. PyMuPDF embeds the exact Lean ZIP in both manuscripts. Run from the extracted edition root

```sh
python 03_reproducibility/build_preprint.py --output ../split-gap-iii-rebuilt
```

The output directory must lie outside the edition. Use `--pandoc` and `--tectonic` for explicit program paths. Use `--only-cached` when the Tectonic bundle and fonts are already available. PDF timestamps and trailer identifiers can change on regeneration. The edition checksum verifies the distributed bytes.

## Lean

The guide in `05_formalization/companion-en.md` gives the commands for a full source build. The dated replay in `02_validation/v1.0/lean-axioms.txt` used the pinned Lean executable and a cache of compiled modules. The 77 results match the archive after normalizing line endings.
