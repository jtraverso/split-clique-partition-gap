# Internal audit · Split Gap III · Preprint 1.0

**PASS for the final bilingual files staged for author review.** The deployment target is `jtraverso/split-clique-partition-gap`, under `preprints/SPLITGAPIII`. The distribution ZIP and its checksum belong in `archives/` at the repository root.

| Check | Result |
|---|---|
| English source | All 30 displayed formulas match commit `75bad56`. The editorial changes introduce the definitions before the prior work, specify the scope of gap preservation, correct one reference to Lemma 7 and simplify the supplement citation. Reference [6] now includes the DOI of *Triangle decompositions III*. The acknowledgments and AI disclosure are unchanged. |
| Spanish translation | The translation includes the complete proofs and both appendices. The paragraph-by-paragraph check matches mathematical expressions, numbered equations, equation references and citations. The two orders of the coordinates and the hinge figure have Spanish labels. |
| PDF output | The English and Spanish manuscripts, companions and proof ledgers were typeset, rendered and inspected. The audit records the TeX and PDF hashes. Each manuscript PDF contains the canonical supplement URL and an embedded ZIP that matches the staged Lean freeze byte for byte. |
| Lean | The freeze from November 24, 2026 retains its original SHA-256. The audit driver was executed with the pinned Lean executable and previously compiled libraries. The 77 declaration reports match the original archive. Section 7 identifies the probabilistic and asymptotic arguments established in the manuscript. |
| Finite arithmetic and distribution | The edition verifier checks the hinge, the finite coefficient identities, the statement and equation lists, and the published URL strings in both manuscript PDFs. It checks the internal freeze manifest and compares the files in the ZIP against the staged edition. |

The reserved DOI is `10.5281/zenodo.24494747`. The deposit remains private with its working title. The staged [deposit metadata](../../zenodo-metadata.json) contains the final title. The author review precedes the public upload and deposit. The anonymous download check must use the actual public destinations after publication. It should follow the DOI to the final title and compare the downloaded distribution ZIP and Lean supplement to the staged SHA-256 values.

[Semantic diff](semantic-diff.json) · [Bilingual parity](BILINGUAL_QA.json) · [PDF validation](PDF_QA.json) · [Lean axiom reports](lean-axioms.txt)
