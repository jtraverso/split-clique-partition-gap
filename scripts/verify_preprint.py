"""Read-only integrity and audit checks for Split Gap preprint 1.0."""
from hashlib import sha256
import json
from pathlib import Path
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[1]
EDITION = ROOT / "preprints" / "SPLITGAP"
VALIDATION = EDITION / "02_validation" / "v1.0"
MANIFEST = EDITION / "04_integrity" / "SHA256SUMS"
ARCHIVE = ROOT / "archives" / "split-gap-preprint-v1.0.zip"
FREEZE = EDITION / "05_formalization" / "split-gap-lean-v1.0.zip"
TOOLCHAIN_FILES = {"lake-manifest.json", "lakefile.toml", "lean-toolchain"}


def check(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def digest(data):
    return sha256(data).hexdigest()


def file_hash(path):
    return digest(path.read_bytes())


def main():
    rows = [line.split("  ", 1) for line in MANIFEST.read_text(encoding="utf-8").splitlines()]
    names = [name for _, name in rows]
    expected = {p.relative_to(EDITION).as_posix() for p in EDITION.rglob("*")
                if p.is_file() and p != MANIFEST}
    check(len(names) == len(set(names)) and set(names) == expected, "edition manifest coverage")
    for sha, name in rows:
        check(file_hash(EDITION / name) == sha, name)

    sidecar = ARCHIVE.with_suffix(".zip.sha256").read_text(encoding="ascii").strip()
    check(sidecar == f"{file_hash(ARCHIVE)}  {ARCHIVE.name}", "edition archive SHA-256")
    with ZipFile(ARCHIVE) as z:
        check(z.testzip() is None, "edition archive CRC")
        paths = expected | {MANIFEST.relative_to(EDITION).as_posix()}
        check(sorted(z.namelist()) == sorted(f"SPLITGAP-v1.0/{p}" for p in paths),
              "edition archive file list")
        for name in paths:
            check(z.read(f"SPLITGAP-v1.0/{name}") == (EDITION / name).read_bytes(),
                  "edition archive member " + name)

    clean_dir = VALIDATION / "lean"
    clean = json.loads((clean_dir / "status.json").read_text(encoding="utf-8"))
    checked = clean_dir / "SOURCE_HASHES.json"
    sources = json.loads(checked.read_text(encoding="utf-8"))
    check(clean["phase"] == "PASS" and clean["source_count"] == len(sources)
          and clean["source_manifest_sha256"] == file_hash(checked), "clean build source binding")
    with ZipFile(FREEZE) as z:
        check(z.testzip() is None, "Lean source archive CRC")
        license_name = "LICENSE-Apache-2.0.txt"
        check(sorted(z.namelist()) == sorted("lean/" + name for name in (*sources, license_name, "Audit/AllAxioms.lean")),
              "Lean archive contains only the pinned sources and license")
        check(z.read("lean/" + license_name) == (FREEZE.parent / license_name).read_bytes(),
              "Lean archive license")
        check(z.read("lean/Audit/AllAxioms.lean") == (clean_dir / "AllAxioms.lean").read_bytes(), "exhaustive axiom checker")
        for name, sha in sources.items():
            archived = z.read("lean/" + name)
            check(digest(archived) == sha, "Lean source archive member " + name)
            current = (ROOT / name).read_bytes()
            if name in TOOLCHAIN_FILES:
                # Git can check out the same configuration with a different line ending.
                current, archived = (data.replace(b"\r\n", b"\n") for data in (current, archived))
            check(current == archived, "repository Lean source " + name)
    axioms = clean["declarations"]
    check(len(axioms) == 24 and all(set(filter(None, x.split(", "))) <=
          {"propext", "Classical.choice", "Quot.sound"} for x in axioms.values()), "axiom audit")
    check("GapExtremal.R434.universal_R434_linear_mixed" in axioms, "mixed gap theorem")

    report = json.loads((VALIDATION / "AUDIT_RESULT.json").read_text(encoding="utf-8"))
    check(report["technical_audit"] == "PASS" and report["proof_revision"] == clean["commit"],
          "audit proof revision")
    for path, sha in report["artifacts"].items():
        check(file_hash(EDITION / path) == sha, "audited artifact " + path)
    rows = (clean_dir / "all-theorems.tsv").read_text(encoding="utf-8").splitlines()[1:]
    declarations = {}
    for row in rows:
        mod, name, dependencies = row.split("\t")
        check(dependencies.startswith("#[") and dependencies.endswith("]"), name)
        declarations[mod, name] = set(filter(None, dependencies[2:-1].split(", ")))
    check(len(rows) == len(declarations) == report["theorem_declarations"]
          and set(axioms) <= {name for _, name in declarations}
          and all(ds <= set(clean["axioms"]) for ds in declarations.values()), "all project theorems")
    index = json.loads((EDITION / "PUBLICATION_INDEX.json").read_text(encoding="utf-8"))
    check(index["version"] == "1.0" and index["doi"] == "10.5281/zenodo.24408988"
          and index["doi_status"] == "reserved_not_published" and index["distribution"] == "preprint",
          "publication metadata")
    print(f"PASS: {len(names)} edition files, {len(sources)} pinned Lean sources, {len(rows)} theorem declarations and 24 named checks.")
    print("Technical audit PASS. Publication authorization is tracked separately.")


if __name__ == "__main__":
    main()
