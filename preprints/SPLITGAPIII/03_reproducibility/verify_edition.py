"""Verify the sealed preprint offline, optionally including an edition ZIP."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, permutations
import io
import json
from pathlib import Path
import re
from zipfile import ZipFile
import pymupdf

ED = Path(__file__).resolve().parents[1]
MANIFEST = "04_integrity/SHA256SUMS"
SUP = "split-gap-iii-lean-v0.4.zip"
PIN = "f5e51ff6a95f04688e92e5c291528ba14c689acda765282cde10c5a4c55cba46"
URL = "https://raw.githubusercontent.com/jtraverso/split-clique-partition-gap/main/preprints/SPLITGAPIII/05_formalization/" + SUP

def require(value, message):
    if not value:
        raise ValueError(message)

def hashes(payload):
    lines = payload.decode("utf-8-sig").splitlines()
    entries = dict(line.split("  ", 1)[::-1] for line in lines if line.strip())
    require(len(entries) == len([line for line in lines if line.strip()]), "duplicate manifest entry")
    return entries

def reports(payload):
    return [line.strip() for line in payload.decode("utf-8-sig").splitlines() if line.strip()]

def math_checks():
    def edges(*cliques):
        return Counter(tuple(sorted(pair)) for q in cliques for pair in combinations(q, 2))
    roots = edges("uhv", "uhw")
    auxiliary = edges("ku","kv","kw","kz","vz","wz","hz")
    require(len(auxiliary) == 7 and not auxiliary.keys() & roots.keys(), "hinge overlap")
    require(len(set("".join("".join(pair) for pair in auxiliary))) == 6, "hinge support")
    for wedge, triangles in [(("uv","hv"),("kuv","hvz","kwz")), (("uw","hw"),("kuw","hwz","kvz"))]:
        require(auxiliary + edges(*wedge) == edges(*triangles), "wrong hinge decomposition")
    for d in (4,5,7):
        vertices = range(d)
        pairs = list(combinations(vertices,2))
        # Check (12) on the elementary zero-margin switches on every four-set.
        for i,j,k,l in combinations(vertices,4):
            for a,b,c,e in [(i,j,k,l),(i,k,j,l)]:
                D = Counter({(a,b):1, (c,e):1})
                D[tuple(sorted((a,c)))] -= 1
                D[tuple(sorted((b,e)))] -= 1
                result = Counter()
                for u,v,x,y in permutations(vertices,4):
                    weight = D[tuple(sorted((u,v)))]
                    for m,n,sign in [(u,v,1),(x,y,1),(u,x,-1),(v,y,-1)]:
                        result[tuple(sorted((m,n)))] += sign * weight
                require(all(result[z] == 2*(d-1)*(d-2)*D[z] for z in pairs), "identity (12)")
    require(105*Fraction(1,4)+15*Fraction(1,8) == Fraction(225,8), "original-core coefficient")
    require(Fraction(1,8)*Fraction(1,64)**2 == Fraction(1,32768), "terminal coefficient")

def verify(archive):
    manifest = hashes((ED / MANIFEST).read_bytes())
    files = {p.relative_to(ED).as_posix() for p in ED.rglob("*") if p.is_file()}
    require(files == set(manifest) | {MANIFEST}, "edition file inventory")
    for path, digest in manifest.items():
        require(sha256((ED/path).read_bytes()).hexdigest() == digest, path)
    if archive:
        with ZipFile(archive) as z:
            require(set(z.namelist()) == files and len(z.namelist()) == len(files), "archive inventory")
            for path in files:
                require(z.read(path) == (ED/path).read_bytes(), "archive: " + path)
    supplement = (ED/"05_formalization"/SUP).read_bytes()
    require(sha256(supplement).hexdigest() == PIN, "supplement SHA-256")
    with ZipFile(io.BytesIO(supplement)) as z:
        internals = hashes(z.read("SHA256SUMS"))
        require(set(internals) | {"SHA256SUMS"} == set(z.namelist()), "freeze inventory")
        for path, digest in internals.items():
            require(sha256(z.read(path)).hexdigest() == digest, "freeze: " + path)
        historical = reports(z.read("AUDIT.txt"))
        driver = re.findall(r"^#print axioms (\S+)", z.read("SplitGapIIIAudit.lean").decode(), re.M)
        names = [re.match(r"'([^']+)'", line).group(1) for line in historical]
        require(len(set(names)) == len(names) == 77 and [a.strip() for a in driver] == names, "Lean audit inventory")
        require(reports((ED/"02_validation/v1.0/lean-axioms.txt").read_bytes()) == historical, "Lean replay")
        for line in historical:
            ax = re.search(r"depends on axioms: \[([^]]*)\]", line)
            require((ax and set(ax[1].split(", ")) <= {"propext","Classical.choice","Quot.sound"}) or "does not depend on any axioms" in line, line)
    en, es = [(ED / f"01_manuscript/split-gap-iii-{lang}.md").read_text(encoding="utf-8")
              for lang in ("en", "es")]
    expected = ["Theorem 1", "Theorem 2", "Theorem 3", "Theorem 4", "Lemma 5", "Proposition 6", "Lemma 7"]
    titles = re.findall(r"^\*\*(Theorem \d+|Lemma \d+|Proposition \d+)", en, re.M)
    require(titles == expected, "English statement ordering")
    titles_es = [x.replace("Teorema", "Theorem").replace("Lema", "Lemma").replace("Proposición", "Proposition")
                 for x in re.findall(r"^\*\*(Teorema \d+|Lema \d+|Proposición \d+)", es, re.M)]
    require(titles_es == expected, "Spanish statement ordering")
    def equations(source):
        return [block for block in re.findall(r"\$\$(.*?)\$\$", source, re.S) if r"\tag{" in block]
    require(equations(en) == equations(es), "numbered equations differ")
    require(re.findall(r"\\tag\{(\d+)\}", en) == list(map(str, range(1, 14))), "equation numbering")
    def urls(source):
        return re.findall(r"<(https?://[^>]+)>", source)
    require(urls(en) == urls(es) and URL in urls(en), "manuscript URL parity")
    require(PIN in en and PIN in es, "manuscript supplement hash")
    pdfs = [(directory, stem, lang) for directory, stem in (
        ("01_manuscript", "split-gap-iii"),
        ("05_formalization", "companion"),
        ("06_proof_ledger", "ledger"),
    ) for lang in ("en", "es")]
    for directory, stem, lang in pdfs:
        path = ED / directory / f"{stem}-{lang}.pdf"
        with pymupdf.open(path) as doc:
            require(all(page.get_text().strip() for page in doc), str(path))
            if directory == "01_manuscript":
                uris = {link.get("uri", "") for page in doc for link in page.get_links()}
                require(URL in uris, f"{lang} PDF supplement URI")
                require(doc.embfile_get(SUP) == supplement, f"{lang} PDF attachment differs")
                for ref in urls(en):
                    require(ref in uris, f"{lang} PDF URI missing: {ref}")
    math_checks()
    print("PASS — edition integrity, source freeze, 77 declaration reports, numbered statements and equations, PDF destinations, embedded ZIP and finite identities.")
    if archive:
        print("PASS — distribution ZIP matches the edition byte for byte.")

if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path)
    verify(parser.parse_args().archive)
