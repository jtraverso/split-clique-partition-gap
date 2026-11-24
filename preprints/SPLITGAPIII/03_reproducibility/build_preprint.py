"""Typeset the edition in a separate directory with Pandoc 3.12 and Tectonic."""
from argparse import ArgumentParser
from pathlib import Path
import re
import shutil
import subprocess
import pymupdf

HERE = Path(__file__).resolve().parent
EDITION = HERE.parent
parser = ArgumentParser(description=__doc__)
parser.add_argument("--output", required=True, type=Path)
parser.add_argument("--pandoc", default="pandoc")
parser.add_argument("--tectonic", default="tectonic")
parser.add_argument("--only-cached", action="store_true")
args = parser.parse_args()
out = args.output.resolve()
if out.is_relative_to(EDITION) or EDITION.is_relative_to(out):
    parser.error("Use a directory separate from the edition")
preamble = (HERE / "preamble.tex").read_text(encoding="utf-8")
for name in ("01_manuscript", "05_formalization", "06_proof_ledger"):
    for md in sorted((EDITION / name).glob("*-??.md")):
        dest = out / name
        dest.mkdir(parents=True, exist_ok=True)
        text = md.read_text(encoding="utf-8")
        title = text.splitlines()[0][2:]
        spanish = md.stem.endswith("-es")
        body = text[text.index("## "):]
        if (md.parent / "figures").is_dir():
            shutil.copytree(md.parent / "figures", dest / "figures", dirs_exist_ok=True)
            body, count = re.subn(r"!\[[^\n]+\]\(figures/(crossing-hinge(?:-es)?)\.svg\)\n\n\*(?:Figure|Figura) 1\. (.*?)\*", lambda m: "\n".join([
                r"\begin{figure}[htbp]\centering", r"\includegraphics[width=.92\linewidth]{figures/" + m[1] + ".pdf}",
                r"\caption{" + m[2] + "}", r"\end{figure}"]), body)
            if count != 1:
                raise ValueError("Expected one hinge figure")
        body = subprocess.run([args.pandoc, "-f", "markdown+raw_tex+tex_math_dollars", "-t", "latex", "--wrap=none", "--syntax-highlighting=none"],
                              input=body, capture_output=True, check=True, text=True, encoding="utf-8").stdout
        body = re.sub(r"\\texttt\{([a-zA-Z0-9_\\.-]{12,})\}", lambda m: r"\nolinkurl{" + m[1].replace(r"\_", "_") + "}", body)
        tex = dest / md.with_suffix(".tex").name
        source = "\n".join([preamble, r"\hypersetup{pdflang=en-US,colorlinks=true,urlcolor=blue,linkcolor=blue,pdftitle={" + title + "},pdfauthor={Juan Pablo Traverso Gianini}}",
            r"\title{" + title + "}", r"\author{Juan Pablo Traverso Gianini\\\small Independent researcher, Santiago, Chile\\\small\href{mailto:jtraverso@gmail.com}{jtraverso@gmail.com}\quad\href{https://orcid.org/0009-0003-6068-4096}{ORCID 0009-0003-6068-4096}}",
            r"\date{Preprint 1.0 \enspace·\enspace November 24, 2026}", r"\begin{document}\raggedbottom\maketitle",
            r"\begin{center}Paper III in the series on clique partition gaps in split graphs.\end{center}",
            r"\noindent DOI \url{https://doi.org/10.5281/zenodo.24494747}\\",
            r"Series repository \url{https://github.com/jtraverso/split-clique-partition-gap}", body, r"\end{document}", ""])
        if spanish:
            source = (source.replace("[english,11pt", "[spanish,11pt")
                      .replace("[english]{babel}", "[spanish,es-noshorthands]{babel}")
                      .replace("pdflang=en-US", "pdflang=es-CL")
                      .replace("Independent researcher", "Investigador independiente")
                      .replace("November 24, 2026}", "24 de noviembre de 2026}")
                      .replace("Paper III in the series on clique partition gaps in split graphs.",
                               "Artículo III de la serie sobre brechas de partición en cliques en grafos split.")
                      .replace(r"Series repository \url", r"Repositorio de la serie \url"))
        tex.write_text(source, encoding="utf-8", newline="\n")
        subprocess.run([args.tectonic, *(["--only-cached"] if args.only_cached else []), "--keep-logs", tex.name], cwd=dest, check=True)

        if name == "01_manuscript":
            archive = EDITION / "05_formalization" / "split-gap-iii-lean-v0.4.zip"
            pdf = tex.with_suffix(".pdf")
            with pymupdf.open(pdf) as document:
                document.embfile_add(archive.name, archive.read_bytes(), filename=archive.name,
                                     desc="Lean 4 sources, pinned dependencies and declaration audit")
                output = document.tobytes(garbage=4, deflate=True)
            pdf.write_bytes(output)
