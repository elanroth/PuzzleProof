"""Check that every docstring of a Lean file appears word for word in its English specification.

Usage (from the library's root): python -I scripts/check_docstrings.py [FILE.lean ...]

With no arguments, every file under Chess/ is checked. The specification of `Chess/A/B.lean` is
`docs/spec/A.B.md` if it exists, else `docs/spec/A.md` (one spec covers a split module such as
`Chess.Game` or `Chess.Rules`). Whitespace is normalised and table pipes are ignored before
comparing. A docstring of a `def`, `abbrev`, `structure`, `inductive` or `instance` that is missing
is an error (exit status 1); a missing theorem docstring is only reported, since a spec may
paraphrase a lemma's English in a table. Untrusted tooling: it reads files and changes nothing.
"""
import glob
import os
import re
import sys

DEF_KEYWORDS = {"def", "abbrev", "structure", "inductive", "instance", "class"}
DOC = re.compile(
    r"/--((?:(?!-/).)*?)-/\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*"
    r"(\w+)\s+(?:\(priority := \w+\)\s+)?([^\s(:{\[]*)",
    re.S,
)


def norm(s):
    return re.sub(r"\s+", " ", s).strip()


def spec_for(path):
    rel = os.path.relpath(path, "Chess").removesuffix(".lean")
    parts = rel.split(os.sep)
    for k in range(len(parts), 0, -1):
        cand = os.path.join("docs", "spec", ".".join(parts[:k]) + ".md")
        if os.path.exists(cand):
            return cand
    return None


def check(path):
    spec = spec_for(path)
    if spec is None:
        print(f"{path}: no specification found")
        return 1
    lean = open(path, encoding="utf-8").read()
    text = norm(open(spec, encoding="utf-8").read().replace("|", " "))
    missing_defs, missing_thms, n = [], [], 0
    for m in DOC.finditer(lean):
        doc, kw, name = norm(m.group(1)), m.group(2), m.group(3)
        n += 1
        if doc in text:
            continue
        (missing_defs if kw in DEF_KEYWORDS else missing_thms).append(f"{kw} {name}: {doc[:90]}")
    print(f"{path} -> {spec}: {n} docstrings, {len(missing_defs)} definitions missing, "
          f"{len(missing_thms)} theorems missing")
    for line in missing_defs:
        print("  DEF  ", line)
    for line in missing_thms:
        print("  thm  ", line)
    return 1 if missing_defs else 0


def main(argv):
    files = argv or sorted(glob.glob("Chess/**/*.lean", recursive=True))
    status = 0
    for f in files:
        status |= check(f)
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
