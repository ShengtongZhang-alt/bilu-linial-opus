#!/usr/bin/env python3
"""Find declarations with the same fully qualified name in BiluLinial/Tight (hard clashes when
both files are imported together), and same short name in different sub-namespaces of
BiluLinial.Tight (ambiguity hazards under `open`).

Usage: /tmp/tight-venv/bin/python scripts/tight/check_secs_dups.py
"""
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TIGHT = ROOT / "BiluLinial" / "Tight"

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s:({\[]+)"
)


def scan(path):
    ns = []  # stack of (kind, name)
    out = []
    in_comment = 0
    for ln, line in enumerate(path.read_text().splitlines(), 1):
        s = line
        # crude block comment tracking
        if in_comment:
            if "-/" in s:
                in_comment = 0
            continue
        if s.lstrip().startswith("/-") and "-/" not in s:
            in_comment = 1
            continue
        m = re.match(r"^\s*namespace\s+(\S+)", s)
        if m:
            ns.append(("ns", m.group(1)))
            continue
        m = re.match(r"^\s*section(?:\s+(\S+))?", s)
        if m and not s.strip().startswith("section_"):
            ns.append(("sec", m.group(1) or ""))
            continue
        m = re.match(r"^\s*end(?:\s+(\S+))?\s*$", s)
        if m:
            if ns:
                ns.pop()
            continue
        m = DECL.match(s)
        if m:
            kind, name = m.groups()
            if kind == "instance":
                continue
            if "private" in s.split(kind)[0]:
                continue
            prefix = ".".join(n for k, n in ns if k == "ns")
            full = (prefix + "." + name) if prefix else name
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            out.append((full, str(path.relative_to(ROOT)), ln))
    return out


def main():
    decls = []
    for f in sorted(TIGHT.rglob("*.lean")):
        decls.extend(scan(f))
    by_full = defaultdict(list)
    for full, f, ln in decls:
        by_full[full].append((f, ln))
    print("== same fully qualified name in two files (hard clash if co-imported) ==")
    for full, locs in sorted(by_full.items()):
        files = {f for f, _ in locs}
        if len(files) > 1:
            print(full)
            for f, ln in locs:
                print(f"    {f}:{ln}")
    print()
    print("== same name modulo a SecA/SecB/SecC sub-namespace (ambiguous under `open`) ==")
    strip = re.compile(r"^BiluLinial\.Tight\.(SecA|SecB|SecC)\.")
    by_short = defaultdict(list)
    for full, f, ln in decls:
        short = strip.sub("BiluLinial.Tight.", full)
        by_short[short].append((full, f, ln))
    for short, locs in sorted(by_short.items()):
        fulls = {fu for fu, _, _ in locs}
        if len(fulls) > 1:
            print(short)
            for fu, f, ln in locs:
                print(f"    {fu}  ({f}:{ln})")


if __name__ == "__main__":
    sys.exit(main())
