#!/usr/bin/env python3
"""Generate ES/Unicode/TextData.lean: the Unicode data String.prototype's case conversion and
normalization use.

usage: tools/gen_es_text.py [path/to/ucd]   (default third_party/ucd/17.0.0, the version the regex
       data uses: see tools/gen_regex_unicode.py, which downloads it)
source: https://www.unicode.org/Public/17.0.0/ucd/

What it writes:
- full case mappings (spec: https://tc39.es/ecma262/#sec-string.prototype.tolowercase): the
  unconditional mappings of SpecialCasing.txt, else UnicodeData.txt's simple ones; the
  language-sensitive and context-sensitive ones are left out (Final_Sigma is applied by
  ES/Unicode/Text.lean, from the Cased and Case_Ignorable ranges written here);
- normalization (spec: https://unicode.org/reports/tr15/): canonical combining classes, full
  canonical decompositions (NFD), full compatibility decompositions where they differ (NFKD), and
  the primary composites (canonical pairs not excluded from composition). Hangul syllables are
  algorithmic and not listed.

Encoding (decoded with ES/Regex/Unicode.lean's `decodeNats`/`decodeRanges`): lists of naturals as
base-64 digits; range lists as (gap, length - 1) pairs; sequence maps as (key delta, count,
values…); value maps as (key delta, value); composition triples as (first delta, second, composite).
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VERSION = "17.0.0"
ucd = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "third_party" / "ucd" / VERSION
OUT = ROOT / "ES" / "Unicode" / "TextData.lean"

ALPHA = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"


def enc_nat(n):
    groups = []
    while True:
        groups.append(n & 31)
        n >>= 5
        if n == 0:
            break
    groups.reverse()
    return "".join(ALPHA[g + 32] for g in groups[:-1]) + ALPHA[groups[-1]]


def enc_ranges(rs):
    out, prev = [], -1
    for a, b in rs:
        out.append(enc_nat(a - prev - 1))
        out.append(enc_nat(b - a))
        prev = b
    return "".join(out)


def enc_seqmap(m):
    out, prev = [], 0
    for k in sorted(m):
        v = m[k]
        out.append(enc_nat(k - prev))
        out.append(enc_nat(len(v)))
        out.extend(enc_nat(x) for x in v)
        prev = k
    return "".join(out)


def enc_valmap(m):
    out, prev = [], 0
    for k in sorted(m):
        out.append(enc_nat(k - prev))
        out.append(enc_nat(m[k]))
        prev = k
    return "".join(out)


def ranges_of(cps):
    out = []
    for c in sorted(cps):
        if out and c == out[-1][1] + 1:
            out[-1][1] = c
        else:
            out.append([c, c])
    return out


def read_lines(name):
    for line in (ucd / name).read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            yield [f.strip() for f in line.split(";")]


def expand_ranges(name, prop):
    cps = set()
    for f in read_lines(name):
        if f[1] != prop:
            continue
        r = f[0].split("..")
        lo = int(r[0], 16)
        hi = int(r[-1], 16)
        cps.update(range(lo, hi + 1))
    return cps


# --- UnicodeData ---------------------------------------------------------------------------------
upper, lower, ccc, decomp = {}, {}, {}, {}
first = None
for f in read_lines("UnicodeData.txt"):
    cp = int(f[0], 16)
    if f[1].endswith(", First>"):
        first = cp
        continue
    if f[1].endswith(", Last>"):
        cps = range(first, cp + 1)
    else:
        cps = [cp]
    for c in cps:
        if f[3] != "0":
            ccc[c] = int(f[3])
        if f[5]:
            parts = f[5].split()
            compat = parts[0].startswith("<")
            if compat:
                parts = parts[1:]
            decomp[c] = (compat, [int(x, 16) for x in parts])
        if f[12]:
            upper[c] = [int(f[12], 16)]
        if f[13]:
            lower[c] = [int(f[13], 16)]

for f in read_lines("SpecialCasing.txt"):
    if len(f) > 4 and f[4]:
        continue  # conditional (language- or context-sensitive)
    cp = int(f[0], 16)
    lo = [int(x, 16) for x in f[1].split()]
    up = [int(x, 16) for x in f[3].split()]
    lower[cp] = lo
    upper[cp] = up

lower = {k: v for k, v in lower.items() if v != [k]}
upper = {k: v for k, v in upper.items() if v != [k]}

cased = expand_ranges("DerivedCoreProperties.txt", "Cased")
case_ignorable = expand_ranges("DerivedCoreProperties.txt", "Case_Ignorable")
excluded = expand_ranges("DerivedNormalizationProps.txt", "Full_Composition_Exclusion")


def full(c, compat, depth=0):
    assert depth < 20
    d = decomp.get(c)
    if d is None or (d[0] and not compat):
        return [c]
    out = []
    for x in d[1]:
        out.extend(full(x, compat, depth + 1))
    return out


nfd = {}
nfkd = {}
for c in decomp:
    a = full(c, False)
    if a != [c]:
        nfd[c] = a
    b = full(c, True)
    if b != a:
        nfkd[c] = b

comps = []
for c, (compat, parts) in decomp.items():
    if compat or len(parts) != 2 or c in excluded:
        continue
    comps.append((parts[0], parts[1], c))
comps.sort()


def enc_comps(ts):
    out, prev = [], 0
    for a, b, c in ts:
        out.append(enc_nat(a - prev))
        out.append(enc_nat(b))
        out.append(enc_nat(c))
        prev = a
    return "".join(out)


fields = [
    ("lowerMap", "Full lowercase mappings (code point → code points), encoded sequence map.", enc_seqmap(lower)),
    ("upperMap", "Full uppercase mappings, encoded sequence map.", enc_seqmap(upper)),
    ("casedRanges", "The Cased property, encoded range list.", enc_ranges(ranges_of(cased))),
    ("caseIgnorableRanges", "The Case_Ignorable property, encoded range list.", enc_ranges(ranges_of(case_ignorable))),
    ("cccMap", "Canonical_Combining_Class (non-zero values), encoded value map.", enc_valmap(ccc)),
    ("nfdMap", "Full canonical decompositions (Hangul excluded), encoded sequence map.", enc_seqmap(nfd)),
    ("nfkdMap", "Full compatibility decompositions where they differ from the canonical ones, encoded sequence map.", enc_seqmap(nfkd)),
    ("compositions", "Primary composites: (first, second, composite) triples sorted by first, encoded.", enc_comps(comps)),
]

total = sum(len(x[2]) for x in fields)
lines = [
    "/-!",
    "# Unicode data for String case conversion and normalization (generated — never edit by hand)",
    "",
    f"Generated by `tools/gen_es_text.py` from the Unicode {VERSION} Character Database: full case",
    f"mappings ({len(lower)} lowercase, {len(upper)} uppercase; unconditional SpecialCasing.txt ones,",
    "else UnicodeData.txt's), the Cased and Case_Ignorable properties (for Final_Sigma),",
    f"canonical combining classes ({len(ccc)}), full decompositions ({len(nfd)} canonical, {len(nfkd)}",
    f"compatibility) and primary composites ({len(comps)}); {total} bytes of base-64 digits in all,",
    "decoded by `ES/Unicode/Text.lean`.",
    "",
    "spec: https://tc39.es/ecma262/#sec-string.prototype.tolowercase",
    "spec: https://tc39.es/ecma262/#sec-string.prototype.normalize",
    "-/",
    "",
    "namespace ES.Unicode.TextData",
    "",
]
for name, doc, val in fields:
    lines.append(f"/-- {doc} -/")
    lines.append(f'def {name} : String := "{val}"')
    lines.append("")
lines.append("end ES.Unicode.TextData")
OUT.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"wrote {OUT} ({total} bytes of data)")
