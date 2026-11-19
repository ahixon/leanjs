#!/usr/bin/env python3
"""Generate ES/Unicode/RegexData.lean: the Unicode data ECMAScript regular expressions use.

usage: tools/gen_regex_unicode.py [path/to/ucd]   (default third_party/ucd/17.0.0; downloaded there
       first if missing — the Unicode version test262's property-escape tests expect, see the
       "Unicode vX" line of test/built-ins/RegExp/property-escapes/generated/*.js)
source: https://www.unicode.org/Public/17.0.0/ucd/ and https://www.unicode.org/Public/17.0.0/emoji/

What it writes (spec: https://tc39.es/ecma262/#sec-runtime-semantics-unicodematchproperty-p):
- property value aliases of General_Category and Script (PropertyValueAliases.txt), and the binary
  properties of table-binary-unicode-properties with their aliases;
- code point sets as range lists: every General_Category value (incl. the groups LC, L, M, N, P,
  S, Z, C), every Script and Script_Extensions value, every binary property;
- the properties of strings (table-binary-unicode-properties-of-strings: emoji-sequences.txt,
  emoji-zwj-sequences.txt) as sorted lists of code point sequences (single code points as ranges);
- simple case folding (CaseFolding.txt statuses C and S: Canonicalize for u/v patterns) and the
  non-unicode Canonicalize's toUppercase table (BMP code units whose full uppercase mapping is one
  code unit, without mappings from non-ASCII to ASCII).

Encoding (decoded by ES/Regex/Unicode.lean): a list of naturals as base-64 digits
(`A-Za-z0-9+/` = 0..63); each number is big-endian groups of 5 bits, every group but the last
offset by 32. Range lists are (gap from the previous range's end + 1, length - 1) pairs; mapping
tables are (key delta, zigzag(value - key)) pairs.
"""
import re
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VERSION = "17.0.0"
ucd = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "third_party" / "ucd" / VERSION
OUT = ROOT / "ES" / "Unicode" / "RegexData.lean"

FILES = {
    "UnicodeData.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/UnicodeData.txt",
    "Scripts.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/Scripts.txt",
    "ScriptExtensions.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/ScriptExtensions.txt",
    "PropertyValueAliases.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/PropertyValueAliases.txt",
    "PropertyAliases.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/PropertyAliases.txt",
    "DerivedCoreProperties.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/DerivedCoreProperties.txt",
    "PropList.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/PropList.txt",
    "CaseFolding.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/CaseFolding.txt",
    "SpecialCasing.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/SpecialCasing.txt",
    "DerivedNormalizationProps.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/DerivedNormalizationProps.txt",
    "DerivedBinaryProperties.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/extracted/DerivedBinaryProperties.txt",
    "DerivedGeneralCategory.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/extracted/DerivedGeneralCategory.txt",
    "emoji-data.txt": f"https://www.unicode.org/Public/{VERSION}/ucd/emoji/emoji-data.txt",
    "emoji-sequences.txt": f"https://www.unicode.org/Public/{VERSION}/emoji/emoji-sequences.txt",
    "emoji-zwj-sequences.txt": f"https://www.unicode.org/Public/{VERSION}/emoji/emoji-zwj-sequences.txt",
}
ucd.mkdir(parents=True, exist_ok=True)
for name, url in FILES.items():
    if not (ucd / name).exists():
        print("fetching", url)
        urllib.request.urlretrieve(url, ucd / name)


def lines(name):
    for line in (ucd / name).read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            yield [f.strip() for f in line.split(";")]


def cprange(s):
    if ".." in s:
        a, b = s.split("..")
        return int(a, 16), int(b, 16)
    return int(s, 16), int(s, 16)


def to_ranges(cps):
    out = []
    for c in sorted(set(cps)):
        if out and out[-1][1] + 1 == c:
            out[-1][1] = c
        else:
            out.append([c, c])
    return [tuple(r) for r in out]


def ranges_of_sets(rs):
    """Normalize a list of (lo, hi) into sorted disjoint ranges."""
    rs = sorted(rs)
    out = []
    for a, b in rs:
        if out and a <= out[-1][1] + 1:
            out[-1][1] = max(out[-1][1], b)
        else:
            out.append([a, b])
    return [tuple(r) for r in out]


def complement(rs):
    out, prev = [], 0
    for a, b in rs:
        if a > prev:
            out.append((prev, a - 1))
        prev = b + 1
    if prev <= 0x10FFFF:
        out.append((prev, 0x10FFFF))
    return out


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


def enc_map(pairs):
    out, prev = [], 0
    for k, v in sorted(pairs):
        d = v - k
        out.append(enc_nat(k - prev))
        out.append(enc_nat(2 * d if d >= 0 else -2 * d - 1))
        prev = k
    return "".join(out)


# --- General_Category -------------------------------------------------------------------------
gc_of = {}
for f in lines("DerivedGeneralCategory.txt"):
    a, b = cprange(f[0])
    gc_of.setdefault(f[1], []).append((a, b))

gc_alias = {}   # every spelling -> canonical long name
gc_short = {}   # long name -> short
for f in lines("PropertyValueAliases.txt"):
    if f[0] == "gc":
        short, long_ = f[1], f[2]
        gc_short[long_] = short
        for s in f[1:]:
            gc_alias[s] = long_
GROUPS = {"LC": ["Lu", "Ll", "Lt"], "L": ["Lu", "Ll", "Lt", "Lm", "Lo"], "M": ["Mn", "Mc", "Me"],
          "N": ["Nd", "Nl", "No"], "P": ["Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po"],
          "S": ["Sm", "Sc", "Sk", "So"], "Z": ["Zs", "Zl", "Zp"], "C": ["Cc", "Cf", "Cs", "Co", "Cn"]}
gc_sets = {}
for long_, short in gc_short.items():
    parts = GROUPS.get(short, [short])
    gc_sets[long_] = ranges_of_sets([r for p in parts for r in gc_of.get(p, [])])

# --- Script / Script_Extensions ---------------------------------------------------------------
sc_alias, sc_long_of_short = {}, {}
for f in lines("PropertyValueAliases.txt"):
    if f[0] == "sc":
        short, long_ = f[1], f[2]
        sc_long_of_short[short] = long_
        for s in f[1:]:
            sc_alias[s] = long_
sc_map = {}
for f in lines("Scripts.txt"):
    a, b = cprange(f[0])
    sc_map.setdefault(f[1], []).append((a, b))
listed = ranges_of_sets([r for rs in sc_map.values() for r in rs])
sc_map["Unknown"] = complement(listed)
sc_of_cp = {}
for name, rs in sc_map.items():
    for a, b in rs:
        for c in range(a, b + 1):
            sc_of_cp[c] = name
scx_of_cp = {}
for f in lines("ScriptExtensions.txt"):
    a, b = cprange(f[0])
    names = [sc_long_of_short[s] for s in f[1].split()]
    for c in range(a, b + 1):
        scx_of_cp[c] = names
sc_sets, scx_sets = {}, {}
for long_ in set(sc_alias.values()):
    sc_sets[long_] = ranges_of_sets(sc_map.get(long_, []))
    cps = [c for c, n in sc_of_cp.items() if n == long_ and c not in scx_of_cp]
    cps += [c for c, ns in scx_of_cp.items() if long_ in ns]
    scx_sets[long_] = to_ranges(cps)

# --- binary properties -------------------------------------------------------------------------
BINARY = [("ASCII", []), ("ASCII_Hex_Digit", ["AHex"]), ("Alphabetic", ["Alpha"]), ("Any", []),
          ("Assigned", []), ("Bidi_Control", ["Bidi_C"]), ("Bidi_Mirrored", ["Bidi_M"]),
          ("Case_Ignorable", ["CI"]), ("Cased", []), ("Changes_When_Casefolded", ["CWCF"]),
          ("Changes_When_Casemapped", ["CWCM"]), ("Changes_When_Lowercased", ["CWL"]),
          ("Changes_When_NFKC_Casefolded", ["CWKCF"]), ("Changes_When_Titlecased", ["CWT"]),
          ("Changes_When_Uppercased", ["CWU"]), ("Dash", []), ("Default_Ignorable_Code_Point", ["DI"]),
          ("Deprecated", ["Dep"]), ("Diacritic", ["Dia"]), ("Emoji", []), ("Emoji_Component", ["EComp"]),
          ("Emoji_Modifier", ["EMod"]), ("Emoji_Modifier_Base", ["EBase"]),
          ("Emoji_Presentation", ["EPres"]), ("Extended_Pictographic", ["ExtPict"]), ("Extender", ["Ext"]),
          ("Grapheme_Base", ["Gr_Base"]), ("Grapheme_Extend", ["Gr_Ext"]), ("Hex_Digit", ["Hex"]),
          ("IDS_Binary_Operator", ["IDSB"]), ("IDS_Trinary_Operator", ["IDST"]), ("ID_Continue", ["IDC"]),
          ("ID_Start", ["IDS"]), ("Ideographic", ["Ideo"]), ("Join_Control", ["Join_C"]),
          ("Logical_Order_Exception", ["LOE"]), ("Lowercase", ["Lower"]), ("Math", []),
          ("Noncharacter_Code_Point", ["NChar"]), ("Pattern_Syntax", ["Pat_Syn"]),
          ("Pattern_White_Space", ["Pat_WS"]), ("Quotation_Mark", ["QMark"]), ("Radical", []),
          ("Regional_Indicator", ["RI"]), ("Sentence_Terminal", ["STerm"]), ("Soft_Dotted", ["SD"]),
          ("Terminal_Punctuation", ["Term"]), ("Unified_Ideograph", ["UIdeo"]), ("Uppercase", ["Upper"]),
          ("Variation_Selector", ["VS"]), ("White_Space", ["space"]), ("XID_Continue", ["XIDC"]),
          ("XID_Start", ["XIDS"])]
bin_raw = {}
for name in ["PropList.txt", "DerivedCoreProperties.txt", "DerivedNormalizationProps.txt",
             "DerivedBinaryProperties.txt", "emoji-data.txt"]:
    for f in lines(name):
        if len(f) == 2:   # binary properties have no value field
            a, b = cprange(f[0])
            bin_raw.setdefault(f[1], []).append((a, b))
bin_sets = {}
for name, _ in BINARY:
    if name == "Any":
        rs = [(0, 0x10FFFF)]
    elif name == "ASCII":
        rs = [(0, 0x7F)]
    elif name == "Assigned":
        rs = complement(gc_sets["Unassigned"])
    else:
        rs = bin_raw[name]
    bin_sets[name] = ranges_of_sets(rs)

# --- properties of strings ---------------------------------------------------------------------
STRPROPS = ["Basic_Emoji", "Emoji_Keycap_Sequence", "RGI_Emoji_Modifier_Sequence",
            "RGI_Emoji_Flag_Sequence", "RGI_Emoji_Tag_Sequence", "RGI_Emoji_ZWJ_Sequence", "RGI_Emoji"]
str_singles = {p: [] for p in STRPROPS}
str_seqs = {p: set() for p in STRPROPS}
for name in ["emoji-sequences.txt", "emoji-zwj-sequences.txt"]:
    for f in lines(name):
        prop = f[1]
        cps = f[0].split()
        targets = [prop, "RGI_Emoji"]
        if len(cps) == 1:
            a, b = cprange(cps[0])
            for t in targets:
                str_singles[t].append((a, b))
        else:
            seq = tuple(int(c, 16) for c in cps)
            for t in targets:
                str_seqs[t].add(seq)

# --- case mappings -----------------------------------------------------------------------------
scf = []
for f in lines("CaseFolding.txt"):
    if f[1] in ("C", "S"):
        scf.append((int(f[0], 16), int(f[2], 16)))
upper_simple = {}
first = None
for line in (ucd / "UnicodeData.txt").read_text(encoding="utf-8").splitlines():
    f = line.split(";")
    if f[12]:
        upper_simple[int(f[0], 16)] = [int(f[12], 16)]
for f in lines("SpecialCasing.txt"):
    # code; lower; title; upper; (condition_list;)?
    if len(f) >= 5 and f[4]:
        continue  # conditional mappings are not part of the default toUppercase
    upper_simple[int(f[0], 16)] = [int(x, 16) for x in f[3].split()]
upper = []
for c, m in upper_simple.items():
    if c > 0xFFFF or len(m) != 1 or m[0] > 0xFFFF or m[0] == c:
        continue
    if c >= 128 and m[0] < 128:
        continue
    upper.append((c, m[0]))


# --- output -------------------------------------------------------------------------------------
def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def alias_str(d):
    return ";" + ";".join(f"{k}={v}" for k, v in sorted(d.items())) + ";"


tables = []
for k, v in sorted(gc_sets.items()):
    tables.append(("gc=" + k, enc_ranges(v)))
for k, v in sorted(sc_sets.items()):
    tables.append(("sc=" + k, enc_ranges(v)))
for k, v in sorted(scx_sets.items()):
    tables.append(("scx=" + k, enc_ranges(v)))
for k, v in sorted(bin_sets.items()):
    tables.append(("bin=" + k, enc_ranges(v)))
str_tables = []
for p in STRPROPS:
    seqs = sorted(str_seqs[p])
    str_tables.append((p, enc_ranges(ranges_of_sets(str_singles[p])),
                       ",".join(" ".join("%X" % c for c in s) for s in seqs)))

bin_alias = {}
for name, aliases in BINARY:
    bin_alias[name] = name
    for a in aliases:
        bin_alias[a] = name

total = sum(len(t[1]) for t in tables) + sum(len(t[1]) + len(t[2]) for t in str_tables)
out = []
out.append(f"""/-!
# Unicode data for regular expressions (generated — never edit by hand)

Generated by `tools/gen_regex_unicode.py` from the Unicode {VERSION} Character Database (the version
test262's property-escape tests expect): {len(gc_sets)} General_Category values, {len(sc_sets)} Script and
Script_Extensions values, {len(bin_sets)} binary properties, {len(STRPROPS)} properties of strings, simple
case folding ({len(scf)} mappings) and the non-unicode Canonicalize's uppercase table ({len(upper)}).
Range lists and mappings are encoded as base-64 digit strings ({total} bytes in all); see the
generator's docstring and `ES/Regex/Unicode.lean`, which decodes them.

spec: https://tc39.es/ecma262/#sec-runtime-semantics-unicodematchproperty-p
spec: https://tc39.es/ecma262/#sec-runtime-semantics-canonicalize-ch
-/

namespace ES.Unicode.RegexData

/-- General_Category value aliases: `;alias=Canonical_Name;` entries. -/
def gcAliases : String := {lean_str(alias_str(gc_alias))}

/-- Script value aliases (also Script_Extensions'): `;alias=Canonical_Name;` entries. -/
def scAliases : String := {lean_str(alias_str(sc_alias))}

/-- The binary properties of table-binary-unicode-properties: `;alias=Canonical_Name;` entries. -/
def binAliases : String := {lean_str(alias_str(bin_alias))}

/-- The properties of strings (table-binary-unicode-properties-of-strings), `;Name;` entries. -/
def strProps : String := {lean_str(";" + ";".join(STRPROPS) + ";")}

/-- Simple case folding (CaseFolding.txt, statuses C and S), encoded mapping. -/
def scf : String := {lean_str(enc_map(scf))}

/-- toUppercase for the non-unicode Canonicalize (single BMP code unit results, none from
non-ASCII to ASCII), encoded mapping. -/
def upper : String := {lean_str(enc_map(upper))}

/-- Code point sets by key (`gc=Long_Name`, `sc=Long_Name`, `scx=Long_Name`, `bin=Name`), sorted
by key, encoded range lists. -/
def tables : Array (String × String) := #[""")
out.append(",\n".join(f"  ({lean_str(k)}, {lean_str(v)})" for k, v in tables))
out.append("""]

/-- Properties of strings: name, the single code points (encoded range list), and the longer
strings (hex code points separated by spaces, strings by commas). -/
def strTables : Array (String × String × String) := #[""")
out.append(",\n".join(f"  ({lean_str(p)}, {lean_str(a)}, {lean_str(b)})" for p, a, b in str_tables))
out.append("""]

end ES.Unicode.RegexData
""")
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text("\n".join(out), encoding="utf-8")
print(f"wrote {OUT} ({OUT.stat().st_size} bytes; {len(tables)} tables)")
