#!/usr/bin/env node
// Builds the RegExp test corpora for ESTests/Regex.lean from V8 (node), into third_party/regex-corpus/:
//
//   exec.txt    every RegExp exec call made by test262's RegExp/String-method tests (run in node with
//               RegExp.prototype.exec wrapped), with V8's results
//   fuzz.txt    random patterns and inputs (exec results, or that the pattern is a SyntaxError)
//   syntax.txt  regex literals of test262's parse-phase SyntaxError tests (must not compile) and of
//               the other literal tests (must compile)
//   props.txt   test262's generated property-escape tests: each regex and its matching code points
//
// usage: node ESTests/regex_corpus.js [fuzzCount]
// Line format (tab-separated; strings as concatenated 4-digit hex code units):
//   E pattern flags input lastIndex expected   expected: "null", "err", or captures
//                                              "s,e;s,e;-;…" (`-`: undefined), index 0 first
//   S pattern flags ok|err file
//   P pattern flags ranges file                ranges: "lo-hi,lo-hi,…" (hex code points)
//   Q pattern flags strings file               strings (v-flag properties): hex strings joined by ","
"use strict";
const fs = require("fs");
const path = require("path");
const vm = require("vm");

const ROOT = path.resolve(__dirname, "..");
const T262 = path.join(ROOT, "third_party", "test262");
const OUT = path.join(ROOT, "third_party", "regex-corpus");
fs.mkdirSync(OUT, { recursive: true });

const hex = (s) => {
  let out = "";
  for (let i = 0; i < s.length; i++) out += s.charCodeAt(i).toString(16).padStart(4, "0");
  return out;
};

function walk(dir, out = []) {
  if (!fs.existsSync(dir)) return out;
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, e.name);
    if (e.isDirectory()) walk(p, out);
    else if (e.name.endsWith(".js") && !e.name.includes("_FIXTURE")) out.push(p);
  }
  return out.sort();
}

function meta(src) {
  const m = src.match(/\/\*---([\s\S]*?)---\*\//);
  return m ? m[1] : "";
}

function capsOf(re, m) {
  // indices via the `d` flag on a copy run at the same lastIndex
  if (m === null) return "null";
  if (!m.indices) return null;
  return m.indices.map((r) => (r === undefined ? "-" : r[0] + "," + r[1])).join(";");
}

function execRecord(source, flags, input, lastIndex) {
  let re;
  try {
    re = new RegExp(source, flags.includes("d") ? flags : flags + "d");
  } catch (e) {
    return "err";
  }
  re.lastIndex = lastIndex;
  const m = RegExp.prototype.exec.call(re, input);
  return capsOf(re, m);
}

// --- exec records from test262 ---------------------------------------------------------------
function harvest() {
  const dirs = [
    "test/built-ins/RegExp",
    "test/built-ins/String/prototype/match",
    "test/built-ins/String/prototype/matchAll",
    "test/built-ins/String/prototype/replace",
    "test/built-ins/String/prototype/replaceAll",
    "test/built-ins/String/prototype/search",
    "test/built-ins/String/prototype/split",
    "test/annexB/built-ins/RegExp",
    "test/language/literals/regexp",
  ];
  const harness = {};
  const inc = (n) => (harness[n] ??= fs.readFileSync(path.join(T262, "harness", n), "utf8"));
  const lines = new Set();
  let files = 0;
  for (const d of dirs) {
    for (const f of walk(path.join(T262, d))) {
      if (f.includes("property-escapes/generated")) continue;
      const src = fs.readFileSync(f, "utf8");
      const md = meta(src);
      if (/negative:/.test(md) || /flags:.*(module|async)/.test(md)) continue;
      const includes = (md.match(/includes:\s*\[([^\]]*)\]/) || [, ""])[1].split(",").map((s) => s.trim()).filter(Boolean);
      const records = { n: 0 };
      const ctx = vm.createContext({ print() {}, console });
      const hook = `
        (function(){
          const origExec = RegExp.prototype.exec;
          const rec = globalThis.__rec;
          RegExp.prototype.exec = function(s) {
            const li = this.lastIndex;
            const str = String(s);
            const r = origExec.call(this, s);
            try { if (rec.n < 3000) { rec[rec.n] = { s: this.source, f: this.flags, i: str, l: typeof li === "number" ? li : 0 }; rec.n++; } } catch (e) {}
            return r;
          };
        })();`;
      ctx.__rec = records;
      let code = inc("assert.js") + "\n" + inc("sta.js") + "\n" + inc("compareArray.js") + "\n" + inc("propertyHelper.js") + "\n";
      for (const i of includes) {
        try { code += inc(i) + "\n"; } catch (e) {}
      }
      try {
        vm.runInContext(code + hook, ctx, { timeout: 5000 });
        vm.runInContext((/flags:.*onlyStrict/.test(md) ? '"use strict";\n' : "") + src, ctx, { timeout: 5000, filename: f });
      } catch (e) {
        // failed tests still contribute the calls they made
      }
      files++;
      for (let r = 0; r < records.n; r++) {
        const { s: source, f: flags, i: input, l: li } = records[r];
        if (typeof source !== "string" || typeof flags !== "string" || typeof input !== "string") continue;
        if (input.length > 100000) continue;
        const lastIndex = Number.isInteger(li) && li >= 0 && li <= 2 ** 31 ? li : 0;
        const exp = execRecord(source, flags, input, lastIndex);
        if (exp === null) continue;
        lines.add(["E", hex(source), flags, hex(input), lastIndex, exp].join("\t"));
      }
    }
  }
  fs.writeFileSync(path.join(OUT, "exec.txt"), [...lines].join("\n") + "\n");
  console.log(`exec.txt: ${lines.size} records from ${files} files`);
}

// --- regex literals: syntax tests ---------------------------------------------------------------
// The regex literals in a source text (a light tokenizer: skips strings, comments, template text).
function regexLiterals(src) {
  const out = [];
  let i = 0;
  let prevSignificant = "";
  const n = src.length;
  while (i < n) {
    const c = src[i];
    if (c === "/" && src[i + 1] === "/") { while (i < n && src[i] !== "\n") i++; continue; }
    if (c === "/" && src[i + 1] === "*") { const j = src.indexOf("*/", i + 2); i = j < 0 ? n : j + 2; continue; }
    if (c === '"' || c === "'" || c === "`") {
      const q = c; i++;
      while (i < n && src[i] !== q) { if (src[i] === "\\") i++; i++; }
      i++; prevSignificant = "x"; continue;
    }
    if (c === "/") {
      // a regex literal where an expression can start
      if (prevSignificant === "" || /[(,=:\[!&|?{};+\-*%<>~^]$/.test(prevSignificant) || /\b(return|typeof|case|do|else|in|of|new|delete|void|throw)$/.test(prevSignificant)) {
        let j = i + 1, inClass = false, ok = false;
        while (j < n && src[j] !== "\n") {
          const d = src[j];
          if (d === "\\") { j += 2; continue; }
          if (d === "[") inClass = true;
          else if (d === "]") inClass = false;
          else if (d === "/" && !inClass) { ok = true; break; }
          j++;
        }
        if (ok) {
          let k = j + 1;
          while (k < n && /[\p{ID_Continue}$]/u.test(src[k])) k++;
          out.push([src.slice(i + 1, j), src.slice(j + 1, k)]);
          i = k; prevSignificant = "x"; continue;
        }
      }
    }
    if (!/\s/.test(c)) {
      // track the previous token's end (identifier words kept whole)
      if (/[\w$]/.test(c)) {
        let k = i; while (k < n && /[\w$]/.test(src[k])) k++;
        prevSignificant = src.slice(i, k); i = k; continue;
      }
      prevSignificant = c;
    }
    i++;
  }
  return out;
}

function syntax() {
  const lines = [];
  const dirs = ["test/built-ins/RegExp", "test/language/literals/regexp", "test/annexB/built-ins/RegExp",
                "test/annexB/language/literals/regexp"];
  let neg = 0, pos = 0;
  for (const d of dirs) {
    for (const f of walk(path.join(T262, d))) {
      if (f.includes("property-escapes/generated") && !f.includes("negative")) continue;
      const src = fs.readFileSync(f, "utf8");
      const md = meta(src);
      const body = src.replace(/\/\*---[\s\S]*?---\*\//, "");
      const rel = path.relative(T262, f);
      if (/negative:\s*\n\s*phase:\s*parse\s*\n\s*type:\s*SyntaxError/.test(md)) {
        const after = body.split("$DONOTEVALUATE();")[1];
        if (after === undefined) continue;
        const lits = regexLiterals(after);
        // only tests whose error is in the (single) regex literal
        if (lits.length !== 1) continue;
        const [p, fl] = lits[0];
        // the literal must be a SyntaxError in V8 too (skip errors of the surrounding script)
        let v8err = false;
        try { new RegExp(p, fl); } catch (e) { v8err = true; }
        // (not a regex pattern error: a line terminator in the literal, etc.)
        if (!v8err) continue;
        lines.push(["S", hex(p), fl, "err", rel].join("\t"));
        neg++;
      } else if (!/negative:/.test(md)) {
        for (const [p, fl] of regexLiterals(body)) {
          let ok = true;
          try { new RegExp(p, fl); } catch (e) { ok = false; }
          if (!ok) continue; // tokenizer misfire
          lines.push(["S", hex(p), fl, "ok", rel].join("\t"));
          pos++;
        }
      }
    }
  }
  fs.writeFileSync(path.join(OUT, "syntax.txt"), lines.join("\n") + "\n");
  console.log(`syntax.txt: ${neg} SyntaxError literals, ${pos} valid literals`);
}

// --- property escapes ------------------------------------------------------------------------------
function props() {
  const lines = [];
  const dir = path.join(T262, "test/built-ins/RegExp/property-escapes/generated");
  for (const f of walk(dir)) {
    const src = fs.readFileSync(f, "utf8");
    const rel = path.relative(T262, f);
    if (f.includes("/strings/")) {
      if (f.includes("negative")) continue;
      const m = src.match(/regExp:\s*\/(.*)\/(\w*),/);
      const strsOf = (text) => [...text.matchAll(/^\s*"((?:[^"\\]|\\.)*)",?$/gm)].map((x) => vm.runInNewContext('"' + x[1] + '"'));
      const [matchPart, nonPart = ""] = src.split("nonMatchStrings:");
      lines.push(["Q", hex(m[1]), m[2], strsOf(matchPart).map(hex).join(",") + "!" + strsOf(nonPart).map(hex).join(","), rel].join("\t"));
      continue;
    }
    // evaluate the buildString calls' arguments
    const ctx = vm.createContext({});
    const matchArgs = src.match(/const matchSymbols = buildString\((\{[\s\S]*?\})\);/);
    const nonArgs = src.match(/const nonMatchSymbols = buildString\((\{[\s\S]*?\})\);/);
    const rangesOf = (a) => {
      if (!a) return [];
      const o = vm.runInContext("(" + a[1] + ")", ctx);
      const rs = o.loneCodePoints.map((c) => [c, c]).concat(o.ranges);
      return rs.sort((x, y) => x[0] - y[0]);
    };
    const enc = (rs) => rs.map(([a, b]) => a.toString(16) + "-" + b.toString(16)).join(",");
    const m = rangesOf(matchArgs), nm = rangesOf(nonArgs);
    for (const t of src.matchAll(/testPropertyEscapes\(\s*\/(.*)\/(\w*),\s*(matchSymbols|nonMatchSymbols)/g)) {
      lines.push(["P", hex(t[1]), t[2], enc(t[3] === "matchSymbols" ? m : nm), rel].join("\t"));
    }
  }
  fs.writeFileSync(path.join(OUT, "props.txt"), lines.join("\n") + "\n");
  console.log(`props.txt: ${lines.length} property regexes`);
}

// --- fuzzing -----------------------------------------------------------------------------------------
function fuzz(count) {
  let seed = 12345;
  const rnd = (n) => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed % n; };
  const pick = (a) => a[rnd(a.length)];
  const alphabet = ["a", "b", "c", "a", "b", "A", "B", "x", "0", "1", "_", " ", "\n", "-", "é", "É", "ſ", "K", "k", "K", "😀", "😁", "\ud83d", "\ude00", "ß", "İ", "ı", "Σ", "σ", "ς", " ", "à", "À", "İ"];
  const atoms = ["a", "b", "c", "a", "b", "A", ".", "\\d", "\\w", "\\W", "\\s", "\\S", "\\D", "\\b", "\\B", "^", "$", "[a-c]", "[^a]", "[\\w-]", "[a-]", "[^\\W]", "[^\\w]", "\\1", "\\2", "\\3", "\\k<n>", "é", "É", "ſ", "k", "K", "\\u212A", "😀", "\\ud83d", "\\ude00", "[😀a]", "\\u{1F600}", "[^😀]", "\\p{L}", "\\P{Ll}", "\\p{Lu}", "\\p{Ll}", "[\\p{Script=Greek}]", "\\p{Script_Extensions=Latin}", "\\x41", "\\cJ", "\\0", "\\10", "\\01", "\\8", "{", "}", "]", "[]", "[^]", "\\c", "\\c1", "[\\c1]", "[\\b]", "Σ", "σ", "ς", "ß", "\\q{ab|c}", "[\\q{ab|c|}a]", "[\\q{abc|ab}]", "[\\w--\\d]", "[\\w&&[a-f]]", "[[a-z]--[aeiou]]", "\\p{RGI_Emoji}", "[\\p{ASCII}--\\p{L}]", "[^[^a]]", "[\\d\\-z]", "[a-z--b]", "\\-", "\\/", "[\\-]", "(?<n>a)", "(?<n>b)", "(?<m>.)", "\\k<m>", "x{2,1}", "a{,2}", "{1}", "(?i)", "(?<=)", "\\u{0}", "\\uD83D\\uDE00", "[\\uD83D\\uDE00-\\uD83D\\uDE01]", "[\\s\\S]", "\\n", "\\r", "\\t", "\\xZZ", "\\u12", "\\p", "\\P{Any}", "\\p{Assigned}", "[^\\p{Lu}]", "İ", "ı", "\\u0130", "[à-é]"];
  const quants = ["", "", "", "", "", "", "", "", "", "", "*", "+", "?", "*?", "+?", "??", "{2}", "{1,3}", "{0,}", "{2,}?", "{0}", "{1,1}", "{0,2}?", "{3,}", "+", "{1,2}"];
  const gen = (depth) => {
    let s = "";
    const n = 1 + rnd(4);
    for (let i = 0; i < n; i++) {
      const r = rnd(12);
      let a;
      if (depth > 0 && r < 3) a = "(" + gen(depth - 1) + ")";
      else if (depth > 0 && r < 4) a = "(?:" + gen(depth - 1) + "|" + gen(depth - 1) + ")";
      else if (depth > 0 && r < 6) a = pick(["(?=", "(?!", "(?<=", "(?<!", "(?<n>", "(?<m>", "(?i:", "(?-i:", "(?m:", "(?s:", "(?is-m:", "(?<n>", "(?:"]) + gen(depth - 1) + (rnd(3) ? "" : "|" + gen(depth - 1)) + ")";
      else a = pick(atoms);
      s += a + pick(quants);
      if (rnd(10) === 0 && i + 1 < n) s += "|";
    }
    return s;
  };
  // inputs: random characters, or what a pattern's literal characters spell
  const literalsOf = (p) => p.replace(/\\[a-zA-Z]\{[^}]*\}|\\[a-zA-Z]|[\\^$.*+?()[\]{}|<>=!:-]/g, "");
  const lines = [];
  const syntaxLines = [];
  for (let k = 0; k < count; k++) {
    const p = gen(2 + rnd(2));
    const flags = pick(["", "", "i", "u", "iu", "v", "iv", "m", "s", "g", "y", "gu", "im", "su", "iy", "yu", "yv", "yi", "yiu", "dgimsuy".split("").filter(() => rnd(2)).join("")]);
    let ok = true;
    try { new RegExp(p, flags); } catch (e) { ok = false; }
    if (!ok) { lines.push(["E", hex(p), flags, "", 0, "err"].join("\t")); continue; }
    for (let t = 0; t < 3; t++) {
      let input = "";
      if (rnd(2)) {
        const lit = [...literalsOf(p)];
        const n = rnd(14);
        for (let i = 0; i < n; i++) input += lit.length && rnd(4) ? lit[rnd(lit.length)] : pick(alphabet);
      } else {
        const n = rnd(12);
        for (let i = 0; i < n; i++) input += pick(alphabet);
      }
      const li = flags.includes("y") || flags.includes("g") ? rnd(input.length + 2) : 0;
      const exp = execRecord(p, flags, input, li);
      if (exp === null) continue;
      lines.push(["E", hex(p), flags, hex(input), li, exp].join("\t"));
    }
  }
  // syntax: random strings over the pattern syntax's characters
  const synChars = ["(", ")", "[", "]", "{", "}", "?", "*", "+", "|", "^", "$", ".", "\\", "-", "&", "&&", "--", "<", ">", "=", "!", ":", ",", "a", "b", "k", "c", "d", "p", "P", "q", "u", "x", "0", "1", "2", "8", "i", "m", "s", "n", "L", "_", "/", "{1}", "{1,2}", "(?", "(?<", "\\k", "\\p{", "\\u{", "\\q{", "[^", "😀", "ſ", "~", "#", "%", "@", "`"];
  for (let k = 0; k < count; k++) {
    let p = "";
    const n = 1 + rnd(9);
    for (let i = 0; i < n; i++) p += pick(synChars);
    const flags = pick(["", "u", "v", "i", "iv", "uy"]);
    let ok = true;
    try { new RegExp(p, flags); } catch (e) { ok = false; }
    syntaxLines.push(["S", hex(p), flags, ok ? "ok" : "err", "fuzz"].join("\t"));
  }
  fs.writeFileSync(path.join(OUT, "fuzz.txt"), lines.join("\n") + "\n");
  fs.writeFileSync(path.join(OUT, "fuzz-syntax.txt"), syntaxLines.join("\n") + "\n");
  console.log(`fuzz.txt: ${lines.length} cases; fuzz-syntax.txt: ${syntaxLines.length}`);
}

// --- new RegExp(...) outcomes in test262 (syntax) --------------------------------------------------
function ctorSyntax() {
  const dirs = ["test/built-ins/RegExp", "test/annexB/built-ins/RegExp"];
  const harness = {};
  const inc = (n) => (harness[n] ??= fs.readFileSync(path.join(T262, "harness", n), "utf8"));
  const lines = new Set();
  for (const d of dirs) {
    for (const f of walk(path.join(T262, d))) {
      if (f.includes("property-escapes/generated")) continue;
      const src = fs.readFileSync(f, "utf8");
      const md = meta(src);
      if (/negative:/.test(md) || /flags:.*(module|async)/.test(md)) continue;
      const includes = (md.match(/includes:\s*\[([^\]]*)\]/) || [, ""])[1].split(",").map((s) => s.trim()).filter(Boolean);
      const rec = { n: 0 };
      const ctx = vm.createContext({ print() {}, __rec: rec });
      const hook = `
        (function(){
          const R = RegExp, rec = globalThis.__rec;
          const P = new Proxy(R, {
            construct(t, args, nt) {
              const p = args[0], f = args[1];
              let ps, fs;
              try { ps = (p === undefined ? "" : (typeof p === "object" && p !== null && p instanceof R) ? p.source : String(p)); fs = f === undefined ? ((p instanceof R) ? p.flags : "") : String(f); } catch (e) {}
              try { const r = Reflect.construct(t, args, nt); if (typeof ps === "string" && rec.n < 3000) rec[rec.n++] = { p: ps, f: fs, ok: true }; return r; }
              catch (e) { if (typeof ps === "string" && e instanceof SyntaxError && rec.n < 3000) rec[rec.n++] = { p: ps, f: fs, ok: false }; throw e; }
            }
          });
          globalThis.RegExp = P;
        })();`;
      let code = inc("assert.js") + "\n" + inc("sta.js") + "\n" + inc("compareArray.js") + "\n" + inc("propertyHelper.js") + "\n";
      for (const i of includes) { try { code += inc(i) + "\n"; } catch (e) {} }
      try {
        vm.runInContext(code + hook, ctx, { timeout: 5000 });
        vm.runInContext(src, ctx, { timeout: 5000, filename: f });
      } catch (e) {}
      const rel = path.relative(T262, f);
      for (let r = 0; r < rec.n; r++) {
        const { p, f: fl, ok } = rec[r];
        if (typeof p !== "string" || typeof fl !== "string") continue;
        lines.add(["S", hex(p), fl, ok ? "ok" : "err", rel].join("\t"));
      }
    }
  }
  fs.writeFileSync(path.join(OUT, "ctor-syntax.txt"), [...lines].join("\n") + "\n");
  console.log(`ctor-syntax.txt: ${lines.size} records`);
}

const what = process.argv[2] || "all";
if (what === "all" || what === "exec") harvest();
if (what === "all" || what === "syntax") syntax();
if (what === "all" || what === "props") props();
if (what === "all" || what === "fuzz") fuzz(Number(process.argv[3] || 20000));
if (what === "all" || what === "ctor") ctorSyntax();
