import ES.Str
import ES.Regex.Syntax

/-!
# Regular expressions: compiling patterns and matching

spec: https://tc39.es/ecma262/#sec-regexp-regular-expression-objects

`compile` parses a pattern (`ES/Regex/Syntax.lean`: grammar, Annex B, early errors) and compiles
it (CompilePattern) into a program for a backtracking machine; `matchAt` runs it at one index
(the [[RegExpMatcher]] closure); `search` scans like RegExpBuiltinExec's loop.

## The machine

The matchers and continuations of 22.2.2 are compiled to instructions (`Inst`) over one array;
the machine keeps the MatchState (`pos`, the captures in `mem`), a stack of choice points, and a
trail: every write to `mem` while a choice point exists records the old value, and resuming a
choice point (after a ~failure~) undoes the writes made since, so each choice point resumes the
exact MatchState it was made in. The correspondence with the spec's closures:

- MatchTwoAlternatives: `split` (try the left alternative; the right one is a choice point).
- MatchSequence: instructions in order (reversed for ~backward~, inside lookbehinds).
- RepeatMatcher: `repStart`/`repLoop`/`repIter`/`repEnd` with two registers per quantifier (the
  iterations done, and the position the current iteration started at: the `matchState` its
  continuation `d` captured). `repLoop` is RepeatMatcher's steps 1 and 6-8 (the choice between
  another iteration and the continuation), `repIter` steps 2-5 (clearing the Atom's captures),
  `repEnd` the continuation `d` (the empty check, then RepeatMatcher again). A quantified single
  character test without captures (`a*`, `[^"]+?`) runs as `charLoop`, which matches the same
  iterations in the same order but makes one choice point for all of them.
- Lookarounds: `lookStart` makes a barrier choice point and `lookEnd` cuts back to it (the
  continuation `d` that returns `y`: no backtracking into the assertion); a barrier resumed by
  ~failure~ means the assertion's Disjunction failed.
- Capture groups: `open`/`close` (the continuation `d` of Atom :: `(` Disjunction `)` sets the
  capture when the group's Disjunction has matched).

The input is the String's code units; for Unicode patterns a character is a code point decoded
on the fly (StringToCodePoints's characters: a surrogate pair is one character; character indices
are converted to code unit indices, as GetStringIndex does), so no input is copied.
-/

namespace ES.Regex

/-- A character class test: ASCII bitmaps, the ranges, and whether it is inverted. -/
structure CClass where
  bits0 : UInt64 := 0
  bits1 : UInt64 := 0
  set : CharSet := #[]
  invert : Bool := false
  deriving Inhabited

namespace CClass
def ofSet (s : CharSet) (invert : Bool) : CClass := Id.run do
  let mut b0 : UInt64 := 0
  let mut b1 : UInt64 := 0
  for c in [0:128] do
    if s.contains c then
      if c < 64 then b0 := b0 ||| ((1 : UInt64) <<< c.toUInt64)
      else b1 := b1 ||| ((1 : UInt64) <<< (c - 64).toUInt64)
  return { bits0 := b0, bits1 := b1, set := s, invert }

@[inline] def test (k : CClass) (c : Nat) : Bool :=
  let m :=
    if c < 64 then (k.bits0 >>> c.toUInt64) &&& 1 == 1
    else if c < 128 then (k.bits1 >>> (c - 64).toUInt64) &&& 1 == 1
    else k.set.contains c
  m != k.invert
end CClass

/-- Machine instructions (see the module docstring). `back`: the matcher's direction is
~backward~. Characters and classes of `ic` matchers are already canonicalized. -/
inductive Inst where
  | fail
  | char (c : Nat) (ic back : Bool)
  | cls (k : Nat) (ic back : Bool)
  /-- Continue at `pc + 1`; on failure at `alt`. -/
  | split (alt : Nat)
  | jmp (t : Nat)
  | open_ (reg : Nat)
  | close (n reg : Nat) (back : Bool)
  | bol (ml : Bool)
  | eol (ml : Bool)
  | wordB (neg ic : Bool)
  | backref (groups : Array Nat) (ic back : Bool)
  | lookStart (reg : Nat) (neg : Bool) (endPc : Nat)
  | lookEnd (reg : Nat) (neg : Bool)
  | repStart (reg : Nat)
  | repLoop (reg min : Nat) (max : Option Nat) (greedy : Bool) (exit : Nat)
  | repIter (reg lo hi : Nat)
  | repEnd (reg min loop : Nat)
  /-- A quantified character test (the `char`/`cls` at `pc + 1`); continues at `pc + 2`. -/
  | charLoop (min : Nat) (max : Option Nat) (greedy : Bool)
  | succeed
  deriving Inhabited

/-- A compiled pattern: what `RegExpInitialize` stores in [[RegExpMatcher]] plus the facts the
built-ins need. -/
structure Program where
  source : JSStr := JSStr.empty
  flags : JSStr := JSStr.empty
  /-- The number of capturing groups (NcapturingParens). -/
  groupCount : Nat := 0
  /-- Each capture's group name (index 1..groupCount; index 0 unused), if named. -/
  groupNames : Array (Option JSStr) := #[]
  hasIndices : Bool := false
  global : Bool := false
  ignoreCase : Bool := false
  multiline : Bool := false
  dotAll : Bool := false
  unicode : Bool := false
  unicodeSets : Bool := false
  sticky : Bool := false
  insts : Array Inst := #[.fail]
  classes : Array CClass := #[]
  /-- Capture slots (2 per group, group 0's unused) followed by the registers. -/
  memSize : Nat := 0
  /-- The characters any match must start with (reading forward from its start), if known:
  `search` skips other positions. -/
  first : Option CClass := none
  deriving Inhabited

/-- Whether any capture group is named (RegExpBuiltinExec's "contains any GroupName"). -/
def Program.hasGroupNames (p : Program) : Bool := p.groupNames.any (·.isSome)

/-- A successful match: the end index and the captures (index 0 is the whole match), each a
code-unit range `[start, end)` or `none` when the group did not participate. -/
structure Match where
  endIndex : Nat
  captures : Array (Option (Nat × Nat))
  deriving Inhabited

/-! ## Compiling -/

structure CState where
  insts : Array Inst := #[]
  classes : Array CClass := #[]
  regs : Nat

abbrev CM := StateM CState

namespace Compile

def emit (i : Inst) : CM Nat :=
  modifyGet fun s => (s.insts.size, { s with insts := s.insts.push i })

def here : CM Nat := return (← get).insts.size

def patch (at_ : Nat) (i : Inst) : CM Unit :=
  modify fun s => { s with insts := s.insts.set! at_ i }

def newReg (n : Nat := 1) : CM Nat :=
  modifyGet fun s => (s.regs, { s with regs := s.regs + n })

def addClass (k : CClass) : CM Nat :=
  modifyGet fun s => (s.classes.size, { s with classes := s.classes.push k })

/-- Whether a node is a single character test (for `charLoop`). -/
def isCharTest : Node → Bool
  | .char .. | .set .. => true
  | _ => false

/-- CompileSubpattern / CompileAtom / CompileAssertion of the node `id` with the given direction
(`back`: ~backward~). `fuel` bounds the recursion: each call descends to a child, and the arena
is a tree, so the node count suffices.
spec: https://tc39.es/ecma262/#sec-compilesubpattern -/
def node (pat : Pattern) (unicode : Bool) (fuel : Nat) (id : Nat) (back : Bool) : CM Unit := do
  match fuel with
  | 0 => return
  | fuel + 1 =>
  match pat.nodes[id]! with
  | .empty => return
  | .char c ic =>
    -- CharacterSetMatcher with a one-element CharSet
    discard <| emit (.char (if ic then canonicalize unicode true c else c) ic back)
  | .set s inv ic =>
    -- CharacterSetMatcher: the CharSet's image under Canonicalize
    let k ← addClass (CClass.ofSet (if ic then canonImage unicode s else s) inv)
    discard <| emit (.cls k ic back)
  | .seq kids =>
    -- MatchSequence (~backward~: the right Term first)
    for k in (if back then kids.reverse else kids) do node pat unicode fuel k back
  | .alt kids =>
    -- MatchTwoAlternatives, nested to the right
    let mut jumps : Array Nat := #[]
    for i in [0:kids.size] do
      if i + 1 < kids.size then
        let sp ← emit (.split 0)
        node pat unicode fuel kids[i]! back
        jumps := jumps.push (← emit (.jmp 0))
        patch sp (.split (← here))
      else node pat unicode fuel kids[i]! back
    let e ← here
    for j in jumps do patch j (.jmp e)
  | .group idx body =>
    let r ← newReg
    discard <| emit (.open_ r)
    node pat unicode fuel body back
    discard <| emit (.close idx r back)
  | .look behind neg body =>
    let r ← newReg
    let st ← emit (.lookStart r neg 0)
    node pat unicode fuel body behind
    discard <| emit (.lookEnd r neg)
    patch st (.lookStart r neg (← here))
  | .quant body mn mx greedy pIdx pCount =>
    -- RepeatMatcher; step 1 with max = 0 is the continuation alone
    if mx == some 0 then return
    if isCharTest pat.nodes[body]! then
      discard <| emit (.charLoop mn mx greedy)
      node pat unicode fuel body back
    else
      let r ← newReg 2
      discard <| emit (.repStart r)
      let loop ← emit (.repLoop r mn mx greedy 0)
      discard <| emit (.repIter r (pIdx + 1) (pIdx + pCount + 1))
      node pat unicode fuel body back
      discard <| emit (.repEnd r mn loop)
      patch loop (.repLoop r mn mx greedy (← here))
  | .bol ml => discard <| emit (.bol ml)
  | .eol ml => discard <| emit (.eol ml)
  | .wordB neg ic => discard <| emit (.wordB neg ic)
  | .backref gs ic => discard <| emit (.backref gs ic back)
  | .namedRef name ic =>
    -- GroupSpecifiersThatMatch's group numbers
    let gs := (List.range pat.groupNames.size).toArray.filter fun i => pat.groupNames[i]! == some name
    discard <| emit (.backref gs ic back)

/-- Assertions: nodes that never move the position. -/
def isZeroWidth : Node → Bool
  | .bol _ | .eol _ | .wordB .. | .look .. | .empty => true
  | _ => false

/-- The characters a match of the node must read first (forward), if determined. -/
def firstSet (pat : Pattern) (maxChar : Nat) : Nat → Nat → Option CharSet
  | 0, _ => none
  | fuel + 1, id =>
    match pat.nodes[id]! with
    | .char c ic => if ic then none else some (CharSet.single c)
    | .set s inv ic => if ic then none else some (if inv then s.complement maxChar else s)
    | .seq kids =>
      -- assertions do not move the position: the first character is read after them
      match kids.find? (fun k => !isZeroWidth pat.nodes[k]!) with
      | some k => firstSet pat maxChar fuel k
      | none => none
    | .alt kids =>
      kids.foldl (fun acc k => acc.bind fun a => (firstSet pat maxChar fuel k).map a.union) (some #[])
    | .group _ body => firstSet pat maxChar fuel body
    | .quant body mn _ _ _ _ => if mn ≥ 1 then firstSet pat maxChar fuel body else none
    | _ => none

end Compile

/-- Parses RegExpInitialize's flags: `none` on a code unit other than d g i m s u v y, or a
repeated one.
spec: https://tc39.es/ecma262/#sec-regexpinitialize (steps 5-6) -/
def parseFlags (flags : JSStr) : Option (Array Bool) := Id.run do
  let names := "dgimsuvy".toList.toArray
  let mut seen := Array.replicate 8 false
  for i in [0:flags.length] do
    let u := (flags.get i).toNat
    match names.findIdx? (·.toNat == u) with
    | none => return none
    | some k =>
      if seen[k]! then return none
      seen := seen.set! k true
  return some seen

/-- Parses and compiles `pattern` with `flags` (RegExpInitialize's steps that can throw a
SyntaxError: invalid flags or an invalid pattern, with its early errors). `.error` carries the
SyntaxError's message (what is wrong, e.g. "Nothing to repeat"; callers add the pattern).
spec: https://tc39.es/ecma262/#sec-regexpinitialize
spec: https://tc39.es/ecma262/#sec-compilepattern -/
def compile (pattern flags : JSStr) : Except String Program := do
  -- 5-6.
  let some f := parseFlags flags | throw "Invalid regular expression flags"
  let (d, g, i, m, s, u, v, y) := (f[0]!, f[1]!, f[2]!, f[3]!, f[4]!, f[5]!, f[6]!, f[7]!)
  -- (ParsePattern step 1)
  if u && v then throw "Invalid regular expression flags"
  -- 10. patternText: code points for u/v, code units otherwise
  let src : Array Nat := Id.run do
    let mut out := Array.mkEmpty pattern.length
    let mut k := 0
    for _ in [0:pattern.length] do
      if k ≥ pattern.length then break
      if u || v then
        let (cp, n, _) := pattern.codePointAt k
        out := out.push cp
        k := k + n
      else
        out := out.push (pattern.get k).toNat
        k := k + 1
    return out
  -- 11-12. ParsePattern
  let pat ← parsePattern src u v i m s
  let unicode := u || v
  -- CompilePattern
  let capSlots := 2 * (pat.groupCount + 1)
  let ((), st) := (do
      Compile.node pat unicode (pat.nodes.size + 1) pat.root false
      discard <| Compile.emit .succeed).run { regs := capSlots }
  let maxChar := if unicode then 0x10FFFF else 0xFFFF
  return {
    source := pattern, flags, groupCount := pat.groupCount, groupNames := pat.groupNames,
    hasIndices := d, global := g, ignoreCase := i, multiline := m, dotAll := s, unicode := u,
    unicodeSets := v, sticky := y, insts := st.insts, classes := st.classes, memSize := st.regs,
    first := (Compile.firstSet pat maxChar (pat.nodes.size + 1) pat.root).map (CClass.ofSet · false) }

/-! ## Matching -/

/-- The resource limit of one match: machine steps (instructions, backtracks, and characters a
`charLoop` reads) before `matchAt` gives up with `.error`. Matching always terminates in the
spec, but backtracking can take exponential time; this bounds it (an engine limit, like a stack
overflow, not a spec semantics). -/
def defaultStepLimit : Nat := 200000000

/-- What one run of the matcher needs. -/
structure Ctx where
  prog : Program
  input : JSStr
  len : Nat
  unicode : Bool

namespace Machine

@[inline] def isHi (c : Nat) : Bool := 0xD800 ≤ c && c ≤ 0xDBFF
@[inline] def isLo (c : Nat) : Bool := 0xDC00 ≤ c && c ≤ 0xDFFF

@[inline] def unit (cx : Ctx) (p : Nat) : Nat := (cx.input.get p).toNat

/-- The character starting at `p < len` and its width in code units. -/
@[inline] def readF (cx : Ctx) (p : Nat) : Nat × Nat :=
  let c := unit cx p
  if cx.unicode && isHi c && p + 1 < cx.len then
    let d := unit cx (p + 1)
    if isLo d then ((c - 0xD800) * 0x400 + (d - 0xDC00) + 0x10000, 2) else (c, 1)
  else (c, 1)

/-- The character ending at `p > 0` and its width. -/
@[inline] def readB (cx : Ctx) (p : Nat) : Nat × Nat :=
  let c := unit cx (p - 1)
  if cx.unicode && isLo c && p ≥ 2 then
    let h := unit cx (p - 2)
    if isHi h then ((h - 0xD800) * 0x400 + (c - 0xDC00) + 0x10000, 2) else (c, 1)
  else (c, 1)

/-- A character test (`char`/`cls`) at `pos`: 1 + the position after the character if it
matches, 0 if not (no allocation in the machine's inner loop).
spec: https://tc39.es/ecma262/#sec-runtime-semantics-charactersetmatcher-abstract-operation (steps 2.a-2.k) -/
@[inline] def testAt (cx : Ctx) (i : Inst) (pos : Nat) : Nat :=
  match i with
  | .char c ic back =>
    if back then
      if pos == 0 then 0 else
      let (ch, w) := readB cx pos
      let ch := if ic then canonicalize cx.unicode true ch else ch
      if ch == c then pos - w + 1 else 0
    else
      if pos ≥ cx.len then 0 else
      let (ch, w) := readF cx pos
      let ch := if ic then canonicalize cx.unicode true ch else ch
      if ch == c then pos + w + 1 else 0
  | .cls k ic back =>
    let cls := cx.prog.classes[k]!
    if back then
      if pos == 0 then 0 else
      let (ch, w) := readB cx pos
      let ch := if ic then canonicalize cx.unicode true ch else ch
      if cls.test ch then pos - w + 1 else 0
    else
      if pos ≥ cx.len then 0 else
      let (ch, w) := readF cx pos
      let ch := if ic then canonicalize cx.unicode true ch else ch
      if cls.test ch then pos + w + 1 else 0
  | _ => 0

/-- IsWordChar(rer, input, e) for the code unit index `e` (word characters are BMP characters
that are not surrogates, so the code unit decides even for Unicode patterns).
spec: https://tc39.es/ecma262/#sec-runtime-semantics-iswordchar-abstract-operation -/
@[inline] def isWordAt (cx : Ctx) (ic : Bool) (e : Nat) (valid : Bool) : Bool :=
  if !valid || e ≥ cx.len then false else
  let c := unit cx e
  if c < 128 then basicWordChars.contains c
  else cx.unicode && ic && (c == 0x017F || c == 0x212A)

/-- BackreferenceMatcher's comparison: the position after matching the captured `[rs, re)` at
`pos` (in the direction), if it matches.
spec: https://tc39.es/ecma262/#sec-backreference-matcher (steps 2.f-2.k) -/
def backrefAt (cx : Ctx) (ic back : Bool) (rs re pos : Nat) : Option Nat := Id.run do
  let canon (c : Nat) : Nat := if ic then canonicalize cx.unicode true c else c
  -- the start of the compared input: `pos` forward, or as many characters before `pos` as the
  -- capture has (~backward~)
  let mut g := pos
  if back then
    let mut q := rs
    for _ in [0:re - rs] do
      if q ≥ re then break
      if g == 0 then return none
      q := q + (readF cx q).2
      g := g - (readB cx g).2
  let mut p := g
  let mut q := rs
  for _ in [0:re - rs] do
    if q ≥ re then break
    if p ≥ cx.len then return none
    let (a, wa) := readF cx q
    let (b, wb) := readF cx p
    if canon a != canon b then return none
    q := q + wa
    p := p + wb
  return some (if back then g else p)

/-- The machine's state besides the program counter: positions and registers in `mem`, the
choice points (6 slots each: kind, pc, pos, trail length, a, b), and the trail (slot, old value
pairs). -/
structure St where
  pos : Nat
  mem : Array Nat
  stack : Array Nat
  trail : Array Nat
  budget : Nat

/-- Writes a slot, recording the old value when a choice point could resume before it. -/
@[inline] def St.write (s : St) (slot v : Nat) : St :=
  let old := s.mem[slot]!
  if old == v then s
  else if s.stack.size == 0 then { s with mem := s.mem.set! slot v }
  else { s with mem := s.mem.set! slot v, trail := (s.trail.push slot).push old }

@[inline] def St.push (s : St) (kind pc pos a b : Nat) : St :=
  let tl := s.trail.size
  { s with stack := s.stack.push kind |>.push pc |>.push pos |>.push tl |>.push a |>.push b }

/-- Undoes the trail down to `len`. -/
def St.unwind (s : St) (len : Nat) : St :=
  let (mem, trail) := go s.mem s.trail ((s.trail.size - len) / 2)
  { s with mem, trail }
where
  go (mem trail : Array Nat) : Nat → Array Nat × Array Nat
    | 0 => (mem, trail)
    | k + 1 =>
      let n := trail.size
      let slot := trail[n - 2]!
      let old := trail[n - 1]!
      go (mem.set! slot old) trail.pop.pop k

/-- Drops choice points down to stack size `n`. -/
def St.cut (s : St) (n : Nat) : St := { s with stack := go s.stack (s.stack.size - n) }
where
  go (st : Array Nat) : Nat → Array Nat
    | 0 => st
    | k + 1 => go st.pop k

inductive Outcome where
  | ok (s : St)
  | fail (s : St)
  | limit

/-- What resuming a choice point leads to: no choice point left, a resumption at `pc`, or
continued failure (a positive lookaround's barrier; a lazy loop that cannot extend). -/
inductive Resume where
  | done (s : St)
  | at (pc : Nat) (s : St)
  | again (s : St)

/-- The step on ~failure~: resumes the newest choice point. -/
@[inline] def backtrack (cx : Ctx) (s : St) : Resume :=
  let n := s.stack.size
  if n == 0 then .done s else
  let kind := s.stack[n - 6]!
  let pc := s.stack[n - 5]!
  let pos := s.stack[n - 4]!
  let tl := s.stack[n - 3]!
  let a := s.stack[n - 2]!
  let b := s.stack[n - 1]!
  let s := { s with stack := s.stack.pop.pop.pop.pop.pop.pop }
  let s := (s.unwind tl)
  let s := { s with pos }
  match kind with
  | 0 => .at pc s
  | 1 =>
    -- a lookaround's Disjunction failed
    match cx.prog.insts[pc]! with
    | .lookStart _ true endPc => .at endPc s
    | _ => .again s
  | 2 =>
    -- greedy charLoop: one iteration fewer
    match cx.prog.insts[pc]!, cx.prog.insts[pc + 1]! with
    | .charLoop mn _ _, .char _ _ back | .charLoop mn _ _, .cls _ _ back =>
      let w :=
        if back then (if cx.unicode && pos + 2 ≤ b && isHi (unit cx pos) && isLo (unit cx (pos + 1)) then 2 else 1)
        else (if cx.unicode && pos ≥ b + 2 && isLo (unit cx (pos - 1)) && isHi (unit cx (pos - 2)) then 2 else 1)
      let pos' := if back then pos + w else pos - w
      let cnt := a - 1
      let s := if cnt > mn then s.push 2 pc pos' cnt b else s
      .at (pc + 2) { s with pos := pos' }
    | _, _ => .done s
  | _ =>
    -- lazy charLoop: one iteration more
    match cx.prog.insts[pc]! with
    | .charLoop _ mx _ =>
      match testAt cx cx.prog.insts[pc + 1]! pos with
      | 0 => .again s
      | r + 1 =>
        let pos' := r
        let cnt := a + 1
        let s := if mx.all (cnt < ·) then s.push 3 pc pos' cnt 0 else s
        .at (pc + 2) { s with pos := pos' }
    | _ => .done s

/-- A greedy `charLoop`'s iterations: how many characters from `p` pass the test (at most `max`),
and the position after them. `fuel`: each iteration reads a character, so the input's length
bounds them. -/
def scan (cx : Ctx) (test : Inst) (max : Option Nat) (cnt p : Nat) : Nat → Nat × Nat
  | 0 => (cnt, p)
  | fuel + 1 =>
    if max == some cnt then (cnt, p) else
    match testAt cx test p with
    | p' + 1 => scan cx test max (cnt + 1) p' fuel
    | 0 => (cnt, p)

/-- Runs the machine for at most `fuel` steps from `pc`; `failing`: a ~failure~ is being
propagated (resume the newest choice point). -/
def run (cx : Ctx) : Nat → Nat → Bool → St → Outcome
  | 0, _, _, _ => .limit
  | fuel + 1, pc, failing, s =>
    if s.budget == 0 then .limit else
    let s := { s with budget := s.budget - 1 }
    if failing then
      match backtrack cx s with
      | .done s' => .fail s'
      | .at pc' s' => run cx fuel pc' false s'
      | .again s' => run cx fuel pc true s'
    else
    match cx.prog.insts[pc]! with
    | .fail => run cx fuel pc true s
    | .succeed => .ok s
    | i@(.char ..) | i@(.cls ..) =>
      match testAt cx i s.pos with
      | p + 1 => run cx fuel (pc + 1) false { s with pos := p }
      | 0 => run cx fuel pc true s
    | .split alt => run cx fuel (pc + 1) false (s.push 0 alt s.pos 0 0)
    | .jmp t => run cx fuel t false s
    | .open_ r => run cx fuel (pc + 1) false (s.write r s.pos)
    | .close n r back =>
      -- Atom :: `(` Disjunction `)`'s continuation d: steps 1-7
      let x := s.mem[r]!
      let (a, b) := if back then (s.pos, x) else (x, s.pos)
      let s := (s.write (2 * n) (a + 1)).write (2 * n + 1) (b + 1)
      run cx fuel (pc + 1) false s
    | .bol ml =>
      -- spec: https://tc39.es/ecma262/#sec-compileassertion (`^`)
      if s.pos == 0 || (ml && isLineTerminator (unit cx (s.pos - 1))) then run cx fuel (pc + 1) false s
      else run cx fuel pc true s
    | .eol ml =>
      -- (`$`)
      if s.pos == cx.len || (ml && isLineTerminator (unit cx s.pos)) then run cx fuel (pc + 1) false s
      else run cx fuel pc true s
    | .wordB neg ic =>
      -- (`\b`, `\B`)
      let a := isWordAt cx ic (s.pos - 1) (s.pos > 0)
      let b := isWordAt cx ic s.pos true
      if (a != b) != neg then run cx fuel (pc + 1) false s else run cx fuel pc true s
    | .backref gs ic back =>
      -- BackreferenceMatcher
      let r := gs.foldl (fun acc g => if s.mem[2 * g + 1]! != 0 then some g else acc) none
      match r with
      | none => run cx fuel (pc + 1) false s
      | some g =>
        let rs := s.mem[2 * g]! - 1
        let re := s.mem[2 * g + 1]! - 1
        match backrefAt cx ic back rs re s.pos with
        | some p => run cx fuel (pc + 1) false { s with pos := p, budget := s.budget - min s.budget (re - rs) }
        | none => run cx fuel pc true s
    | .lookStart r _ _ =>
      let idx := s.stack.size
      let s := s.push 1 pc s.pos 0 0
      run cx fuel (pc + 1) false (s.write r idx)
    | .lookEnd r neg =>
      let idx := s.mem[r]!
      if neg then
        -- the Disjunction matched: the negative assertion fails, with the state before it
        let tl := s.stack[idx + 3]!
        let s := (s.cut idx).unwind tl
        run cx fuel pc true s
      else
        -- the Disjunction matched: keep its captures, return to the saved position
        let p := s.stack[idx + 2]!
        let s := s.cut idx
        run cx fuel (pc + 1) false { s with pos := p }
    | .repStart r => run cx fuel (pc + 1) false (s.write r 0)
    | .repLoop r mn mx greedy exit =>
      -- RepeatMatcher steps 1, 6-8 for min - k, max - k
      let k := s.mem[r]!
      if mx == some k then run cx fuel exit false s
      else if k < mn then run cx fuel (pc + 1) false s
      else if greedy then run cx fuel (pc + 1) false (s.push 0 exit s.pos 0 0)
      else run cx fuel exit false (s.push 0 (pc + 1) s.pos 0 0)
    | .repIter r lo hi =>
      -- RepeatMatcher steps 2-5: the iteration's start, its Atom's captures cleared
      let s := s.write (r + 1) s.pos
      let s := Id.run do
        let mut s := s
        for g in [lo:hi] do
          s := (s.write (2 * g) 0).write (2 * g + 1) 0
        return s
      run cx fuel (pc + 1) false s
    | .repEnd r mn loop =>
      -- the continuation d: step 2.b (empty check), then RepeatMatcher with min - 1, max - 1
      let k := s.mem[r]!
      if k ≥ mn && s.pos == s.mem[r + 1]! then run cx fuel pc true s
      else run cx fuel loop false (s.write r (k + 1))
    | .charLoop mn mx greedy =>
      let test := cx.prog.insts[pc + 1]!
      if greedy then
        let (cnt, p) := scan cx test mx 0 s.pos (cx.len + 1)
        let s := { s with budget := s.budget - min s.budget cnt }
        if cnt < mn then run cx fuel pc true s
        else
          let s := if cnt > mn then s.push 2 pc p cnt s.pos else s
          run cx fuel (pc + 2) false { s with pos := p }
      else
        let r := Id.run do
          let mut p := s.pos
          for _ in [0:mn] do
            match testAt cx test p with
            | p' + 1 => p := p'
            | 0 => return none
          return some p
        let s := { s with budget := s.budget - min s.budget mn }
        match r with
        | none => run cx fuel pc true s
        | some p =>
          let s := if mx.all (mn < ·) then s.push 3 pc p mn 0 else s
          run cx fuel (pc + 2) false { s with pos := p }

/-- The start of the character holding code unit `index` (RegExpBuiltinExec step 13.b's
inputIndex, as a code unit index): one unit back inside a surrogate pair of a Unicode pattern. -/
def charStart (cx : Ctx) (index : Nat) : Nat :=
  if cx.unicode && index > 0 && index < cx.len && isLo (unit cx index) && isHi (unit cx (index - 1))
  then index - 1 else index

/-- The matcher closure of CompilePattern at a code unit index (already a character start),
with the machine's arrays passed in (for reuse: `mem` all zero, `stack` and `trail`
empty) and returned after a failed run. -/
def exec' (cx : Ctx) (start limit : Nat) (s : St) : Except String (Option Match) × Option St :=
  let p := cx.prog
  match run cx limit 0 false { s with pos := start, budget := limit } with
  | .limit => (.error "RegExp too big: the match exceeded the engine's step limit", none)
  | .fail s =>
    -- (no choice point is left: the registers and the trail are reset)
    let s := Id.run do
      let mut mem := s.mem
      for k in [0:mem.size] do mem := mem.set! k 0
      let mut trail := s.trail
      for _ in [0:trail.size] do trail := trail.pop
      return { s with mem, trail }
    (.ok none, some s)
  | .ok s =>
    let caps := Id.run do
      let mut caps : Array (Option (Nat × Nat)) := #[some (start, s.pos)]
      for g in [1:p.groupCount + 1] do
        let a := s.mem[2 * g]!
        let b := s.mem[2 * g + 1]!
        caps := caps.push (if b == 0 then none else some (a - 1, b - 1))
      return caps
    (.ok (some { endIndex := s.pos, captures := caps }), none)

/-- Fresh machine arrays. -/
def St.fresh (p : Program) : St :=
  { pos := 0, mem := Array.replicate p.memSize 0, stack := Array.mkEmpty 96, trail := Array.mkEmpty 64, budget := 0 }

/-- The matcher closure of CompilePattern at a code unit index (already a character start).
spec: https://tc39.es/ecma262/#sec-compilepattern (steps 2.a-2.f) -/
def exec (cx : Ctx) (start limit : Nat) : Except String (Option Match) :=
  let s := St.fresh cx.prog
  (exec' cx start limit s).1

end Machine

/-- Runs the matcher at exactly `index` of `input` (RegExpBuiltinExec's step 11's matcher call;
the caller handles lastIndex, sticky, and advancing). `.error` is an engine limit (the match took
too many steps, `defaultStepLimit`). For a Unicode pattern an `index` inside a surrogate pair
starts the match at the pair (step 13.b's inputIndex); `captures[0]` then starts there too:
DEVIATION (docs/es.md, RegExp match start inside a surrogate pair): the spec's Match Record keeps
lastIndex as the start, V8 reports the pair's start (and so do we, so the start never exceeds the
end). -/
def matchAt (p : Program) (input : JSStr) (index : Nat) (limit : Nat := defaultStepLimit) :
    Except String (Option Match) :=
  let cx : Ctx := { prog := p, input, len := input.length, unicode := p.unicode || p.unicodeSets }
  if index > cx.len then .ok none
  else Machine.exec cx (Machine.charStart cx index) limit

/-- RegExpBuiltinExec's loop for a non-sticky RegExp: the first match at `fromIndex` or after,
trying the indices `AdvanceStringIndex` steps through (one code unit at a time for BMP patterns,
one code point for Unicode patterns). Equal to calling `matchAt` at each of those indices in turn;
positions whose first character cannot start a match are skipped. The step limit applies to each
index.
spec: https://tc39.es/ecma262/#sec-regexpbuiltinexec (step 13)
spec: https://tc39.es/ecma262/#sec-advancestringindex -/
def search (p : Program) (input : JSStr) (fromIndex : Nat) (limit : Nat := defaultStepLimit) :
    Except String (Option Match) := Id.run do
  let cx : Ctx := { prog := p, input, len := input.length, unicode := p.unicode || p.unicodeSets }
  let mut i := fromIndex
  let mut st := Machine.St.fresh p
  for _ in [0:cx.len + 2] do
    -- 13.a.
    if i > cx.len then return .ok none
    -- 13.b.
    let start := Machine.charStart cx i
    let skip := match p.first with
      | some k => start ≥ cx.len || !k.test (Machine.readF cx start).1
      | none => false
    if !skip then
      match Machine.exec' cx start limit st with
      | (.ok none, some st') => st := st'
      | (r, _) => return r
    -- 13.d.ii. AdvanceStringIndex
    i := if !cx.unicode || i + 1 ≥ cx.len then i + 1 else i + (input.codePointAt i).2.1
  return .ok none

end ES.Regex
