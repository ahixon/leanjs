import ES

/-!
# Host requests: an embedder stub (Zippy's docs/lean-engine.md)

Host built-ins `double(x)` (2x), `fail()` (throws "boom") and `note(s)` (records `s` in the embedder's own
state), called directly, from nested functions, inside `try`, from a generator, from a promise job, and in a
loop. `lake build es-host-test && .lake/build/bin/es-host-test`
-/

open ES

def hostDefs : Array BuiltinDef := #[⟨"host.double", hostFn "double"⟩, ⟨"host.fail", hostFn "fail"⟩,
  ⟨"host.note", hostFn "note"⟩]

def hostSetup : M Unit := do
  for (nm, len) in [("double", 1), ("fail", 0), ("note", 1)] do
    let f ← makeBuiltinFn s!"host.{nm}" len nm
    defGlobal nm (.obj f)

/-- The embedder: its state is the list of notes. -/
def answer : HostAnswer (Array String) := fun notes name _ args s =>
  match name, (args[0]? : Option Value) with
  | "double", some (Value.num x) => (notes, .normal (.num (Conv.addF x x)), s)
  | "fail", _ => (notes, .throw (.str "boom"), s)
  | "note", some (Value.str t) => (notes.push t.toString, .normal .undefined, s)
  | _, _ => (notes, .throw (.str s!"bad host call {name}"), s)

def cases : List (String × String × List String) := [
  ("direct", "double(21)", []),
  ("nested", "function g(y) { return double(y) * 10; } function f(x) { return g(x) + 1; } f(2)", []),
  ("throw caught", "function h() { try { fail(); } catch (e) { return 'caught ' + e; } } h()", []),
  ("throw uncaught", "function h() { fail(); return 1; } try { h(); } catch (e) { 'outer ' + e }", []),
  ("generator", "function* gen() { yield double(1); yield double(2); } let it = gen(); it.next().value + it.next().value", []),
  ("loop", "let s = 0; for (let i = 0; i < 100; i = i + 1) { s = s + double(i); } s", []),
  ("notes in order", "function a() { note('a'); b(); note('c'); } function b() { note('b'); } a(); 'done'", ["a", "b", "c"]),
  ("job", "Promise.resolve(5).then(v => note('job ' + double(v))); 'queued'", ["job 10"]),
  ("callback", "[1, 2, 3].map(x => double(x)).join(',')", [])]

def expected : List String := ["42", "41", "caught boom", "outer boom", "6", "9900", "done", "queued", "2,4,6"]

def main : IO UInt32 := do
  let mut failed := 0
  for ((name, src, notesExp), exp) in cases.zip expected do
    match newSession hostDefs hostSetup with
    | .error m => IO.println s!"FAIL {name}: session: {m}"; failed := failed + 1
    | .ok sess =>
      let (out, sess, notes) := sess.runScriptWith answer #[] src
      let got := match out with
        | .value v => match (sess.run (toStr v)).1 with
          | .ok (.ok t) => t.toString
          | _ => "(unprintable)"
        | .threw _ => "(threw)"
        | .halted m => s!"(halted: {m})"
      if got == exp && notes.toList == notesExp then IO.println s!"ok   {name}: {got}"
      else
        IO.println s!"FAIL {name}: got {got} notes {notes.toList}, expected {exp} notes {notesExp}"
        failed := failed + 1
  return if failed == 0 then 0 else 1
