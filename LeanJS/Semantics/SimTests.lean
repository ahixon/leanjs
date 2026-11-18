/-
  Tests for the verified core.

  1. Non-vacuity: the end-to-end theorems are instantiated on concrete
     programs with concrete evaluation derivations, showing that their
     hypotheses are satisfiable (a simulation theorem whose premises can never
     hold would be worthless).
  2. The executable translators compute the expected outputs (checked by the
     kernel with `rfl`/`decide`, or by `#guard`, which fails the build).
  3. Programs outside the core are rejected rather than mistranslated.
-/
import LeanJS.Semantics.SimCompose
import LeanJS.JS.Parser
import LeanJS.JS.Emit
import LeanJS.Lean.Emit

namespace LeanJS.Semantics.Tests

open LeanJS.JS
open LeanJS.IR
open LeanJS.Semantics
open LeanJS.Trans.Core

/-! ## 1. Non-vacuity -/


/-- `((x) => x)("hi")` -/
def jsIdApp : JS.Expr :=
  .call (.arrowFunction [pid "x"] (.expr (.ident "x")) false) [.literal (.string "hi")]

theorem jsIdApp_eval (st : Store) :
    JSEvalExpr .nil st jsIdApp (.val (.string "hi") st) :=
  JSSem.call_ok (JSSem.arrow rfl) (JSSem.args_cons_ok (JSSem.literal rfl) JSSem.args_nil)
    (JSSem.apply_expr_body (JSSem.ident rfl))

def jsIdApp_ir : IRExpr := .app (.lam none (anyParams ["x"]) [] (.var "x")) [.lit (.string "hi")]

theorem jsIdApp_toIR : JSToIRExpr jsIdApp jsIdApp_ir :=
  .call (.arrow_expr rfl .ident) (.cons .str .nil)

/-- The verified translator produces exactly this IR (checked by the kernel) -/
example : Res.out (jsExpr jsIdApp) = .ok jsIdApp_ir := by rfl

def jsIdApp_back : JS.Expr :=
  .call (.arrowFunction [pid "x"] (.expr (.ident "x")) false) [.literal (.string "hi")]

theorem jsIdApp_fromIR : IRToJSExpr jsIdApp_ir jsIdApp_back :=
  .app (.lam_expr .var) (.cons .str .nil)

/-- End-to-end: the round-tripped program provably evaluates to `"hi"`. -/
theorem jsIdApp_roundtrip (st : Store) :
    JSEvalExpr .nil st jsIdApp_back (.val (.string "hi") st) :=
  js_roundtrip_expr_prim jsIdApp_toIR jsIdApp_fromIR (jsIdApp_eval st) .string

/-- JS program `function f(x) { return x; } f("hi");` -/
def jsProg : JS.Program :=
  [.funcDecl "f" [pid "x"] [.return_ (some (.ident "x"))] false false,
   .expr (.call (.ident "f") [.literal (.string "hi")])]

theorem jsProg_eval (st : Store) : JSEvalStmts .nil st jsProg (.val .undefined st) :=
  JSSem.stmts_funcDecl rfl
    (JSSem.stmts_stmt_ok rfl
      (JSSem.stmt_expr
        (JSSem.call_ok (JSSem.ident rfl) (JSSem.args_cons_ok (JSSem.literal rfl) JSSem.args_nil)
          (JSSem.apply_block_body
            (JSSem.stmts_stmt_signal rfl (JSSem.stmt_return_some (JSSem.ident rfl)) trivial))))
      JSSem.stmts_nil)

def jsProg_ir : IRExpr :=
  .«let» "f" .any (.lam (some "f") (anyParams ["x"]) [] (.var "x"))
    (.app (.var "f") [.lit (.string "hi")])

def jsProg_back : JS.Program :=
  [.funcDecl "f" [pid "x"] [.return_ (some (.ident "x"))] false false,
   .expr (.call (.ident "f") [.literal (.string "hi")])]

theorem jsProg_toIR : JSToIRStmts jsProg jsProg_ir :=
  .funcDecl rfl (.ret .ident) (.last rfl (.expr (.call .ident (.cons .str .nil))))

theorem jsProg_fromIR : IRToJSStmts .discard jsProg_ir jsProg_back :=
  .funcDecl (.expr_tail .var) (.expr_discard (.app .var (.cons .str .nil)))

/-- End-to-end: the round-tripped program provably completes normally. -/
theorem jsProg_roundtrip (st : Store) : ∃ v', JSEvalStmts .nil st jsProg_back (.val v' st) :=
  js_roundtrip_program_completes jsProg_toIR jsProg_fromIR (jsProg_eval st)

-- …and it is exactly what the executable translator produces.
#guard JS.Emit.emitProgram ((jsRoundtrip jsProg).toOption.getD []) ==
  JS.Emit.emitProgram jsProg_back

/-- Lean `(fun x => x) "hi"` -/
def leanIdApp : LeanJS.Lean.LeanExpr :=
  .app (.lam [⟨"x", none⟩] (.ident "x")) (.lit (.string "hi"))

theorem leanIdApp_eval (st : Store) :
    LeanEvalExpr .nil st leanIdApp (.val (.string "hi") st) :=
  LeanSem.app_ok LeanSem.lam_one LeanSem.lit (LeanSem.apply_closure (LeanSem.ident rfl))

theorem leanIdApp_toIR :
    LeanToIRExpr leanIdApp (.app (.lam none [("x", .any)] [] (.var "x")) [.lit (.string "hi")]) :=
  .app (.lam_one .ident) .lit

theorem leanIdApp_toJS :
    JSEvalExpr .nil Store.empty
      (.call (.arrowFunction [pid "x"] (.expr (.ident "x")) false) [.literal (.string "hi")])
      (.val (.string "hi") Store.empty) :=
  lean_to_js_expr_prim leanIdApp_toIR (.app (.lam_expr .var) (.cons .str .nil))
    (leanIdApp_eval _) .string

/-- Lean round trip: `(fun x => x) "hi"` comes back unchanged and still
    provably evaluates to `"hi"`. -/
theorem leanIdApp_roundtrip :
    LeanEvalExpr .nil Store.empty leanIdApp (.val (.string "hi") Store.empty) :=
  lean_roundtrip_expr_prim leanIdApp_toIR (.app (.lam .var) .str) (leanIdApp_eval _) .string

#guard LeanJS.Lean.Emit.emitLeanExpr ((leanRoundtrip leanIdApp).toOption.getD .unit) ==
  LeanJS.Lean.Emit.emitLeanExpr leanIdApp

/-! ## 2–3. Executable translators (through the real parser and emitter) -/

def jsRoundtripSrc (src : String) : String :=
  match JS.Parser.parseProgram src with
  | .error e => s!"parse error: {e}"
  | .ok p =>
    match jsRoundtrip p with
    | .ok p' => JS.Emit.emitProgram p'
    | .error e => s!"rejected: {e}"

def isRejected (s : String) : Bool := s.startsWith "rejected:"

-- Accepted, and the output is stable under a second round trip
#guard !isRejected (jsRoundtripSrc "const add = (a, b) => a + b;\nconst r = add(1, 2);")
#guard let once := jsRoundtripSrc "const add = (a, b) => a + b;\nconst r = add(1, 2);"
       jsRoundtripSrc once == once
#guard let once := jsRoundtripSrc "function f(x) { if (x > 0) { return 1; } return 2; }\nf(3);"
       !isRejected once && jsRoundtripSrc once == once

-- Rejected: outside the verified core
#guard isRejected (jsRoundtripSrc "let x = 1; x = 2;")            -- assignment
#guard isRejected (jsRoundtripSrc "while (true) {}")              -- loop
#guard isRejected (jsRoundtripSrc "var x = 1;")                   -- var
#guard isRejected (jsRoundtripSrc "const o = {a: 1}; o.a;")       -- member access (JS→IR)
#guard isRejected (jsRoundtripSrc "const t = `x${1}`;")           -- template literal
#guard isRejected (jsRoundtripSrc "const f = ({a}) => a;")        -- destructuring parameter

end LeanJS.Semantics.Tests
