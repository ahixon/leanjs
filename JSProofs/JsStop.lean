import JSProofs.JsTactic

/-!
# `js` that stops at given property reads (zippy docs/react-proofs.md)

`js_until ["k", …] [facts]` runs `js`'s steps but leaves every goal whose computation is a read `obj.k` of one of
the keys: reads of accessor properties (the DOM's attributes on the Lean engine), which `wp_getMemberAcc` and a
hypothesis about the getter handle instead of `js`'s own-data-property rule.
-/

open Lean Elab Tactic Meta

namespace Logic

/-- Whether the goal is `WP … (obj.k) …` for one of the keys. -/
def isStopRead (t : Expr) (ks : List String) : MetaM Bool := do
  let t := (← instantiateMVars t).consumeMData
  unless t.isAppOf ``Logic.WP do return false
  let args := t.getAppArgs
  if args.size < 5 then return false
  let x := args[args.size - 3]!.consumeMData
  unless x.isAppOf ``ES.Sem.getValue do return false
  let ref := x.getAppArgs[0]!
  let s := toString (← ppExpr ref)
  return ks.any fun k => (s.splitOn s!"\"{k}\"").length > 1

syntax "js_step_unless" "[" str,* "]" "[" Lean.Parser.Tactic.simpArg,* "]" : tactic
elab_rules : tactic
  | `(tactic| js_step_unless [$ks,*] [$xs,*]) => do
    let keys := ks.getElems.toList.map (·.getString)
    if ← isStopRead (← getMainTarget) keys then throwError "js_step_unless: a stop read"
    let ys : Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
      `Lean.Parser.Tactic.simpLemma] "," := ⟨xs.elemsAndSeps⟩
    evalTactic (← `(tactic| first | js_go | js_norm [*, $ys,*] | js_split))

macro "js_until" "[" ks:str,* "]" "[" xs:Lean.Parser.Tactic.simpArg,* "]" : tactic => do
  let ys : Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨xs.elemsAndSeps⟩
  `(tactic| repeat' (js_step_unless [$ks,*] [$ys,*]))

end Logic
