import Proofs.AddGen
open ES
example : #[1,2].foldl (· + ·) 0 = 3 := by rfl
example : #[1,2].foldl (· + ·) 0 = 3 := by decide
example : (AddGen.add_func.params.foldl (fun acc (p : Param) => match p with | .mk t _ _ => acc ++ boundNames t) #[]) = #["a", "b"] := by decide
example : (#[JSStr.ofString "a", JSStr.ofString "b"]).contains "arguments" = false := by decide
