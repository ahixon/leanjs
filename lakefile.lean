import Lake
open Lake DSL

package «lean-js» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib LeanJS where
  srcDir := "."
  roots := #[`LeanJS]

lean_exe «lean-js» where
  root := `Main
  supportInterpreter := true
