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
  -- Recent macOS `dyld` rejects binaries produced by the linker bundled with
  -- Lean 4.17 ("__DATA_CONST segment missing SG_READ_ONLY flag"), so link
  -- with the system linker there.
  moreLinkArgs := if System.Platform.isOSX then #["--ld-path=/usr/bin/ld"] else #[]
