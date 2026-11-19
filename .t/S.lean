import ES
open ES
example : (JSStr.ofString "a" == JSStr.ofString "arguments") = false := by decide
example : (JSStr.ofString "a" == JSStr.ofString "a") = true := by decide
