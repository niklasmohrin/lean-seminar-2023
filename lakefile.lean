import Lake
open Lake DSL

package FlowEquivalentForest where
  leanOptions := #[ ⟨`pp.unicode.fun, true⟩ ]

@[default_target]
lean_lib FlowEquivalentForest

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.7.0"
