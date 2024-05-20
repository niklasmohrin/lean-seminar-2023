import Lake
open Lake DSL

def moreLeanArgs := #[
  "-Dpp.unicode.fun=true" -- pretty-prints `fun a ↦ b`
]

def moreServerArgs := moreLeanArgs

package LeanSeminar where
  moreLeanArgs := moreLeanArgs
  moreServerArgs := moreServerArgs

@[default_target]
lean_lib FlowEquivalentForest where
  moreLeanArgs := moreLeanArgs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.7.0"
