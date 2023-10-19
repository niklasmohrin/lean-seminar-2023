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
lean_lib LeanSeminar where
  moreLeanArgs := moreLeanArgs

-- Last commit with Lean 4.1.0 in their `lean-toolchain` file
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"bf1ceb82960fe37c5f22a2b07d26ca12f27716ba"
