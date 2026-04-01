import Lake
open Lake DSL

package "BigBangTheorem" where
  version := v!"0.1.0"
  keywords := #["math", "lean", "lorentzian-geometry"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "e960b84129b3caf423ecf0ea7409a8758a47012c"

@[default_target]
lean_lib «BigBangTheorem» where
