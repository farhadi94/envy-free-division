import Lake
open Lake DSL

package «envy-free-research» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

require «fixed-point-theorems» from git
  "https://github.com/harfe/fixed-point-theorems-lean4.git" @ "93a3eed3364281a9dbf9652bb52356a8db65057c"

@[default_target]
lean_lib EnvyFreeResearch
