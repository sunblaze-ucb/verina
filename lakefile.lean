import Lake
open Lake DSL

package «llm4verification» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require batteries from git "https://github.com/leanprover-community/batteries.git" @ "v4.18.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.18.0"

require plausible from git "https://github.com/leanprover-community/plausible.git" @ "v4.18.0"

-- require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "7b8651b39629159540430f83208fd812c6e8a0bc"

@[default_target]
lean_lib «Llm4verification» where
  -- add any library configuration options here
