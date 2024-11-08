import Lake
open Lake DSL

package «Coins» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require batteries from git
  "https://github.com/leanprover-community/batteries.git"

@[default_target]
lean_lib «Coins» where
