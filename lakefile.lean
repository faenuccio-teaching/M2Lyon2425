import Lake
open Lake DSL

package "M2Lyon2425" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "d684d596bcf8fbb114320776b80a1dbfce0a0786"

@[default_target]
lean_lib «M2Lyon2425» where
  -- add any library configuration options here
