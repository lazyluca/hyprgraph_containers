import Lake
open Lake DSL

package "hyprgraph_containers" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.34.1"

@[default_target]
lean_lib «CamposSamotij» where
  -- add any library configuration options here
