import Lake
open Lake DSL

-- Mathlib supplies the tactics the level hints refer to (use, nth_rewrite,
-- tauto, contrapose, apply at). Pinned to the tag matching lean-toolchain so
-- `lake exe cache get` can serve prebuilt oleans.
require "leanprover-community" / mathlib @ git "v4.35.0"

package «nng-local» where
  leanOptions := #[
    -- Upstream NNG4 settings: auto-named hypotheses stay usable, as the hints
    -- assume, and let values stay visible in the goal view.
    ⟨`tactic.hygienic, false⟩,
    ⟨`pp.showLetValues, true⟩,
    ⟨`linter.all, false⟩]

@[default_target]
lean_lib NngLocal
