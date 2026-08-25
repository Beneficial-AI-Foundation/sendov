import Lake
open Lake DSL

-- Pinned to the 4.34 release line branch until the stable v4.34.0 branch
-- advances past v4.33.0 (see log.md); switch back to a tag when it does.
require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint"@"chore/start-lean-4-34-release-line"

-- sendov comes last: lake gives precedence to later requires, so shared
-- transitive dependencies (proofwidgets, plausible) resolve to the revisions
-- pinned by sendov/mathlib, keeping `lake exe cache get` hashes valid.
require sendov from ".."

package SendovBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib SendovBlueprint where
