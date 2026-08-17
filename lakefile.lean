/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package json where
  leanOptions := #[⟨`warningAsError, true⟩]

@[default_target]
lean_lib Json

-- Tests live in a subproject so that nothing test-only appears in the dependency
-- graph a consumer resolves.
@[test_driver]
script tests do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  child.wait
