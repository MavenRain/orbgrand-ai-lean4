import Lake
-- Lake configuration for orbgrand-ai-lean4.
--
-- Formalization of "Decoding in the presence of ISI without
-- interleaving - ORBGRAND-AI" by K. R. Duffy, M. Grundei,
-- J. A. Millward, M. Rangaswamy, M. Medard (arXiv:2510.14939).
--
-- Depends on:
--   * Mathlib4 -- complex numbers, matrices, determinants, Gaussian
--     measure theory, differential entropy, lim-inf / lim-sup,
--     analysis of log / exp.
--   * kan-tactics -- proof tactic library (local sibling directory).
--
-- autoImplicit is disabled project-wide to avoid accidental
-- free-variable introduction.
open Lake DSL

package OrbgrandAi where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib OrbgrandAi where
  srcDir := "."

require «kan-tactics» from ".." / "kan-tactics"

-- `doc-gen4` is pinned to `v4.30.0-rc1` rather than `main`:
-- `doc-gen4@main` bumps the Lean toolchain to `v4.30.0-rc2`, which is
-- incompatible with our Mathlib commit (`c290b55c`) which uses
-- `v4.30.0-rc1`.  Pinning by tag keeps doc-gen4 in lockstep with
-- Mathlib's toolchain.
--
-- The require is unconditional: an experiment with
-- `meta if get_config? env = some "dev" then require ... ` showed
-- that the conditional did not activate under `lake -Kenv=dev update`
-- on this Lake version, so we always pull doc-gen4 to keep the
-- documentation pipeline working.  The default `lake build` does not
-- invoke any doc-gen4 facet, so the unconditional require costs a
-- one-time fetch but no extra build work.
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.30.0-rc1"

-- `require mathlib` must come LAST so that Mathlib's pinned versions
-- of transitive deps (plausible, UnicodeBasic, leansqlite, ...) win
-- over doc-gen4's older pins.  Otherwise `lake exe cache get` computes
-- the wrong cache hashes and the Mathlib cache fails to load.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "c290b55c6ec09dd4a2afce6d695b90c6d8ec16fb"
