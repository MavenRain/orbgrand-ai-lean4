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

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "c290b55c6ec09dd4a2afce6d695b90c6d8ec16fb"

require «kan-tactics» from ".." / "kan-tactics"

-- `doc-gen4` is pulled in only under `lake -Kenv=dev`, so `lake build`
-- in the default mode stays free of the documentation toolchain.  The
-- documentation GitHub Actions workflow passes `-Kenv=dev` explicitly.
meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
