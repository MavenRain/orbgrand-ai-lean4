import OrbgrandAi.Section00
import OrbgrandAi.Section02
import OrbgrandAi.Section03
import OrbgrandAi.Section04
import OrbgrandAi.Section06

/-!
# OrbgrandAi

Lean 4 formalization of the paper

> Ken R. Duffy, Moritz Grundei, Jane A. Millward, Muralidhar Rangaswamy,
> Muriel Medard.  *Decoding in the presence of ISI without
> interleaving - ORBGRAND-AI.*  arXiv:2510.14939 (May 2026).

The paper develops a soft-input maximum-likelihood-style decoder
called ORBGRAND-AI that exploits, rather than equalises away, the
statistical correlation that an inter-symbol-interference (ISI)
channel imparts on additive noise.  The headline mathematical
contributions are:

1. A closed-form expression for the differential entropy rate of
   first-order and second-order Gauss-Markov noise, with an explicit
   determinant formula for the auto-covariance matrix.
2. An upper bound on the Shannon capacity of an additive
   second-order Gauss-Markov channel via the Verdu-Han lim-inf
   information rate and Hadamard's inequality.
3. The GRAND family of code-book-agnostic decoders, with a soft
   variant ORBGRAND-AI that factorises the posterior across
   small symbol neighbourhoods under an "approximate independence"
   assumption.

The Lean library mirrors the paper's section structure:

* `OrbgrandAi.Section00` -- shared probability layer: AWGN noise measure
  on `EuclideanSpace ℝ (Fin n_s)` and the `bler` operator used by the
  Section IV / VI.B probabilistic statements.  Not a paper section;
  promoted to its own module so the Mathlib measure-theory imports
  are paid exactly once.
* `OrbgrandAi.Section02` -- ISI channel models (Section II of the paper).
* `OrbgrandAi.Section03` -- entropy rates, Yule-Walker, capacity bound (Section III).
* `OrbgrandAi.Section04` -- GRAND, ORBGRAND, ORBGRAND-AI algorithm (Section IV).
* `OrbgrandAi.Section06` -- robustness under imperfect CSI / quantisation (Section VI).

## Conventions

* All tactic proofs use exclusively `kan-tactics`.  Standard Mathlib
  tactics (`simp`, `rw`, `exact`, `linarith`, ...) do not appear in
  any `by ...` block in this library.  Term-mode proofs that happen
  to involve names like `rfl` as values are permitted.
* No exceptions: definitions that can fail return `Option` or
  `Except`.  There is no `panic!`, `unreachable!`, or `throwError`.
* The library is structured as a reusable Lake dependency.  Downstream
  projects can `require OrbgrandAi from git ...` and import the top
  module `OrbgrandAi` to bring the full public surface in scope.
-/
