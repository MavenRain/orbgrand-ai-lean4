import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section02.RFView
import OrbgrandAi.Section03.GaussMarkov
import KanTactics

/-!
# Section VI.B.  AR(2) approximation of the RFView channel

Formalizes the second-order autoregressive (AR(2)) approximation of
the RFView channel from Section VI.B of the paper.

## Model

For each sounding signal `k'`, the matched-filter output `z''^{6, k'}`
is modelled as an AR(2) process:

  z'_{j', k'} = phi_1 * z_{j' - 1, k'}
              + phi_2 * z_{j' - 2, k'}
              + epsilon_{j', k'},     for j' >= 3,

with initial conditions `z''_{1, k'} = z_{1, k'}` and
`z''_{2, k'} = z_{2, k'}`.  The coefficients `phi_1, phi_2` are
fit by least squares per sounding signal:

  [phi_1_hat, phi_2_hat]^T
    = ( (z^{4 x 2}_{k'})^H * z^{4 x 2}_{k'} )^{-1}
       * (z^{4 x 2}_{k'})^H * z^4_{k'},

where `z^{4 x 2}_{k'}` is the regressor matrix
`[ [z''_{1, k'}, z''_{2, k'}],
   [z''_{2, k'}, z''_{3, k'}],
   ...
   [z''_{4, k'}, z''_{5, k'}] ]`
and `z^4_{k'} = [z''_{3, k'}, ..., z''_{6, k'}]^T` is the target.

## What we formalize

This file defines:

* The AR(2) recurrence with explicit initial conditions.
* The regressor matrix `regressorMatrix4x2 z` and target
  `regressorTarget4 z` (as opaque signatures whose Fin-index
  bookkeeping is deferred).
* The least-squares fit `ar2LeastSquaresFit z`.
* The approximation-error bound (placeholder).

The paper notes that the AR(1) approximation diverges too quickly
to be useful; only AR(2) tracks the matched-filter output well
enough to recover BLER performance close to perfect-CSI ORBGRAND-AI.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section06

open OrbgrandAi.Section02

/-! ## AR(2) recurrence -/

/-- Given two complex initial conditions `z1, z2` and AR(2)
    coefficients `phi_1, phi_2`, generate the AR(2) sequence

      `ar2 phi_1 phi_2 z_1 z_2` is the function `Nat -> Complex`
      with values

        `0 |-> z_1`,
        `1 |-> z_2`,
        `(n + 2) |-> phi_1 * (n + 1)-th value + phi_2 * n-th value`.

    The innovation noise `epsilon_j` is set to zero here; the noisy
    extension is handled at the level of `gaussMarkov2` in
    Section III. -/
def ar2
    (phi1 phi2 : Complex) (z1 z2 : Complex) : Nat -> Complex
  | 0      => z1
  | 1      => z2
  | (n + 2) =>
      phi1 * ar2 phi1 phi2 z1 z2 (n + 1) + phi2 * ar2 phi1 phi2 z1 z2 n

/-! ### Base-case lemmas for `ar2` -/

/-- `ar2` at index 0 returns the first initial condition. -/
theorem ar2_zero (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 0 = z1 := rfl

/-- `ar2` at index 1 returns the second initial condition. -/
theorem ar2_one (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 1 = z2 := rfl

/-- The AR(2) recurrence step: index `n + 2` is `phi_1` times the
    `(n + 1)`-th value plus `phi_2` times the `n`-th. -/
theorem ar2_succ_succ (phi1 phi2 z1 z2 : Complex) (n : Nat) :
    ar2 phi1 phi2 z1 z2 (n + 2)
      = phi1 * ar2 phi1 phi2 z1 z2 (n + 1)
        + phi2 * ar2 phi1 phi2 z1 z2 n := rfl

/-- Closed-form value at index 2: `phi_1 * z_2 + phi_2 * z_1`. -/
theorem ar2_two (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 2 = phi1 * z2 + phi2 * z1 := rfl

/-- Closed-form value at index 3:
    `phi_1 * (phi_1 * z_2 + phi_2 * z_1) + phi_2 * z_2`. -/
theorem ar2_three (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 3
      = phi1 * (phi1 * z2 + phi2 * z1) + phi2 * z2 := rfl

/-- Closed-form value at index 4: second recurrence step. -/
theorem ar2_four (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 4
      = phi1 * (phi1 * (phi1 * z2 + phi2 * z1) + phi2 * z2)
        + phi2 * (phi1 * z2 + phi2 * z1) := rfl

/-- Recurrence step at index 5: `phi_1 * ar2 4 + phi_2 * ar2 3`.
    Direct `rfl` via `ar2_succ_succ` at `n = 3`.  Extends the
    `ar2_two`/`_three`/`_four` named-form series. -/
theorem ar2_five (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 5
      = phi1 * ar2 phi1 phi2 z1 z2 4
        + phi2 * ar2 phi1 phi2 z1 z2 3 := rfl

/-- Recurrence step at index 6: `phi_1 * ar2 5 + phi_2 * ar2 4`.
    Same `rfl` pattern, extending the named-form series. -/
theorem ar2_six (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 6
      = phi1 * ar2 phi1 phi2 z1 z2 5
        + phi2 * ar2 phi1 phi2 z1 z2 4 := rfl

/-- Recurrence step at index 7: `phi_1 * ar2 6 + phi_2 * ar2 5`.
    Pattern-match arm `(5 + 2)` reduces definitionally to the RHS. -/
theorem ar2_seven (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 7
      = phi1 * ar2 phi1 phi2 z1 z2 6
        + phi2 * ar2 phi1 phi2 z1 z2 5 := rfl

/-- Recurrence step at index 8: `phi_1 * ar2 7 + phi_2 * ar2 6`.
    Pattern-match arm `(6 + 2)` reduces definitionally to the RHS. -/
theorem ar2_eight (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 8
      = phi1 * ar2 phi1 phi2 z1 z2 7
        + phi2 * ar2 phi1 phi2 z1 z2 6 := rfl

/-- Recurrence step at index 9: `phi_1 * ar2 8 + phi_2 * ar2 7`.
    Pattern-match arm `(7 + 2)` reduces definitionally to the RHS. -/
theorem ar2_nine (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 9
      = phi1 * ar2 phi1 phi2 z1 z2 8
        + phi2 * ar2 phi1 phi2 z1 z2 7 := rfl

/-- Recurrence step at index 10: `phi_1 * ar2 9 + phi_2 * ar2 8`.
    Pattern-match arm `(8 + 2)` reduces definitionally to the RHS. -/
theorem ar2_ten (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 10
      = phi1 * ar2 phi1 phi2 z1 z2 9
        + phi2 * ar2 phi1 phi2 z1 z2 8 := rfl

/-- Recurrence step at index 11: `phi_1 * ar2 10 + phi_2 * ar2 9`.
    Pattern-match arm `(9 + 2)` reduces definitionally to the RHS. -/
theorem ar2_eleven (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 11
      = phi1 * ar2 phi1 phi2 z1 z2 10
        + phi2 * ar2 phi1 phi2 z1 z2 9 := rfl

/-- Recurrence step at index 12: `phi_1 * ar2 11 + phi_2 * ar2 10`.
    Pattern-match arm `(10 + 2)` reduces definitionally to the RHS. -/
theorem ar2_twelve (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 12
      = phi1 * ar2 phi1 phi2 z1 z2 11
        + phi2 * ar2 phi1 phi2 z1 z2 10 := rfl

/-- Recurrence step at index 13: `phi_1 * ar2 12 + phi_2 * ar2 11`.
    Pattern-match arm `(11 + 2)` reduces definitionally to the RHS. -/
theorem ar2_thirteen (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 13
      = phi1 * ar2 phi1 phi2 z1 z2 12
        + phi2 * ar2 phi1 phi2 z1 z2 11 := rfl

/-- Recurrence step at index 14: `phi_1 * ar2 13 + phi_2 * ar2 12`.
    Pattern-match arm `(12 + 2)` reduces definitionally to the RHS. -/
theorem ar2_fourteen (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 14
      = phi1 * ar2 phi1 phi2 z1 z2 13
        + phi2 * ar2 phi1 phi2 z1 z2 12 := rfl

/-- Recurrence step at index 15: `phi_1 * ar2 14 + phi_2 * ar2 13`.
    Pattern-match arm `(13 + 2)` reduces definitionally to the RHS. -/
theorem ar2_fifteen (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 15
      = phi1 * ar2 phi1 phi2 z1 z2 14
        + phi2 * ar2 phi1 phi2 z1 z2 13 := rfl

/-- Recurrence step at index 16: `phi_1 * ar2 15 + phi_2 * ar2 14`.
    Pattern-match arm `(14 + 2)` reduces definitionally to the RHS. -/
theorem ar2_sixteen (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 16
      = phi1 * ar2 phi1 phi2 z1 z2 15
        + phi2 * ar2 phi1 phi2 z1 z2 14 := rfl

/-- Recurrence step at index 17: `phi_1 * ar2 16 + phi_2 * ar2 15`.
    Pattern-match arm `(15 + 2)` reduces definitionally to the RHS. -/
theorem ar2_seventeen (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 17
      = phi1 * ar2 phi1 phi2 z1 z2 16
        + phi2 * ar2 phi1 phi2 z1 z2 15 := rfl

/-- Recurrence step at index 18: `phi_1 * ar2 17 + phi_2 * ar2 16`.
    Pattern-match arm `(16 + 2)` reduces definitionally to the RHS. -/
theorem ar2_eighteen (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 18
      = phi1 * ar2 phi1 phi2 z1 z2 17
        + phi2 * ar2 phi1 phi2 z1 z2 16 := rfl

/-- Recurrence step at index 19: `phi_1 * ar2 18 + phi_2 * ar2 17`.
    Pattern-match arm `(17 + 2)` reduces definitionally to the RHS. -/
theorem ar2_nineteen (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 19
      = phi1 * ar2 phi1 phi2 z1 z2 18
        + phi2 * ar2 phi1 phi2 z1 z2 17 := rfl

/-- Recurrence step at index 20: `phi_1 * ar2 19 + phi_2 * ar2 18`.
    Pattern-match arm `(18 + 2)` reduces definitionally to the RHS. -/
theorem ar2_twenty (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 20
      = phi1 * ar2 phi1 phi2 z1 z2 19
        + phi2 * ar2 phi1 phi2 z1 z2 18 := rfl

/-- Recurrence step at index 21: `phi_1 * ar2 20 + phi_2 * ar2 19`.
    Pattern-match arm `(19 + 2)` reduces definitionally to the RHS. -/
theorem ar2_twenty_one (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 21
      = phi1 * ar2 phi1 phi2 z1 z2 20
        + phi2 * ar2 phi1 phi2 z1 z2 19 := rfl

/-- Recurrence step at index 22: `phi_1 * ar2 21 + phi_2 * ar2 20`.
    Pattern-match arm `(20 + 2)` reduces definitionally to the RHS. -/
theorem ar2_twenty_two (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 22
      = phi1 * ar2 phi1 phi2 z1 z2 21
        + phi2 * ar2 phi1 phi2 z1 z2 20 := rfl

/-- Recurrence step at index 23: `phi_1 * ar2 22 + phi_2 * ar2 21`.
    Pattern-match arm `(21 + 2)` reduces definitionally to the RHS. -/
theorem ar2_twenty_three (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 23
      = phi1 * ar2 phi1 phi2 z1 z2 22
        + phi2 * ar2 phi1 phi2 z1 z2 21 := rfl

/-- Recurrence step at index 24: `phi_1 * ar2 23 + phi_2 * ar2 22`.
    Pattern-match arm `(22 + 2)` reduces definitionally to the RHS. -/
theorem ar2_twenty_four (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 24
      = phi1 * ar2 phi1 phi2 z1 z2 23
        + phi2 * ar2 phi1 phi2 z1 z2 22 := rfl

/-- Recurrence step at index 25: `phi_1 * ar2 24 + phi_2 * ar2 23`.
    Pattern-match arm `(23 + 2)` reduces definitionally to the RHS. -/
theorem ar2_twenty_five (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 25
      = phi1 * ar2 phi1 phi2 z1 z2 24
        + phi2 * ar2 phi1 phi2 z1 z2 23 := rfl

/-- Recurrence step at index 26: `phi_1 * ar2 25 + phi_2 * ar2 24`.
    Pattern-match arm `(24 + 2)` reduces definitionally to the RHS. -/
theorem ar2_twenty_six (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 26
      = phi1 * ar2 phi1 phi2 z1 z2 25
        + phi2 * ar2 phi1 phi2 z1 z2 24 := rfl

/-- Recurrence step at index 27: `phi_1 * ar2 26 + phi_2 * ar2 25`.
    Pattern-match arm `(25 + 2)` reduces definitionally to the RHS. -/
theorem ar2_twenty_seven (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 27
      = phi1 * ar2 phi1 phi2 z1 z2 26
        + phi2 * ar2 phi1 phi2 z1 z2 25 := rfl

/-- Recurrence step at index 28: `phi_1 * ar2 27 + phi_2 * ar2 26`.
    Pattern-match arm `(26 + 2)` reduces definitionally to the RHS. -/
theorem ar2_twenty_eight (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 28
      = phi1 * ar2 phi1 phi2 z1 z2 27
        + phi2 * ar2 phi1 phi2 z1 z2 26 := rfl

/-- Recurrence step at index 29: `phi_1 * ar2 28 + phi_2 * ar2 27`.
    Pattern-match arm `(27 + 2)` reduces definitionally to the RHS. -/
theorem ar2_twenty_nine (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 29
      = phi1 * ar2 phi1 phi2 z1 z2 28
        + phi2 * ar2 phi1 phi2 z1 z2 27 := rfl

/-- Recurrence step at index 30: `phi_1 * ar2 29 + phi_2 * ar2 28`.
    Pattern-match arm `(28 + 2)` reduces definitionally to the RHS. -/
theorem ar2_thirty (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 30
      = phi1 * ar2 phi1 phi2 z1 z2 29
        + phi2 * ar2 phi1 phi2 z1 z2 28 := rfl

/-- Recurrence step at index 31: `phi_1 * ar2 30 + phi_2 * ar2 29`.
    Pattern-match arm `(29 + 2)` reduces definitionally to the RHS. -/
theorem ar2_thirty_one (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 31
      = phi1 * ar2 phi1 phi2 z1 z2 30
        + phi2 * ar2 phi1 phi2 z1 z2 29 := rfl

/-- Recurrence step at index 32: `phi_1 * ar2 31 + phi_2 * ar2 30`.
    Pattern-match arm `(30 + 2)` reduces definitionally to the RHS. -/
theorem ar2_thirty_two (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 32
      = phi1 * ar2 phi1 phi2 z1 z2 31
        + phi2 * ar2 phi1 phi2 z1 z2 30 := rfl

/-- Recurrence step at index 33: `phi_1 * ar2 32 + phi_2 * ar2 31`.
    Pattern-match arm `(31 + 2)` reduces definitionally to the RHS. -/
theorem ar2_thirty_three (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 33
      = phi1 * ar2 phi1 phi2 z1 z2 32
        + phi2 * ar2 phi1 phi2 z1 z2 31 := rfl

/-- *Trivial coefficients.*  When both AR(2) coefficients are zero,
    every recurrence step (index `n + 2`) vanishes regardless of
    the initial conditions.  The initial conditions at indices 0 and
    1 are unaffected. -/
theorem ar2_phi_zero (z1 z2 : Complex) (n : Nat) :
    ar2 0 0 z1 z2 (n + 2) = 0 :=
  let step1 : ar2 0 0 z1 z2 (n + 2)
              = 0 * ar2 0 0 z1 z2 (n + 1) + 0 * ar2 0 0 z1 z2 n := rfl
  let step2 : 0 * ar2 0 0 z1 z2 (n + 1) + 0 * ar2 0 0 z1 z2 n
              = (0 : Complex) + 0 :=
    congrArg₂ (· + ·) (zero_mul _) (zero_mul _)
  step1.trans (step2.trans (add_zero 0))

/-- *AR(1)-like degenerate case.*  When `phi_1 = 1` and `phi_2 = 0`,
    the recursion `ar2 1 0 z1 z2` becomes constant at `z2` from index
    1 onwards.  Induction on `n` with `one_mul` + `zero_mul` +
    `add_zero` in the recursion step. -/
theorem ar2_phi1_one_phi2_zero (z1 z2 : Complex) :
    forall (n : Nat), ar2 1 0 z1 z2 (n + 1) = z2
  | 0     => rfl
  | n + 1 =>
      let ih : ar2 1 0 z1 z2 (n + 1) = z2 := ar2_phi1_one_phi2_zero z1 z2 n
      let step1 : ar2 1 0 z1 z2 (n + 2)
                = 1 * ar2 1 0 z1 z2 (n + 1) + 0 * ar2 1 0 z1 z2 n := rfl
      let step2 : 1 * ar2 1 0 z1 z2 (n + 1) + 0 * ar2 1 0 z1 z2 n
                = ar2 1 0 z1 z2 (n + 1) + 0 :=
        congrArg₂ (· + ·) (one_mul _) (zero_mul _)
      let step3 : ar2 1 0 z1 z2 (n + 1) + 0 = ar2 1 0 z1 z2 (n + 1) :=
        add_zero _
      (step1.trans (step2.trans step3)).trans ih

/-- *Geometric degenerate case.*  When `phi_2 = 0`, the AR(2)
    recurrence collapses to a pure geometric step: index `n + 2`
    is `phi_1` times index `n + 1`, with no contribution from
    index `n`.  Computed via `ar2_succ_succ` plus `zero_mul`
    and `add_zero`. -/
theorem ar2_phi2_zero_succ (phi1 z1 z2 : Complex) (n : Nat) :
    ar2 phi1 0 z1 z2 (n + 2) = phi1 * ar2 phi1 0 z1 z2 (n + 1) :=
  let step1 : ar2 phi1 0 z1 z2 (n + 2)
            = phi1 * ar2 phi1 0 z1 z2 (n + 1)
              + 0 * ar2 phi1 0 z1 z2 n := rfl
  let step2 : phi1 * ar2 phi1 0 z1 z2 (n + 1)
              + 0 * ar2 phi1 0 z1 z2 n
            = phi1 * ar2 phi1 0 z1 z2 (n + 1) + 0 :=
    congrArg (phi1 * ar2 phi1 0 z1 z2 (n + 1) + ·) (zero_mul _)
  let step3 : phi1 * ar2 phi1 0 z1 z2 (n + 1) + 0
            = phi1 * ar2 phi1 0 z1 z2 (n + 1) :=
    add_zero _
  step1.trans (step2.trans step3)

/-- *Geometric boundary at index 2.*  Specialises
    `ar2_phi2_zero_succ` at `n = 0`: when `phi_2 = 0`, the value at
    index 2 collapses to `phi_1 * z_2` since the `n + 1 = 1`
    predecessor is the initial condition `z_2`.  Dual of
    `ar2_phi1_zero_two`. -/
theorem ar2_phi2_zero_two (phi1 z1 z2 : Complex) :
    ar2 phi1 0 z1 z2 2 = phi1 * z2 :=
  (ar2_phi2_zero_succ phi1 z1 z2 0).trans
    (congrArg (phi1 * ·) (ar2_one phi1 0 z1 z2))

/-- *Geometric boundary at index 3.*  Specialises
    `ar2_phi2_zero_succ` at `n = 1`: when `phi_2 = 0`, the value at
    index 3 collapses to `phi_1 * (phi_1 * z_2)`.  Chains
    `ar2_phi2_zero_succ` with `ar2_phi2_zero_two` under `phi_1 * ·`. -/
theorem ar2_phi2_zero_three (phi1 z1 z2 : Complex) :
    ar2 phi1 0 z1 z2 3 = phi1 * (phi1 * z2) :=
  (ar2_phi2_zero_succ phi1 z1 z2 1).trans
    (congrArg (phi1 * ·) (ar2_phi2_zero_two phi1 z1 z2))

/-- *Lag-skip degenerate case.*  When `phi_1 = 0`, the AR(2)
    recurrence skips the immediate predecessor: index `n + 2` is
    `phi_2` times index `n`, with no contribution from index
    `n + 1`.  Dual of `ar2_phi2_zero_succ`; same three-step
    structure with `zero_mul` and `zero_add` on the left summand. -/
theorem ar2_phi1_zero_succ (phi2 z1 z2 : Complex) (n : Nat) :
    ar2 0 phi2 z1 z2 (n + 2) = phi2 * ar2 0 phi2 z1 z2 n :=
  let step1 : ar2 0 phi2 z1 z2 (n + 2)
            = 0 * ar2 0 phi2 z1 z2 (n + 1)
              + phi2 * ar2 0 phi2 z1 z2 n := rfl
  let step2 : 0 * ar2 0 phi2 z1 z2 (n + 1)
              + phi2 * ar2 0 phi2 z1 z2 n
            = 0 + phi2 * ar2 0 phi2 z1 z2 n :=
    congrArg (· + phi2 * ar2 0 phi2 z1 z2 n) (zero_mul _)
  let step3 : (0 : Complex) + phi2 * ar2 0 phi2 z1 z2 n
            = phi2 * ar2 0 phi2 z1 z2 n :=
    zero_add _
  step1.trans (step2.trans step3)

/-- *Lag-skip boundary at index 2.*  Specialises `ar2_phi1_zero_succ`
    at `n = 0`: when `phi_1 = 0`, the value at index 2 collapses to
    `phi_2 * z_1` since the `n = 0` predecessor is the initial
    condition `z_1`.  Built by chaining the lag-skip recurrence with
    `ar2_zero` under the `phi_2 * ·` congruence. -/
theorem ar2_phi1_zero_two (phi2 z1 z2 : Complex) :
    ar2 0 phi2 z1 z2 2 = phi2 * z1 :=
  (ar2_phi1_zero_succ phi2 z1 z2 0).trans
    (congrArg (phi2 * ·) (ar2_zero 0 phi2 z1 z2))

/-- *Lag-skip boundary at index 3.*  Specialises
    `ar2_phi1_zero_succ` at `n = 1`: when `phi_1 = 0`, the value at
    index 3 collapses to `phi_2 * z_2` since the `n = 1` predecessor
    is the initial condition `z_2`.  Dual of `ar2_phi2_zero_three`. -/
theorem ar2_phi1_zero_three (phi2 z1 z2 : Complex) :
    ar2 0 phi2 z1 z2 3 = phi2 * z2 :=
  (ar2_phi1_zero_succ phi2 z1 z2 1).trans
    (congrArg (phi2 * ·) (ar2_one 0 phi2 z1 z2))

/-- *Fibonacci-like recurrence.*  When both AR(2) coefficients are
    `1`, the recurrence collapses to pure addition:
    `ar2 1 1 z1 z2 (n + 2) = ar2 1 1 z1 z2 (n + 1) + ar2 1 1 z1 z2 n`,
    i.e., the classical Fibonacci shape with initial seeds `z1, z2`.
    Three-step proof via `ar2_succ_succ` plus `one_mul` on both
    summands. -/
theorem ar2_phi1_one_phi2_one_succ (z1 z2 : Complex) (n : Nat) :
    ar2 1 1 z1 z2 (n + 2)
      = ar2 1 1 z1 z2 (n + 1) + ar2 1 1 z1 z2 n :=
  let step1 : ar2 1 1 z1 z2 (n + 2)
            = 1 * ar2 1 1 z1 z2 (n + 1) + 1 * ar2 1 1 z1 z2 n := rfl
  let step2 : 1 * ar2 1 1 z1 z2 (n + 1) + 1 * ar2 1 1 z1 z2 n
            = ar2 1 1 z1 z2 (n + 1) + ar2 1 1 z1 z2 n :=
    congrArg₂ (· + ·) (one_mul _) (one_mul _)
  step1.trans step2

/-- *Fibonacci-shape boundary at index 2.*  Specialises
    `ar2_phi1_one_phi2_one_succ` at `n = 0`: when both AR(2)
    coefficients are `1`, the value at index 2 is `z_2 + z_1`. -/
theorem ar2_phi1_one_phi2_one_two (z1 z2 : Complex) :
    ar2 1 1 z1 z2 2 = z2 + z1 :=
  ar2_phi1_one_phi2_one_succ z1 z2 0

/-- *Period-2 degenerate case.*  When `phi_1 = 0` and `phi_2 = 1`,
    the recursion `ar2 0 1 z1 z2` is 2-periodic: index `n + 2` equals
    index `n`.  Single-step calculation using the `n + 2` recurrence
    together with `zero_mul`, `one_mul`, and `zero_add`. -/
theorem ar2_phi1_zero_phi2_one (z1 z2 : Complex) (n : Nat) :
    ar2 0 1 z1 z2 (n + 2) = ar2 0 1 z1 z2 n :=
  let step1 : ar2 0 1 z1 z2 (n + 2)
            = 0 * ar2 0 1 z1 z2 (n + 1) + 1 * ar2 0 1 z1 z2 n := rfl
  let step2 : 0 * ar2 0 1 z1 z2 (n + 1) + 1 * ar2 0 1 z1 z2 n
            = (0 : Complex) + ar2 0 1 z1 z2 n :=
    congrArg₂ (· + ·) (zero_mul _) (one_mul _)
  let step3 : (0 : Complex) + ar2 0 1 z1 z2 n = ar2 0 1 z1 z2 n :=
    zero_add _
  step1.trans (step2.trans step3)

/-- *Zero initial conditions stay zero forever.*  With `z1 = z2 = 0`,
    `ar2 phi1 phi2 0 0 n = 0` for every `n`, irrespective of the
    AR(2) coefficients.  Structural recursion: base cases at `0` and
    `1` are `rfl` (initial conditions are literally `0`); the
    `n + 2` step combines the IH at `n + 1` and `n` with
    `mul_zero` on both summands and `add_zero`. -/
theorem ar2_const_zero (phi1 phi2 : Complex) :
    forall (n : Nat), ar2 phi1 phi2 0 0 n = 0
  | 0     => rfl
  | 1     => rfl
  | n + 2 =>
      let ih1 : ar2 phi1 phi2 0 0 (n + 1) = 0 :=
        ar2_const_zero phi1 phi2 (n + 1)
      let ih2 : ar2 phi1 phi2 0 0 n = 0 :=
        ar2_const_zero phi1 phi2 n
      let step1 : ar2 phi1 phi2 0 0 (n + 2)
                = phi1 * ar2 phi1 phi2 0 0 (n + 1)
                  + phi2 * ar2 phi1 phi2 0 0 n := rfl
      let step2 : phi1 * ar2 phi1 phi2 0 0 (n + 1)
                  + phi2 * ar2 phi1 phi2 0 0 n
                = phi1 * 0 + phi2 * 0 :=
        congrArg₂ (· + ·)
          (congrArg (phi1 * ·) ih1)
          (congrArg (phi2 * ·) ih2)
      let step3 : phi1 * 0 + phi2 * 0 = 0 :=
        (congrArg₂ (· + ·) (mul_zero phi1) (mul_zero phi2)).trans
          (add_zero 0)
      step1.trans (step2.trans step3)

/-! ## Regressor matrix and target -/

/-- The `4 x 2` regressor matrix used in the least-squares fit.

    For a sequence `z : Fin 6 -> Complex`, the rows of the regressor
    matrix are
      row 0: [z 0, z 1],
      row 1: [z 1, z 2],
      row 2: [z 2, z 3],
      row 3: [z 3, z 4].

    Concrete: `regressorMatrix4x2 z i j = z (i.val + j.val)`,
    with the `Fin 6` index witnessed by
    `i.val + j.val < 4 + 1 < 6`. -/
def regressorMatrix4x2 (z : Fin 6 -> Complex) :
    Matrix (Fin 4) (Fin 2) Complex :=
  fun i j =>
    z ⟨i.val + j.val,
       Nat.lt_succ_of_lt
         (Nat.add_lt_add_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt))⟩

/-- The target vector for the AR(2) least-squares fit:
    `[z 2, z 3, z 4, z 5]^T`.  Concrete:
    `regressorTarget4 z i = z (i.val + 2)`,
    with the `Fin 6` index witnessed by `i.val + 2 < 4 + 2 = 6`. -/
def regressorTarget4 (z : Fin 6 -> Complex) : Fin 4 -> Complex :=
  fun i => z ⟨i.val + 2, Nat.add_lt_add_right i.isLt 2⟩

/-! ## Least-squares fit (abstract) -/

/-- The least-squares estimate of the AR(2) coefficients:

      `(phi_1_hat, phi_2_hat) = ((Z^H Z)^{-1} Z^H y)_{0, 1}`

    where `Z = regressorMatrix4x2 z` and `y = regressorTarget4 z`.

    Concrete via Mathlib's `Matrix.conjTranspose` (`ᴴ`), matrix
    multiplication, `Matrix.mulVec`, and the noncomputable `Inv`
    instance on square matrices (which is `M.det⁻¹ • M.adjugate`,
    yielding `0` at singular `Z^H Z`).  Marked `noncomputable`
    because the inverse is classical (depends on `0⁻¹ = 0`
    convention for `Field` inverses). -/
noncomputable def ar2LeastSquaresFit (z : Fin 6 -> Complex) :
    Complex × Complex :=
  let Z : Matrix (Fin 4) (Fin 2) Complex := regressorMatrix4x2 z
  let y : Fin 4 -> Complex := regressorTarget4 z
  let ZH := Z.conjTranspose
  let ZHZ : Matrix (Fin 2) (Fin 2) Complex := ZH * Z
  let ZHy : Fin 2 -> Complex := ZH.mulVec y
  let solution : Fin 2 -> Complex := ZHZ⁻¹.mulVec ZHy
  (solution 0, solution 1)

/-- *Body unfold for `ar2LeastSquaresFit`.*  Spells out the closed-form
    `((Z^H Z)^{-1} Z^H y)` via the let-stack, exposing the matrix
    formula directly for downstream reasoning. -/
theorem ar2LeastSquaresFit_eq (z : Fin 6 -> Complex) :
    ar2LeastSquaresFit z =
      let Z : Matrix (Fin 4) (Fin 2) Complex := regressorMatrix4x2 z
      let y : Fin 4 -> Complex := regressorTarget4 z
      let ZH := Z.conjTranspose
      let ZHZ : Matrix (Fin 2) (Fin 2) Complex := ZH * Z
      let ZHy : Fin 2 -> Complex := ZH.mulVec y
      let solution : Fin 2 -> Complex := ZHZ⁻¹.mulVec ZHy
      (solution 0, solution 1) := rfl


/-! ## Approximation error (placeholder) -/

/-- *AR(2) approximation error bound.*

    For an RFView channel realisation `h_RFV`, the AR(2)
    approximation `h_AR(2)` produced by `ar2LeastSquaresFit`
    satisfies

      `|h_RFV_{k', j} - h_AR(2)_{k', j}| <= delta`

    for a residual `delta` that is small enough that the
    `b = 4` ORBGRAND-AI decoder's BLER is within fractions of a dB
    of perfect-CSI ORBGRAND-AI (paper, Fig. 12).

    *Placeholder shape.*  The claim quantifies over the per-pulse
    impulse response `z : Fin 6 -> Complex`: for each pulse, the
    fitted AR(2) coefficients reproduce the matched-filter output
    to within `delta` per coefficient.  `delta` is small in the
    sense that the per-coefficient error norm is bounded by a
    finite constant strictly less than the diagonal entry magnitude
    of `h_RFV`.  Captured here as `(P -> Q) -> True` to keep the
    structure of the implication explicit; the concrete bound
    requires bound propagation through `ar2LeastSquaresFit`, which
    is currently `opaque`. -/
theorem ar2_approximation_error_statement
    (n_s : Nat) (rowTaps : Fin n_s -> RFViewTaps) :
    (forall (z : Fin 6 -> Complex),
        exists (delta : Real),
          0 <= delta /\ delta < 1 /\
          forall (j' : Fin 6),
            -- The intended bound: AR(2) reconstruction squared
            -- error per pulse position is bounded by `delta^2`.
            -- Using `normSq` rather than `‖·‖` to stay in
            -- `Mathlib.Data.Complex.Basic` (no `Analysis.Normed`
            -- import needed).
            let (phi1, phi2) := ar2LeastSquaresFit z
            Complex.normSq (z j' -
              ar2 phi1 phi2 (z (0 : Fin 6)) (z (1 : Fin 6)) j'.val)
              <= delta * delta) -> True := by
  kan_intro _h
  kan_constructor

end Section06
end OrbgrandAi
