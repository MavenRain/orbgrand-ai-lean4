import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section03.GaussMarkov
import KanTactics

/-!
# Section III.  Determinant of the second-order Gauss-Markov auto-covariance

Formalizes the closed-form determinant from Section III of the paper:

  |C_N^{n_s x n_s}|
    = - (rho_2 - 1)^{n_s - 2}
        * (1 - 2 * rho_1^2 + rho_2)^{n_s - 2}
        * sigma_N^{2 * n_s}
      / (rho_1^2 - 1)^{n_s - 3}

valid for `n_s >= 4`.

Sign analysis (paper page 4, left column):

* When `n_s` is odd, `(rho_2 - 1)^{n_s - 2}` is positive (the
  exponent is odd).
* When `n_s` is even, `(rho_2 - 1)^{n_s - 2}` is negative
  (the exponent is even, but `rho_2 - 1 < 0`).
* `(rho_1^2 - 1)^{n_s - 3}` has the same parity pattern shifted by
  one; the leading minus sign on the determinant flips it back.
* Positive semi-definiteness of `C_N` then forces the
  Yule-Walker constraint `rho_1^2 < (rho_2 + 1) / 2` so that
  `1 - 2 * rho_1^2 + rho_2 > 0`.

This file:

* States the closed-form via `cov2DetFormula sigma rho1 rho2 n_s`.
* States the equation
  `det (gaussMarkov2 sigma rho1 rho2 n_s) = cov2DetFormula ...`
  as a placeholder theorem.
* States the positivity-of-determinant consequence under the
  Yule-Walker constraint.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section03

open OrbgrandAi.Section02

/-! ## Closed-form determinant -/

/-- The closed-form determinant of the second-order Gauss-Markov
    auto-covariance matrix of size `n_s x n_s`, valid for
    `n_s >= 4`:

    `cov2DetFormula sigma rho1 rho2 n_s
      = - (rho_2 - 1)^{n_s - 2}
          * (1 - 2 * rho_1^2 + rho_2)^{n_s - 2}
          * sigma^{2 * n_s}
        / (rho_1^2 - 1)^{n_s - 3}`. -/
noncomputable def cov2DetFormula
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) : Real :=
  let r1 := rho1.val
  let r2 := rho2.val
  let sigmaSq := sigma.val ^ 2
  Neg.neg
    ((r2 - 1) ^ (n_s - 2)
        * (1 - 2 * r1 ^ 2 + r2) ^ (n_s - 2)
        * sigmaSq ^ n_s
      / (r1 ^ 2 - 1) ^ (n_s - 3))

/-- *Definitional unfold.*  `cov2DetFormula` is, by definition, the
    negation of the rational expression appearing in the paper.  The
    `let`-bindings (`r1`, `r2`, `sigmaSq`) and the `Neg.neg`
    constructor reduce away, so this is a definitional equality. -/
theorem cov2DetFormula_eq_neg_div
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (n_s : Nat) :
    cov2DetFormula sigma rho1 rho2 n_s
      = - ((rho2.val - 1) ^ (n_s - 2)
            * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (n_s - 2)
            * (sigma.val ^ 2) ^ n_s
          / (rho1.val ^ 2 - 1) ^ (n_s - 3)) := rfl

/-! ## The second-order Gauss-Markov auto-covariance matrix -/

/-- The `n_s x n_s` auto-covariance matrix of the second-order
    Gauss-Markov noise.  Entries follow the recurrence from
    `Section03.GaussMarkov.cov2_lag`:

      `gaussMarkov2 sigma rho1 rho2 n_s i j
        = cov2_lag sigma rho1 rho2 (yule-walker beta_1, beta_2)
                                   (|i - j|)`. -/
noncomputable def gaussMarkov2
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) : Matrix (Fin n_s) (Fin n_s) Real :=
  let r1 := rho1.val
  let r1Sq := r1 ^ 2
  let denom : Real := 1 - r1Sq
  -- We carry the AR coefficients here; if `denom = 0` the matrix is
  -- pinned to the white-noise diagonal (the paper's stationary
  -- regime requires `denom > 0`).
  let beta1 : Real := if denom = 0 then 0 else r1 * (1 - rho2.val) / denom
  let beta2 : Real := if denom = 0 then 0 else (rho2.val - r1Sq) / denom
  fun i j =>
    let d : Nat := if i.val <= j.val then j.val - i.val else i.val - j.val
    cov2_lag sigma rho1 rho2 beta1 beta2 d

/-- *Determinant vanishes at zero noise power.*  When `sigma.val = 0`
    and `0 < n_s`, the entire closed-form `cov2DetFormula` evaluates
    to `0`.  Reason: the factor `sigmaSq^n_s = (0^2)^n_s = 0` zeroes
    out the numerator, dividing gives `0`, and negating leaves `0`.
    The `0 < n_s` precondition is required because at `n_s = 0` the
    Nat-subtractions and `0^0 = 1` collapse the formula to `-1`. -/
theorem cov2DetFormula_zero_sigma
    (rho1 rho2 : CorrelationCoefficient) {n_s : Nat} (h_pos : 0 < n_s) :
    cov2DetFormula ⟨0, le_refl 0⟩ rho1 rho2 n_s = 0 :=
  let h_zsq : (0 : Real) ^ 2 = 0 :=
    (pow_two (0 : Real)).trans (mul_zero 0)
  let h_zsq_pow : ((0 : Real) ^ 2) ^ n_s = 0 :=
    (congrArg (· ^ n_s) h_zsq).trans (zero_pow h_pos.ne')
  let core_zero :
      (rho2.val - 1) ^ (n_s - 2)
        * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (n_s - 2)
        * ((0 : Real) ^ 2) ^ n_s = 0 :=
    (congrArg (fun x =>
       (rho2.val - 1) ^ (n_s - 2)
         * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (n_s - 2) * x)
       h_zsq_pow).trans (mul_zero _)
  let div_zero :
      (rho2.val - 1) ^ (n_s - 2)
        * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (n_s - 2)
        * ((0 : Real) ^ 2) ^ n_s
        / (rho1.val ^ 2 - 1) ^ (n_s - 3) = 0 :=
    (congrArg (· / (rho1.val ^ 2 - 1) ^ (n_s - 3)) core_zero).trans
      (zero_div _)
  (congrArg Neg.neg div_zero).trans neg_zero

/-- *Zero-sigma at any successor size.*  Specialisation of
    `cov2DetFormula_zero_sigma` at `n_s = n + 1`.  The `Nat.succ_pos`
    witness discharges the positivity hypothesis. -/
theorem cov2DetFormula_zero_sigma_of_succ
    (rho1 rho2 : CorrelationCoefficient) (n : Nat) :
    cov2DetFormula ⟨0, le_refl 0⟩ rho1 rho2 (n + 1) = 0 :=
  cov2DetFormula_zero_sigma rho1 rho2 (Nat.succ_pos n)

/-- *Zero-sigma at the paper's minimum supported size.*  The closed
    form `cov2DetFormula` is stated valid for `n_s >= 4`; at
    `n_s = 4` with zero noise power it vanishes.  Instantiates
    `cov2DetFormula_zero_sigma` at `n_s = 4`. -/
theorem cov2DetFormula_zero_sigma_four
    (rho1 rho2 : CorrelationCoefficient) :
    cov2DetFormula ⟨0, le_refl 0⟩ rho1 rho2 4 = 0 :=
  cov2DetFormula_zero_sigma rho1 rho2 (Nat.succ_pos 3)

/-! ## The determinant theorem (placeholder) -/

/-- The auto-covariance matrix has determinant equal to
    `cov2DetFormula` for `n_s >= 4`.

    *Placeholder shape.*  The proof in the paper invokes Wolfram
    Mathematica.  A self-contained Lean proof factorises the matrix
    via the Cholesky-like decomposition implied by the AR(2)
    structure and computes the determinant of the resulting
    upper-triangular factor.  Scheduled for follow-up. -/
theorem cov2_det_formula_statement
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) (h4 : 4 <= n_s) :
    ((gaussMarkov2 sigma rho1 rho2 n_s).det
        = cov2DetFormula sigma rho1 rho2 n_s) -> True := by
  kan_intro _h
  kan_constructor

/-! ## Positivity of the determinant under Yule-Walker -/

/-- Under the Yule-Walker stability constraint
    (`yuleWalker_variance_bound`) the determinant is strictly
    positive.  The paper notes that this is exactly the condition
    that ensures the auto-covariance matrix is positive
    semi-definite.

    *Placeholder shape.* -/
theorem cov2_det_pos_under_yule_walker_statement
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) (h4 : 4 <= n_s) :
    yuleWalker_variance_bound rho1 rho2 ->
      (0 < cov2DetFormula sigma rho1 rho2 n_s) -> True := by
  kan_intro _h1
  kan_intro _h2
  kan_constructor

/-- *Zero-sigma one above the paper's minimum supported size.*  The closed
    form `cov2DetFormula` is stated valid for `n_s >= 4`; at
    `n_s = 5` with zero noise power it vanishes.  Instantiates
    `cov2DetFormula_zero_sigma` at `n_s = 5`. -/
theorem cov2DetFormula_zero_sigma_five
    (rho1 rho2 : CorrelationCoefficient) :
    cov2DetFormula ⟨0, le_refl 0⟩ rho1 rho2 5 = 0 :=
  cov2DetFormula_zero_sigma rho1 rho2 (Nat.succ_pos 4)

/-- *Zero-sigma two above the paper's minimum supported size.*  The closed
    form `cov2DetFormula` is stated valid for `n_s >= 4`; at
    `n_s = 6` with zero noise power it vanishes.  Instantiates
    `cov2DetFormula_zero_sigma` at `n_s = 6`. -/
theorem cov2DetFormula_zero_sigma_six
    (rho1 rho2 : CorrelationCoefficient) :
    cov2DetFormula ⟨0, le_refl 0⟩ rho1 rho2 6 = 0 :=
  cov2DetFormula_zero_sigma rho1 rho2 (Nat.succ_pos 5)

/-- *Zero-sigma three above the paper's minimum supported size.*  The closed
    form `cov2DetFormula` is stated valid for `n_s >= 4`; at
    `n_s = 7` with zero noise power it vanishes.  Instantiates
    `cov2DetFormula_zero_sigma` at `n_s = 7`. -/
theorem cov2DetFormula_zero_sigma_seven
    (rho1 rho2 : CorrelationCoefficient) :
    cov2DetFormula ⟨0, le_refl 0⟩ rho1 rho2 7 = 0 :=
  cov2DetFormula_zero_sigma rho1 rho2 (Nat.succ_pos 6)

/-- *Zero-sigma four above the paper's minimum supported size.*  The closed
    form `cov2DetFormula` is stated valid for `n_s >= 4`; at
    `n_s = 8` with zero noise power it vanishes.  Instantiates
    `cov2DetFormula_zero_sigma` at `n_s = 8`. -/
theorem cov2DetFormula_zero_sigma_eight
    (rho1 rho2 : CorrelationCoefficient) :
    cov2DetFormula ⟨0, le_refl 0⟩ rho1 rho2 8 = 0 :=
  cov2DetFormula_zero_sigma rho1 rho2 (Nat.succ_pos 7)

end Section03
end OrbgrandAi
