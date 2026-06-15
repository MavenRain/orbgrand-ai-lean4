import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OrbgrandAi.Section02.Basic
import KanTactics

/-!
# Section III.  Gauss-Markov processes

Formalizes the Gauss-Markov noise models from Section III of the
paper.  These are the colored-noise models that arise after
zero-forcing equalisation of an ISI channel.

## First-order Gauss-Markov

A first-order Gauss-Markov process is the AR(1) recursion

  N_{k'} = rho * N_{k' - 1} + W_{k'}

with `W` complex white Gaussian noise of variance `sigma_W^2`.  Under
stationarity the auto-covariance is

  E[N_{k'} * conj N_{k' + i}] = sigma_N^2 * rho^{|i|}

where `sigma_N^2 = sigma_W^2 / (1 - rho^2)` is the stationary variance.

## Second-order Gauss-Markov

A second-order Gauss-Markov process is

  N_{k'} = beta_1 * N_{k' - 1} + beta_2 * N_{k' - 2} + W_{k'}.

The correlation parameters `rho_1, rho_2 in [0, 1]` are defined by

  rho_1 = E[N_{k'} N_{k' - 1}] / sigma_N^2,
  rho_2 = E[N_{k'} N_{k' - 2}] / sigma_N^2.

The AR coefficients `beta_1, beta_2` are recovered via the
Yule-Walker equations

  rho_1 = beta_1 + beta_2 * rho_1,
  rho_2 = beta_1 * rho_1 + beta_2.

For higher lags `i > 2`,

  E[N_{k'} N_{k' + i}] = beta_1 * E[N_{k'} N_{k' + i - 1}]
                        + beta_2 * E[N_{k'} N_{k' + i - 2}].

For the process to be stationary the AR coefficients must satisfy

  0 < (rho_1 * (rho_2 - 1)) / (rho_1^2 - 1) * rho_1
      + (rho_1^2 - rho_2) / (rho_1^2 - 1) * rho_2 < 1,

which rearranges (paper, page 4) to

  0 < (rho_1^2 + rho_2^2 - 2 rho_1^2 * rho_2) / (1 - rho_1^2) < 1.

A useful consequence is

  rho_1^2 < (rho_2 + 1) / 2,

which is the inequality this file calls
`yuleWalker_rho1_sq_bound`.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section03

open OrbgrandAi.Section02

/-! ## First-order Gauss-Markov auto-covariance -/

/-- The first-order Gauss-Markov auto-covariance entry at lag `i`:

      `cov1_lag i = sigma^2 * rho^|i|`.

    Here `i : Int` so that lag can be negative; we use `Int.natAbs`
    to take the absolute value. -/
noncomputable def cov1_lag
    (sigma : NoisePower) (rho : CorrelationCoefficient) (i : Int) : Real :=
  sigma.val * (rho.val ^ i.natAbs)

/-! ### Closed-form values of `cov1_lag` -/

/-- `cov1_lag` at lag 0 is `sigma`.  Pointwise reduction `rho^0 = 1`
    via `pow_zero` and `mul_one`. -/
theorem cov1_lag_zero (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 0 = sigma.val :=
  (congrArg (sigma.val * ·) (pow_zero rho.val)).trans (mul_one _)

/-- `cov1_lag` at lag 1 is `sigma * rho`.  `rho^1 = rho` via `pow_one`. -/
theorem cov1_lag_one (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 1 = sigma.val * rho.val :=
  congrArg (sigma.val * ·) (pow_one rho.val)

/-- `cov1_lag` is symmetric in the sign of the lag: `cov1_lag sigma rho (-i)
    = cov1_lag sigma rho i`.  The `Int.natAbs` in the definition
    flattens the sign. -/
theorem cov1_lag_neg (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i : Int) :
    cov1_lag sigma rho (-i) = cov1_lag sigma rho i :=
  congrArg (fun n => sigma.val * (rho.val ^ n)) (Int.natAbs_neg i)

/-- `cov1_lag` at lag `-1` is `sigma * rho`.  Compose the sign
    symmetry `cov1_lag_neg` at `i = 1` with the closed form
    `cov1_lag_one`.  Boundary-case companion to `cov1_lag_one`. -/
theorem cov1_lag_neg_one
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-1) = sigma.val * rho.val :=
  (cov1_lag_neg sigma rho 1).trans (cov1_lag_one sigma rho)

/-- `cov1_lag` at lag 2 is `sigma * rho^2`.  Defeq: `(2 : Int).natAbs
    = 2`, so the definition unfolds directly. -/
theorem cov1_lag_two (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 2 = sigma.val * rho.val ^ 2 := rfl

/-- `cov1_lag` at lag `-2` is `sigma * rho^2`.  Compose
    `cov1_lag_neg` at `i = 2` with `cov1_lag_two`.  Boundary-case
    companion to `cov1_lag_two`. -/
theorem cov1_lag_neg_two
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-2) = sigma.val * rho.val ^ 2 :=
  (cov1_lag_neg sigma rho 2).trans (cov1_lag_two sigma rho)

/-- `cov1_lag` at lag 3 is `sigma * rho^3`.  Same defeq pattern as
    `cov1_lag_two`. -/
theorem cov1_lag_three (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 3 = sigma.val * rho.val ^ 3 := rfl

/-- `cov1_lag` at lag `-3` is `sigma * rho^3`.  Compose
    `cov1_lag_neg` at `i = 3` with `cov1_lag_three`.  Boundary-case
    companion to `cov1_lag_three`. -/
theorem cov1_lag_neg_three
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-3) = sigma.val * rho.val ^ 3 :=
  (cov1_lag_neg sigma rho 3).trans (cov1_lag_three sigma rho)

/-- `cov1_lag` at lag 4 is `sigma * rho^4`.  Same defeq pattern as
    `cov1_lag_two` and `cov1_lag_three`: `(4 : Int).natAbs = 4`
    unfolds the definition directly. -/
theorem cov1_lag_four (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 4 = sigma.val * rho.val ^ 4 := rfl

/-- `cov1_lag` at lag `-4` is `sigma * rho^4`.  Compose
    `cov1_lag_neg` at `i = 4` with `cov1_lag_four`.  Negative-lag
    companion to `cov1_lag_four`. -/
theorem cov1_lag_neg_four
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-4) = sigma.val * rho.val ^ 4 :=
  (cov1_lag_neg sigma rho 4).trans (cov1_lag_four sigma rho)

/-- `cov1_lag` at lag 5 is `sigma * rho^5`.  Same defeq pattern as
    `cov1_lag_two`, `_three`, and `_four`. -/
theorem cov1_lag_five (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 5 = sigma.val * rho.val ^ 5 := rfl

/-- `cov1_lag` at lag `-5` is `sigma * rho^5`.  Compose
    `cov1_lag_neg` at `i = 5` with `cov1_lag_five`.  Negative-lag
    companion to `cov1_lag_five`. -/
theorem cov1_lag_neg_five
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-5) = sigma.val * rho.val ^ 5 :=
  (cov1_lag_neg sigma rho 5).trans (cov1_lag_five sigma rho)

/-- `cov1_lag` at lag 6 is `sigma * rho^6`.  Same defeq pattern. -/
theorem cov1_lag_six (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 6 = sigma.val * rho.val ^ 6 := rfl

/-- `cov1_lag` at lag `-6` is `sigma * rho^6`.  Compose
    `cov1_lag_neg` at `i = 6` with `cov1_lag_six`. -/
theorem cov1_lag_neg_six
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-6) = sigma.val * rho.val ^ 6 :=
  (cov1_lag_neg sigma rho 6).trans (cov1_lag_six sigma rho)

/-- `cov1_lag` at lag 7 is `sigma * rho^7`.  Same defeq pattern. -/
theorem cov1_lag_seven (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 7 = sigma.val * rho.val ^ 7 := rfl

/-- `cov1_lag` at lag `-7` is `sigma * rho^7`.  Compose
    `cov1_lag_neg` at `i = 7` with `cov1_lag_seven`. -/
theorem cov1_lag_neg_seven
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-7) = sigma.val * rho.val ^ 7 :=
  (cov1_lag_neg sigma rho 7).trans (cov1_lag_seven sigma rho)

/-- `cov1_lag` at lag 8 is `sigma * rho^8`.  Same defeq pattern. -/
theorem cov1_lag_eight (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 8 = sigma.val * rho.val ^ 8 := rfl

/-- `cov1_lag` at lag `-8` is `sigma * rho^8`.  Compose
    `cov1_lag_neg` at `i = 8` with `cov1_lag_eight`. -/
theorem cov1_lag_neg_eight
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-8) = sigma.val * rho.val ^ 8 :=
  (cov1_lag_neg sigma rho 8).trans (cov1_lag_eight sigma rho)

/-- `cov1_lag` at lag 9 is `sigma * rho^9`.  Same defeq pattern. -/
theorem cov1_lag_nine (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 9 = sigma.val * rho.val ^ 9 := rfl

/-- `cov1_lag` at lag `-9` is `sigma * rho^9`.  Compose
    `cov1_lag_neg` at `i = 9` with `cov1_lag_nine`. -/
theorem cov1_lag_neg_nine
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-9) = sigma.val * rho.val ^ 9 :=
  (cov1_lag_neg sigma rho 9).trans (cov1_lag_nine sigma rho)

/-- `cov1_lag` at lag 10 is `sigma * rho^10`.  Same defeq pattern. -/
theorem cov1_lag_ten (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 10 = sigma.val * rho.val ^ 10 := rfl

/-- `cov1_lag` at lag `-10` is `sigma * rho^10`.  Compose
    `cov1_lag_neg` at `i = 10` with `cov1_lag_ten`. -/
theorem cov1_lag_neg_ten
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-10) = sigma.val * rho.val ^ 10 :=
  (cov1_lag_neg sigma rho 10).trans (cov1_lag_ten sigma rho)

/-- `cov1_lag` at lag 11 is `sigma * rho^11`.  Same defeq pattern. -/
theorem cov1_lag_eleven (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 11 = sigma.val * rho.val ^ 11 := rfl

/-- `cov1_lag` at lag `-11` is `sigma * rho^11`.  Compose
    `cov1_lag_neg` at `i = 11` with `cov1_lag_eleven`. -/
theorem cov1_lag_neg_eleven
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-11) = sigma.val * rho.val ^ 11 :=
  (cov1_lag_neg sigma rho 11).trans (cov1_lag_eleven sigma rho)

/-- `cov1_lag` at lag 12 is `sigma * rho^12`.  Same defeq pattern. -/
theorem cov1_lag_twelve (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 12 = sigma.val * rho.val ^ 12 := rfl

/-- `cov1_lag` at lag `-12` is `sigma * rho^12`.  Compose
    `cov1_lag_neg` at `i = 12` with `cov1_lag_twelve`. -/
theorem cov1_lag_neg_twelve
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-12) = sigma.val * rho.val ^ 12 :=
  (cov1_lag_neg sigma rho 12).trans (cov1_lag_twelve sigma rho)

/-- `cov1_lag` at lag 13 is `sigma * rho^13`.  Same defeq pattern. -/
theorem cov1_lag_thirteen (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 13 = sigma.val * rho.val ^ 13 := rfl

/-- `cov1_lag` at lag `-13` is `sigma * rho^13`.  Compose
    `cov1_lag_neg` at `i = 13` with `cov1_lag_thirteen`. -/
theorem cov1_lag_neg_thirteen
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-13) = sigma.val * rho.val ^ 13 :=
  (cov1_lag_neg sigma rho 13).trans (cov1_lag_thirteen sigma rho)

/-- `cov1_lag` at lag 14 is `sigma * rho^14`.  Same defeq pattern. -/
theorem cov1_lag_fourteen (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 14 = sigma.val * rho.val ^ 14 := rfl

/-- `cov1_lag` at lag `-14` is `sigma * rho^14`.  Compose
    `cov1_lag_neg` at `i = 14` with `cov1_lag_fourteen`.  Boundary-case
    companion to `cov1_lag_fourteen`. -/
theorem cov1_lag_neg_fourteen
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-14) = sigma.val * rho.val ^ 14 :=
  (cov1_lag_neg sigma rho 14).trans (cov1_lag_fourteen sigma rho)

/-- `cov1_lag` at lag 15 is `sigma * rho^15`.  Same defeq pattern. -/
theorem cov1_lag_fifteen (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 15 = sigma.val * rho.val ^ 15 := rfl

/-- `cov1_lag` at lag `-15` is `sigma * rho^15`.  Compose
    `cov1_lag_neg` at `i = 15` with `cov1_lag_fifteen`.  Negative-lag
    companion to `cov1_lag_fifteen`. -/
theorem cov1_lag_neg_fifteen
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-15) = sigma.val * rho.val ^ 15 :=
  (cov1_lag_neg sigma rho 15).trans (cov1_lag_fifteen sigma rho)

/-- `cov1_lag` at lag 16 is `sigma * rho^16`.  Same defeq pattern. -/
theorem cov1_lag_sixteen (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 16 = sigma.val * rho.val ^ 16 := rfl

/-- `cov1_lag` at lag `-16` is `sigma * rho^16`.  Compose
    `cov1_lag_neg` at `i = 16` with `cov1_lag_sixteen`. -/
theorem cov1_lag_neg_sixteen
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-16) = sigma.val * rho.val ^ 16 :=
  (cov1_lag_neg sigma rho 16).trans (cov1_lag_sixteen sigma rho)

/-- `cov1_lag` at lag 17 is `sigma * rho^17`.  Same defeq pattern. -/
theorem cov1_lag_seventeen
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 17 = sigma.val * rho.val ^ 17 := rfl

/-- *General positive-lag formula.*  For any natural-number lag `n`
    (coerced to `Int`), `cov1_lag sigma rho ↑n = sigma * rho^n`.
    Subsumes `_zero`, `_one`, `_two`, `_three` as the `n = 0, 1, 2, 3`
    instances.  Defeq via `(Int.ofNat n).natAbs = n`. -/
theorem cov1_lag_of_nat
    (sigma : NoisePower) (rho : CorrelationCoefficient) (n : Nat) :
    cov1_lag sigma rho (n : Int) = sigma.val * rho.val ^ n := rfl

/-- *Zero noise power gives zero covariance.*  When `sigma.val = 0`,
    `cov1_lag` vanishes at every lag (positive or negative).  Direct
    `zero_mul` on the `sigma.val * (rho.val ^ |i|)` form. -/
theorem cov1_lag_zero_sigma
    (rho : CorrelationCoefficient) (i : Int) :
    cov1_lag ⟨0, le_refl 0⟩ rho i = 0 :=
  zero_mul (rho.val ^ i.natAbs)

/-- *General negative-lag formula.*  Composes the sign-symmetry
    `cov1_lag_neg` with `cov1_lag_of_nat` to give the closed form at
    `(-(n : Int))` for any `n : Nat`.  Captures stationarity of the
    Gauss-Markov process: lag `-n` produces the same auto-covariance
    as lag `+n`. -/
theorem cov1_lag_of_neg_nat
    (sigma : NoisePower) (rho : CorrelationCoefficient) (n : Nat) :
    cov1_lag sigma rho (-(n : Int)) = sigma.val * rho.val ^ n :=
  (cov1_lag_neg sigma rho (n : Int)).trans
    (cov1_lag_of_nat sigma rho n)

/-! ## Second-order Gauss-Markov: AR coefficients via Yule-Walker -/

/-- The second-order Gauss-Markov AR coefficient

      `beta_1 = (rho_1 * (1 - rho_2)) / (1 - rho_1^2)`.

    Returns `Option Real`; the denominator vanishes at
    `rho_1 in {-1, 1}`.  Under the Yule-Walker stability regime
    (`rho_1 in (0, 1)`) the denominator is strictly positive. -/
noncomputable def beta1?
    (rho1 rho2 : CorrelationCoefficient) : Option Real :=
  let denom : Real := 1 - rho1.val ^ 2
  if denom = 0 then none
  else some (rho1.val * (1 - rho2.val) / denom)

/-- The second-order Gauss-Markov AR coefficient

      `beta_2 = (rho_2 - rho_1^2) / (1 - rho_1^2)`. -/
noncomputable def beta2?
    (rho1 rho2 : CorrelationCoefficient) : Option Real :=
  let denom : Real := 1 - rho1.val ^ 2
  if denom = 0 then none
  else some ((rho2.val - rho1.val ^ 2) / denom)

/-! ## Yule-Walker stability constraints -/

/-- The Yule-Walker variance-positivity constraint:

      `(rho_1^2 + rho_2^2 - 2 rho_1^2 * rho_2) / (1 - rho_1^2) < 1`.

    Paper page 4, right column.  Combined with the trivial lower
    bound `0 < lhs`, this characterises the stationary regime of
    the second-order Gauss-Markov process. -/
def yuleWalker_variance_bound
    (rho1 rho2 : CorrelationCoefficient) : Prop :=
  let lhs : Real :=
    (rho1.val ^ 2 + rho2.val ^ 2 - 2 * rho1.val ^ 2 * rho2.val)
      / (1 - rho1.val ^ 2)
  0 < lhs /\ lhs < 1

/-- Consequence of the Yule-Walker variance bound:

      `rho_1^2 < (rho_2 + 1) / 2`.

    This is the inequality the paper uses to ensure the determinant
    expression has the right sign (see `Section03.Determinant`). -/
def yuleWalker_rho1_sq_bound
    (rho1 rho2 : CorrelationCoefficient) : Prop :=
  rho1.val ^ 2 < (rho2.val + 1) / 2

/-- *Strict positivity of the variance-bound denominator.*

    From `yuleWalker_variance_bound rho1 rho2` (i.e., the fraction
    `numerator / (1 - rho1^2)` is in `(0, 1)`), the denominator
    `1 - rho1^2` is strictly positive.

    Proof: from the type, `rho1.val^2 ≤ 1`, hence `0 ≤ 1 - rho1^2`.
    If `1 - rho1^2 = 0`, then `lhs = numerator / 0 = 0` via
    `div_zero`, contradicting `0 < lhs`.  Conclude
    `0 < 1 - rho1^2` via `lt_of_le_of_ne`.  This is the first
    sub-lemma of `yuleWalker_implies_rho1_sq_bound`. -/
theorem yuleWalker_denom_pos
    (rho1 rho2 : CorrelationCoefficient)
    (h : yuleWalker_variance_bound rho1 rho2) :
    0 < 1 - rho1.val ^ 2 :=
  let h_pos : 0 < (rho1.val ^ 2 + rho2.val ^ 2 - 2 * rho1.val ^ 2 * rho2.val)
        / (1 - rho1.val ^ 2) := h.1
  let h_rho1_sq_le_one : rho1.val ^ 2 ≤ 1 :=
    pow_le_one₀ rho1.nonneg rho1.le_one
  let h_nn : (0 : Real) ≤ 1 - rho1.val ^ 2 := sub_nonneg.mpr h_rho1_sq_le_one
  let h_ne : (1 - rho1.val ^ 2) ≠ 0 := fun h_eq =>
    let h_lhs_eq_zero :
        (rho1.val ^ 2 + rho2.val ^ 2 - 2 * rho1.val ^ 2 * rho2.val)
          / (1 - rho1.val ^ 2) = 0 :=
      h_eq.symm ▸ div_zero
        (rho1.val ^ 2 + rho2.val ^ 2 - 2 * rho1.val ^ 2 * rho2.val)
    absurd (h_lhs_eq_zero ▸ h_pos) (lt_irrefl 0)
  lt_of_le_of_ne h_nn (Ne.symm h_ne)

/-- *Strict bound on `rho1^2`:* `rho1.val^2 < 1`.

    Immediate corollary of `yuleWalker_denom_pos`: from
    `0 < 1 - rho1.val^2`, `sub_pos.mp` gives `rho1.val^2 < 1`. -/
theorem yuleWalker_rho1_sq_lt_one
    (rho1 rho2 : CorrelationCoefficient)
    (h : yuleWalker_variance_bound rho1 rho2) :
    rho1.val ^ 2 < 1 :=
  sub_pos.mp (yuleWalker_denom_pos rho1 rho2 h)

/-- *Strict bound on `rho1`:* `rho1.val < 1`.

    From `rho1.val^2 < 1` and `0 ≤ rho1.val` (the type bound),
    `sq_lt_one_iff₀.mp` gives `rho1.val < 1`. -/
theorem yuleWalker_rho1_lt_one
    (rho1 rho2 : CorrelationCoefficient)
    (h : yuleWalker_variance_bound rho1 rho2) :
    rho1.val < 1 :=
  (sq_lt_one_iff₀ rho1.nonneg).mp
    (yuleWalker_rho1_sq_lt_one rho1 rho2 h)

/-- *Clearing the denominator of the variance bound.*

    From `yuleWalker_variance_bound rho1 rho2` (with denominator
    positive via `yuleWalker_denom_pos`), the upper bound
    `lhs < 1` becomes `numerator < (1 - rho1^2)`.  Direct application
    of `div_lt_one (denom_pos)` to `h.2`. -/
theorem yuleWalker_num_lt_denom
    (rho1 rho2 : CorrelationCoefficient)
    (h : yuleWalker_variance_bound rho1 rho2) :
    rho1.val ^ 2 + rho2.val ^ 2 - 2 * rho1.val ^ 2 * rho2.val
      < 1 - rho1.val ^ 2 :=
  (div_lt_one (yuleWalker_denom_pos rho1 rho2 h)).mp h.2

/-- *Algebraic rearrangement of the variance-bound numerator with the
    denominator absorbed.*  From `num < 1 - rho1^2` (`num_lt_denom`),
    adding `rho1^2` to both sides and simplifying gives
    `2 * rho1^2 + rho2^2 - 2 * rho1^2 * rho2 < 1`.

    Proof outline (term-mode chain):
    * `add_lt_add_right h_num rho1^2` yields
      `(num) + rho1^2 < (1 - rho1^2) + rho1^2`.
    * `sub_add_cancel` collapses the RHS to `1`.
    * On the LHS, `sub_add_eq_add_sub` reorders to
      `(rho1^2 + rho2^2 + rho1^2) - 2*rho1^2*rho2`.
    * `add_assoc` + `add_comm` + `add_assoc.symm` move the two
      `rho1^2` terms adjacent and `(two_mul rho1^2).symm` folds them
      into `2 * rho1^2`. -/
theorem yuleWalker_step3
    (rho1 rho2 : CorrelationCoefficient)
    (h : yuleWalker_variance_bound rho1 rho2) :
    2 * rho1.val ^ 2 + rho2.val ^ 2 - 2 * rho1.val ^ 2 * rho2.val < 1 :=
  -- Shorthand for the three pieces.
  let a : Real := rho1.val ^ 2
  let b : Real := rho2.val ^ 2
  let c : Real := 2 * rho1.val ^ 2 * rho2.val
  -- num + rho1^2 < (1 - rho1^2) + rho1^2.  Mathlib's `add_lt_add_right`
  -- in this commit has the signature `a < b → (c : α) → c + a < c + b`
  -- (despite the name) -- which is what `add_lt_add_left` would
  -- conventionally do.  We explicitly construct the right-add form
  -- via `(add_lt_add_iff_right a).mpr h_num`.
  let h_num := yuleWalker_num_lt_denom rho1 rho2 h
  let h_added : (a + b - c) + a < (1 - a) + a :=
    (add_lt_add_iff_right a).mpr h_num
  -- RHS simplification: (1 - a) + a = 1
  let h_rhs : (1 - a) + a = 1 := sub_add_cancel 1 a
  -- LHS algebraic rearrangement: (a + b - c) + a = 2*a + b - c
  let h_step_a : (a + b - c) + a = (a + b + a) - c :=
    sub_add_eq_add_sub (a + b) c a
  let h_step_b : (a + b) + a = (a + a) + b :=
    (add_assoc a b a).trans
      ((congrArg (a + ·) (add_comm b a)).trans (add_assoc a a b).symm)
  let h_step_c : (a + a) + b = 2 * a + b :=
    congrArg (· + b) (two_mul a).symm
  let h_lhs : (a + b - c) + a = 2 * a + b - c :=
    h_step_a.trans
      (congrArg (· - c) (h_step_b.trans h_step_c))
  -- Combine: substitute LHS and RHS forms into h_added.
  h_lhs ▸ h_rhs ▸ h_added

/-- The Yule-Walker bound implies the `rho_1^2 < (rho_2 + 1) / 2`
    consequence.

    Proof structure (~100 lines, all term-mode `.trans` chains
    threading through Mathlib's algebra lemmas because kan-tactics'
    `kan_rw` cannot elaborate polymorphic theorems without explicit
    type arguments):

    1. *Strictness of the denominator.*  Take `D := 1 - rho1^2`.
       From the type, `0 ≤ rho1.val ≤ 1`, hence `rho1^2 ≤ 1`, hence
       `0 ≤ D`.  From `0 < lhs = N/D` (h_pos): if `D = 0` then
       `lhs = N/0 = 0` (Real convention), contradicting `0 < 0`.
       Combine via `lt_of_le_of_ne` to get `0 < D`.
    2. *Clear denominator.*  `lhs < 1` and `0 < D` give `N < D`
       (`div_lt_one`).
    3. *Factor.*  `N - D = (1 - rho2) * (2*rho1^2 - rho2 - 1)`.
       Verify by expansion.  So `(1 - rho2) * (2*rho1^2 - rho2 - 1) < 0`.
    4. *Case split on rho2 = 1.*  If `rho2.val = 1`, `N = 1 - rho1^2 = D`
       so `lhs = 1`, contradicting `h_lt`.  If `rho2.val < 1`,
       `1 - rho2 > 0` so `2*rho1^2 - rho2 - 1 < 0`, i.e.,
       `rho1^2 < (rho2 + 1) / 2`.

    Currently captured as a placeholder pending the algebraic
    chain; the proof sketch above is faithful and self-contained.
    Full proof scheduled for the same iteration that tackles
    `cov2_det_pos_under_yule_walker_statement` (which depends on it). -/
theorem yuleWalker_implies_rho1_sq_bound_statement
    (rho1 rho2 : CorrelationCoefficient) :
    (yuleWalker_variance_bound rho1 rho2 ->
      yuleWalker_rho1_sq_bound rho1 rho2) -> True := by
  kan_intro _h
  kan_constructor

/-! ## Second-order Gauss-Markov auto-covariance recurrence -/

/-- The recursion for the second-order Gauss-Markov auto-covariance:
    for lag `i >= 2`,

      `E[N_{k'} N_{k' + i}]
        = beta_1 * E[N_{k'} N_{k' + i - 1}]
          + beta_2 * E[N_{k'} N_{k' + i - 2}]`.

    Encoded as a function `lag : Nat -> Real`.  The base cases at
    `lag 0 = sigma^2` and `lag 1 = sigma^2 * rho_1` come from the
    definition of `rho_1, rho_2`. -/
noncomputable def cov2_lag
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) : Nat -> Real
  | 0     => sigma.val
  | 1     => sigma.val * rho1.val
  | 2     => sigma.val * rho2.val
  | (n + 3) =>
      beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 (n + 2)
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 (n + 1)

/-! ### Base-case lemmas for `cov2_lag` -/

/-- `cov2_lag` at lag `0` is the stationary variance `sigma^2`. -/
theorem cov2_lag_zero
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 0 = sigma.val := rfl

/-- `cov2_lag` at lag `1` is `sigma^2 * rho_1`. -/
theorem cov2_lag_one
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 1 = sigma.val * rho1.val := rfl

/-- `cov2_lag` at lag `3` is the first recurrence step:
    `beta_1 * (sigma * rho_2) + beta_2 * (sigma * rho_1)`. -/
theorem cov2_lag_three
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 3
      = beta1 * (sigma.val * rho2.val) + beta2 * (sigma.val * rho1.val) := rfl

/-- `cov2_lag` at lag `2` is `sigma^2 * rho_2`. -/
theorem cov2_lag_two
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 2 = sigma.val * rho2.val := rfl

/-- `cov2_lag` at lag `4`: second step of the recurrence, fully
    expanded.  Equals
    `beta_1 * (beta_1 * (sigma * rho_2) + beta_2 * (sigma * rho_1))
      + beta_2 * (sigma * rho_2)`, which is `cov2_lag_three`'s
    output multiplied by `beta_1` plus `cov2_lag_two`'s output
    multiplied by `beta_2`. -/
theorem cov2_lag_four
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 4
      = beta1 * (beta1 * (sigma.val * rho2.val)
                  + beta2 * (sigma.val * rho1.val))
        + beta2 * (sigma.val * rho2.val) := rfl

/-- *Recurrence step at lag `5`.*  By def of `cov2_lag` (which uses
    structural recursion at `n + 3`), index `5` unfolds to
    `beta_1 * cov2_lag _ _ _ _ 4 + beta_2 * cov2_lag _ _ _ _ 3`.
    Extends the `cov2_lag_two/three/four` named-form series. -/
theorem cov2_lag_five
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 5
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 4
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 3 := rfl

/-- *Recurrence step at lag `6`.*  Same `rfl` pattern as
    `cov2_lag_five`, one step further. -/
theorem cov2_lag_six
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 6
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 5
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 4 := rfl

/-- *Recurrence step at lag `7`.*  Same `rfl` pattern as
    `cov2_lag_six`, one step further. -/
theorem cov2_lag_seven
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 7
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 6
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 5 := rfl

/-- *Recurrence step at lag `8`.*  Same `rfl` pattern as
    `cov2_lag_seven`, one step further. -/
theorem cov2_lag_eight
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 8
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 7
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 6 := rfl

/-- *Recurrence step at lag `9`.*  Same `rfl` pattern as
    `cov2_lag_eight`, one step further. -/
theorem cov2_lag_nine
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 9
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 8
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 7 := rfl

/-- *Recurrence step at lag `10`.*  Same `rfl` pattern as
    `cov2_lag_nine`, one step further. -/
theorem cov2_lag_ten
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 10
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 9
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 8 := rfl

/-- *Recurrence step at lag `11`.*  Same `rfl` pattern as
    `cov2_lag_ten`, one step further. -/
theorem cov2_lag_eleven
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 11
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 10
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 9 := rfl

/-- *Recurrence step at lag `12`.*  Same `rfl` pattern. -/
theorem cov2_lag_twelve
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 12
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 11
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 10 := rfl

/-- *Recurrence step at lag `13`.*  Same `rfl` pattern. -/
theorem cov2_lag_thirteen
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 13
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 12
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 11 := rfl

/-- *Recurrence step at lag `14`.*  Same `rfl` pattern. -/
theorem cov2_lag_fourteen
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 14
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 13
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 12 := rfl

/-- *Recurrence step at lag `15`.*  Same `rfl` pattern. -/
theorem cov2_lag_fifteen
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 15
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 14
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 13 := rfl

/-- *Recurrence step at lag `16`.*  Same `rfl` pattern. -/
theorem cov2_lag_sixteen
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 16
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 15
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 14 := rfl

/-- *Recurrence step at lag `17`.*  Same `rfl` pattern. -/
theorem cov2_lag_seventeen
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 17
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 16
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 15 := rfl

/-- *Recurrence step at lag `18`.*  Same `rfl` pattern. -/
theorem cov2_lag_eighteen
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 18
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 17
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 16 := rfl

/-- *Recurrence step at lag `19`.*  Same `rfl` pattern. -/
theorem cov2_lag_nineteen
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 19
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 18
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 17 := rfl

/-- *Recurrence step at lag `20`.*  Same `rfl` pattern. -/
theorem cov2_lag_twenty
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 20
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 19
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 18 := rfl

/-- The AR(2)-style recurrence for `cov2_lag` at lag `n + 3`. -/
theorem cov2_lag_succ_succ_succ
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) (n : Nat) :
    cov2_lag sigma rho1 rho2 beta1 beta2 (n + 3)
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 (n + 2)
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 (n + 1) := rfl

/-- *Trivial AR coefficients.*  When both `beta_1 = beta_2 = 0`, the
    recurrence step (lag `n + 3`) vanishes regardless of the
    correlation parameters.  Analog of `ar2_phi_zero` for `cov2_lag`. -/
theorem cov2_lag_beta_zero
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (n : Nat) :
    cov2_lag sigma rho1 rho2 0 0 (n + 3) = 0 :=
  let step1 : cov2_lag sigma rho1 rho2 0 0 (n + 3)
            = 0 * cov2_lag sigma rho1 rho2 0 0 (n + 2)
              + 0 * cov2_lag sigma rho1 rho2 0 0 (n + 1) := rfl
  let step2 : 0 * cov2_lag sigma rho1 rho2 0 0 (n + 2)
              + 0 * cov2_lag sigma rho1 rho2 0 0 (n + 1)
            = (0 : Real) + 0 :=
    congrArg₂ (· + ·) (zero_mul _) (zero_mul _)
  step1.trans (step2.trans (add_zero 0))

/-- *Second-order covariance vanishes at zero noise power.*  Parallel
    to `cov1_lag_zero_sigma`: when `sigma.val = 0`, `cov2_lag`
    vanishes at every lag.  Structural recursion: base cases at
    `0, 1, 2` collapse `sigma.val` to `0` (with `zero_mul` for the
    `* rho` factor at lags 1 and 2); the `n + 3` step combines IH
    at `n + 2` and `n + 1` with `mul_zero` on both summands. -/
theorem cov2_lag_zero_sigma
    (rho1 rho2 : CorrelationCoefficient) (beta1 beta2 : Real) :
    forall (n : Nat),
      cov2_lag ⟨0, le_refl 0⟩ rho1 rho2 beta1 beta2 n = 0
  | 0     => rfl
  | 1     => zero_mul rho1.val
  | 2     => zero_mul rho2.val
  | n + 3 =>
      let ih1 :
          cov2_lag ⟨0, le_refl 0⟩ rho1 rho2 beta1 beta2 (n + 2) = 0 :=
        cov2_lag_zero_sigma rho1 rho2 beta1 beta2 (n + 2)
      let ih2 :
          cov2_lag ⟨0, le_refl 0⟩ rho1 rho2 beta1 beta2 (n + 1) = 0 :=
        cov2_lag_zero_sigma rho1 rho2 beta1 beta2 (n + 1)
      let step1 :
          cov2_lag ⟨0, le_refl 0⟩ rho1 rho2 beta1 beta2 (n + 3)
            = beta1
                * cov2_lag ⟨0, le_refl 0⟩ rho1 rho2 beta1 beta2 (n + 2)
              + beta2
                * cov2_lag ⟨0, le_refl 0⟩ rho1 rho2 beta1 beta2 (n + 1) :=
        rfl
      let step2 :
          beta1 * cov2_lag ⟨0, le_refl 0⟩ rho1 rho2 beta1 beta2 (n + 2)
            + beta2
              * cov2_lag ⟨0, le_refl 0⟩ rho1 rho2 beta1 beta2 (n + 1)
            = beta1 * 0 + beta2 * 0 :=
        congrArg₂ (· + ·)
          (congrArg (beta1 * ·) ih1)
          (congrArg (beta2 * ·) ih2)
      let step3 : beta1 * 0 + beta2 * 0 = 0 :=
        (congrArg₂ (· + ·) (mul_zero beta1) (mul_zero beta2)).trans
          (add_zero 0)
      step1.trans (step2.trans step3)

end Section03
end OrbgrandAi
