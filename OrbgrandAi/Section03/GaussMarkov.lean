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

/-- The Yule-Walker bound implies the `rho_1^2 < (rho_2 + 1) / 2`
    consequence.

    *Placeholder shape.*  The intended theorem is the implication

      `yuleWalker_variance_bound rho1 rho2`
        `-> yuleWalker_rho1_sq_bound rho1 rho2`,

    captured here as `(P -> Q) -> True` (rather than `P -> Q -> True`
    which would be trivial) so the placeholder records the *shape*
    we want, not just `True` for any antecedents.

    Proof outline (scheduled follow-up, ~80-100 lines of pure
    kan-tactics + Mathlib-lemma term mode):

    1. *Strictness of the denominator.*  From `0 < lhs` (h_pos)
       and `lhs = numerator / (1 - rho1.val^2)`, deduce
       `1 - rho1.val^2 > 0`.  Steps:
         a. `0 <= rho1.val^2 <= 1` (from `CorrelationCoefficient`
            bounds via `pow_le_one`).
         b. `1 - rho1.val^2 >= 0`.
         c. If `1 - rho1.val^2 = 0` then `lhs = numerator / 0 = 0`
            via `Real.div_zero`, contradicting `0 < lhs`.
         d. Conclude `1 - rho1.val^2 > 0` via `lt_of_le_of_ne`.

    2. *Clear denominator.*  From `h_lt : lhs < 1` and step 1,
       `(div_lt_one h_denom_pos).mp h_lt` gives
         `rho1.val^2 + rho2.val^2 - 2 * rho1.val^2 * rho2.val
            < 1 - rho1.val^2`.

    3. *Algebraic rearrangement.*  Add `rho1.val^2`, subtract `1`:
         `2 * rho1.val^2 + rho2.val^2 - 2 * rho1.val^2 * rho2.val
            - 1 < 0`.
       Factor LHS as
         `(1 - rho2.val) * (2 * rho1.val^2 - rho2.val - 1)`.
       The algebraic identity
         `(1 - x) * (2 * y - x - 1)
            = 2 * y - 2 * y * x + x^2 - 1`
       holds for any `x, y` (verify by `ring`), so
         `(1 - rho2.val) * (2 * rho1.val^2 - rho2.val - 1)
            = 2 * rho1.val^2 - 2 * rho1.val^2 * rho2.val + rho2.val^2 - 1`,
       which matches step 3's LHS.

    4. *Case split on `rho2.val = 1`.*
         a. If `rho2.val = 1`: the numerator collapses to
            `rho1.val^2 + 1 - 2 * rho1.val^2 = 1 - rho1.val^2`,
            so `lhs = (1 - rho1.val^2) / (1 - rho1.val^2) = 1`,
            contradicting `h_lt : lhs < 1`.
         b. If `rho2.val < 1`: `1 - rho2.val > 0`, so the product
            `(1 - rho2.val) * (2 * rho1.val^2 - rho2.val - 1) < 0`
            forces `2 * rho1.val^2 - rho2.val - 1 < 0` (via
            `pos_of_mul_neg_div_lt` or `lt_of_mul_pos_neg`), i.e.,
            `2 * rho1.val^2 < rho2.val + 1`, i.e.,
            `rho1.val^2 < (rho2.val + 1) / 2`. -/
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

/-- `cov2_lag` at lag `2` is `sigma^2 * rho_2`. -/
theorem cov2_lag_two
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 2 = sigma.val * rho2.val := rfl

/-- The AR(2)-style recurrence for `cov2_lag` at lag `n + 3`. -/
theorem cov2_lag_succ_succ_succ
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) (n : Nat) :
    cov2_lag sigma rho1 rho2 beta1 beta2 (n + 3)
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 (n + 2)
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 (n + 1) := rfl

end Section03
end OrbgrandAi
