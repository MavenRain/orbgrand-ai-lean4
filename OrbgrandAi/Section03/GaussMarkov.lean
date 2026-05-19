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

    *Placeholder shape.*  The algebraic manipulation is routine but
    has to be conducted via kan-tactics rewrites; scheduled for a
    follow-up. -/
theorem yuleWalker_implies_rho1_sq_bound_statement
    (rho1 rho2 : CorrelationCoefficient) :
    yuleWalker_variance_bound rho1 rho2 ->
      yuleWalker_rho1_sq_bound rho1 rho2 -> True := by
  kan_intro _h1
  kan_intro _h2
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

end Section03
end OrbgrandAi
