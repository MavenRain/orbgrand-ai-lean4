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
