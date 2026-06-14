import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section03.GaussMarkov
import OrbgrandAi.Section03.Determinant
import KanTactics

/-!
# Section III.  Differential entropy rates

Formalizes the normalised differential entropy rates from Section III
of the paper.

## First-order Gauss-Markov

Eq. (9.34) of Cover-Thomas, restated by the paper as

  H_rate(N^{n_s}) = log(2 * e * pi) + (1 / n_s) * log |C_N^{n_s x n_s}|
                  = log(2 * e * pi * sigma_N^2)
                    + (1 - 1 / n_s) * log(1 - rho^2).

The last term `(1 - 1/n_s) log(1 - rho^2) < 0` for `rho > 0`
quantifies the entropy decrease due to correlation.  In the
asymptotic limit `n_s -> infinity`,

  lim H_rate = log(2 * e * pi * sigma_N^2 * (1 - rho^2)).

## Block-`b` approximation

If we treat the noise as block-independent (blocks of size `b`,
independent across blocks), the corresponding normalised entropy
rate is

  H_block_rate(N) = log(2 * e * pi * sigma_N^2)
                  + (1 - 1 / b) * log(1 - rho^2).

For `b = 2` we already recover more than half of the
asymptotic-`n_s` reduction, which is the paper's empirical
justification for ORBGRAND-AI using small `b`.

## Second-order Gauss-Markov

Substituting `cov2DetFormula` for `|C_N|` gives, for `n_s >= 4`,

  H_rate2(N^{n_s}) = (1/2) * log(2 * pi * e * sigma_N^2)
                   + (1 / (2 * n_s))
                       * log( - (rho_2 - 1)^{n_s - 2}
                              * (1 - 2 * rho_1^2 + rho_2)^{n_s - 2}
                              / (rho_1^2 - 1)^{n_s - 3} ).

Following the paper we expose all of these as explicit Lean
definitions and state the equational characterisations as
placeholder theorems.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section03

open OrbgrandAi.Section02

/-! ## First-order entropy rate -/

/-- Normalised differential entropy rate of a stationary first-order
    Gauss-Markov process of variance `sigma^2` and correlation
    `rho`, for a block of length `n_s >= 1`. -/
noncomputable def entropyRate1
    (sigma : NoisePower) (rho : CorrelationCoefficient) (n_s : Nat) : Real :=
  Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
    + (1 - (1 : Real) / (n_s : Real)) * Real.log (1 - rho.val ^ 2)

/-- Asymptotic entropy rate (limit as `n_s -> infinity`). -/
noncomputable def entropyRate1_asymp
    (sigma : NoisePower) (rho : CorrelationCoefficient) : Real :=
  Real.log (2 * Real.exp 1 * Real.pi * sigma.val * (1 - rho.val ^ 2))

/-- Block-`b` approximation: noise treated as independent across
    blocks of size `b`, fully correlated within each block. -/
noncomputable def entropyRate1_block
    (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) : Real :=
  Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
    + (1 - (1 : Real) / (b.toNat : Real)) * Real.log (1 - rho.val ^ 2)

/-! ## Second-order entropy rate -/

/-- Normalised differential entropy rate of a stationary second-order
    Gauss-Markov process for `n_s >= 4`, computed using
    `cov2DetFormula`.  The `1/2` factor matches the paper's
    convention (Section III, right column). -/
noncomputable def entropyRate2
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) : Real :=
  let r1 := rho1.val
  let r2 := rho2.val
  (1 / 2 : Real) * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
    + (1 / (2 * (n_s : Real)))
        * Real.log
            (- (r2 - 1) ^ (n_s - 2)
                * (1 - 2 * r1 ^ 2 + r2) ^ (n_s - 2)
              / (r1 ^ 2 - 1) ^ (n_s - 3))

/-! ## Equational characterisations (placeholders) -/

/-- The entropy-rate formula for a first-order Gauss-Markov process
    follows from the closed form of the auto-covariance determinant
    via the standard Gaussian entropy formula
    `H = log(2 e pi) + (1/n) log |C|`.

    Stated as a definitional rewrite; the proof is `rfl` because
    `entropyRate1` is defined to be exactly the right-hand side. -/
theorem entropyRate1_eq
    (sigma : NoisePower) (rho : CorrelationCoefficient) (n_s : Nat) :
    entropyRate1 sigma rho n_s
      = Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
        + (1 - (1 : Real) / (n_s : Real))
            * Real.log (1 - rho.val ^ 2) := rfl

/-- *Symmetric form of `entropyRate1_eq`.*  The explicit log
    expression equals `entropyRate1 sigma rho n_s`.  `.symm` of
    `entropyRate1_eq`. -/
theorem entropyRate1_eq_symm
    (sigma : NoisePower) (rho : CorrelationCoefficient) (n_s : Nat) :
    Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
      + (1 - (1 : Real) / (n_s : Real))
          * Real.log (1 - rho.val ^ 2)
      = entropyRate1 sigma rho n_s :=
  (entropyRate1_eq sigma rho n_s).symm

/-- The block-`b` entropy rate is asymptotic-`n_s -> infinity` with
    `n_s` replaced by `b`: the correlation contribution is captured
    only within blocks of size `b`, with no cross-block term.

    Definitional. -/
theorem entropyRate1_block_eq
    (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    entropyRate1_block sigma rho b
      = Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
        + (1 - (1 : Real) / (b.toNat : Real))
            * Real.log (1 - rho.val ^ 2) := rfl

/-- *Symmetric form of `entropyRate1_block_eq`.*  The explicit log
    expression equals `entropyRate1_block sigma rho b`.  `.symm`
    of `entropyRate1_block_eq`. -/
theorem entropyRate1_block_eq_symm
    (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
      + (1 - (1 : Real) / (b.toNat : Real))
          * Real.log (1 - rho.val ^ 2)
      = entropyRate1_block sigma rho b :=
  (entropyRate1_block_eq sigma rho b).symm

/-- *Asymptotic entropy rate unfolding.*  `entropyRate1_asymp` is the
    log of `2 * e * pi * sigma^2 * (1 - rho^2)`, the limit form. -/
theorem entropyRate1_asymp_eq
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    entropyRate1_asymp sigma rho
      = Real.log (2 * Real.exp 1 * Real.pi * sigma.val
                  * (1 - rho.val ^ 2)) := rfl

/-- *Symmetric form of `entropyRate1_asymp_eq`.*  The closed-form
    log expression equals `entropyRate1_asymp`.  The `.symm` of
    `entropyRate1_asymp_eq`, useful for rewriting from the
    explicit log form back into the abbreviation. -/
theorem log_eq_entropyRate1_asymp
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    Real.log (2 * Real.exp 1 * Real.pi * sigma.val
              * (1 - rho.val ^ 2))
      = entropyRate1_asymp sigma rho :=
  (entropyRate1_asymp_eq sigma rho).symm

/-- *Entropy rate matches block form when n_s = b.toNat.*  The
    `entropyRate1` and `entropyRate1_block` formulas coincide
    definitionally when the block size equals the sequence length. -/
theorem entropyRate1_eq_block
    (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    entropyRate1 sigma rho b.toNat = entropyRate1_block sigma rho b := rfl

/-- *Symmetric form of `entropyRate1_eq_block`.*  The block-`b`
    entropy rate equals the `entropyRate1` formula evaluated at the
    sequence length `b.toNat`.  Just the `.symm` of
    `entropyRate1_eq_block`. -/
theorem entropyRate1_block_eq_entropyRate1
    (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    entropyRate1_block sigma rho b = entropyRate1 sigma rho b.toNat :=
  (entropyRate1_eq_block sigma rho b).symm

/-- *Closed-form chain.*  Two-step composition of
    `entropyRate1_eq_block` (collapse to the `entropyRate1_block`
    abbreviation) and `entropyRate1_block_eq` (unfold to the log
    form), giving the explicit log expression for
    `entropyRate1 sigma rho b.toNat`. -/
theorem entropyRate1_at_block_eq_log_form
    (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    entropyRate1 sigma rho b.toNat
      = Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
        + (1 - (1 : Real) / (b.toNat : Real))
            * Real.log (1 - rho.val ^ 2) :=
  (entropyRate1_eq_block sigma rho b).trans
    (entropyRate1_block_eq sigma rho b)

/-- *Symmetric form of `entropyRate1_at_block_eq_log_form`.*  The
    explicit log expression equals `entropyRate1 sigma rho b.toNat`.
    `.symm`, useful for rewriting from the closed log form back. -/
theorem entropyRate1_at_block_eq_log_form_symm
    (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
      + (1 - (1 : Real) / (b.toNat : Real))
          * Real.log (1 - rho.val ^ 2)
      = entropyRate1 sigma rho b.toNat :=
  (entropyRate1_at_block_eq_log_form sigma rho b).symm

/-- *Closed-form chain via the block route.*  Composes
    `entropyRate1_block_eq_entropyRate1` with
    `entropyRate1_at_block_eq_log_form` to unfold
    `entropyRate1_block` directly to the explicit log form. -/
theorem entropyRate1_block_at_block_eq_log_form
    (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    entropyRate1_block sigma rho b
      = Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
        + (1 - (1 : Real) / (b.toNat : Real))
            * Real.log (1 - rho.val ^ 2) :=
  (entropyRate1_block_eq_entropyRate1 sigma rho b).trans
    (entropyRate1_at_block_eq_log_form sigma rho b)

/-- The second-order entropy rate matches the substitution of
    `cov2DetFormula` into the Gaussian entropy formula.

    Definitional. -/
theorem entropyRate2_eq
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (n_s : Nat) :
    entropyRate2 sigma rho1 rho2 n_s
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * (n_s : Real)))
            * Real.log
                (- (rho2.val - 1) ^ (n_s - 2)
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (n_s - 2)
                  / (rho1.val ^ 2 - 1) ^ (n_s - 3)) := rfl

/-- *Symmetric form of `entropyRate2_eq`.*  The explicit log
    expression equals `entropyRate2 sigma rho1 rho2 n_s`.  `.symm`
    of `entropyRate2_eq`. -/
theorem entropyRate2_eq_symm
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (n_s : Nat) :
    (1 / 2 : Real)
        * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
      + (1 / (2 * (n_s : Real)))
          * Real.log
              (- (rho2.val - 1) ^ (n_s - 2)
                  * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (n_s - 2)
                / (rho1.val ^ 2 - 1) ^ (n_s - 3))
      = entropyRate2 sigma rho1 rho2 n_s :=
  (entropyRate2_eq sigma rho1 rho2 n_s).symm

end Section03
end OrbgrandAi
