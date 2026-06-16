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

/-- *Symmetric form of `entropyRate1_block_at_block_eq_log_form`.* -/
theorem entropyRate1_block_at_block_eq_log_form_symm
    (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
      + (1 - (1 : Real) / (b.toNat : Real))
          * Real.log (1 - rho.val ^ 2)
      = entropyRate1_block sigma rho b :=
  (entropyRate1_block_at_block_eq_log_form sigma rho b).symm

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

/-- *Boundary case `n_s = 4` of `entropyRate2`.*  The paper specifies
    the second-order entropy-rate formula for `n_s >= 4`; pinning the
    formula at the boundary value `n_s = 4` reduces the abstract
    `n_s - 2` and `n_s - 3` exponents to `2` and `1`, giving the
    paper's minimal-sequence closed form.  Specialisation of
    `entropyRate2_eq` at `n_s = 4`; reduces by Nat computation. -/
theorem entropyRate2_at_four_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 4
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((4 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 2
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 2
                  / (rho1.val ^ 2 - 1) ^ 1) :=
  entropyRate2_eq sigma rho1 rho2 4

/-- *Boundary case `n_s = 5` of `entropyRate2`.*  Companion of
    `entropyRate2_at_four_eq_log_form`: pinning the second-order
    entropy-rate formula at `n_s = 5` reduces the abstract `n_s - 2`
    and `n_s - 3` exponents to `3` and `2`, giving the next paper
    boundary case above the minimal sequence length.  Specialisation
    of `entropyRate2_eq` at `n_s = 5`; reduces by Nat computation. -/
theorem entropyRate2_at_five_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 5
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((5 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 3
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 3
                  / (rho1.val ^ 2 - 1) ^ 2) :=
  entropyRate2_eq sigma rho1 rho2 5

/-- *Boundary case `n_s = 6` of `entropyRate2`.*  Companion of
    `entropyRate2_at_four_eq_log_form` and
    `entropyRate2_at_five_eq_log_form`: pinning the second-order
    entropy-rate formula at `n_s = 6` reduces the abstract `n_s - 2`
    and `n_s - 3` exponents to `4` and `3`.  Specialisation of
    `entropyRate2_eq` at `n_s = 6`; reduces by Nat computation. -/
theorem entropyRate2_at_six_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 6
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((6 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 4
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 4
                  / (rho1.val ^ 2 - 1) ^ 3) :=
  entropyRate2_eq sigma rho1 rho2 6

/-- *Boundary case `n_s = 7` of `entropyRate2`.*  Companion of
    the `n_s = 4`, `5`, `6` variants.  Specialisation of
    `entropyRate2_eq` at `n_s = 7`; reduces by Nat computation. -/
theorem entropyRate2_at_seven_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 7
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((7 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 5
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 5
                  / (rho1.val ^ 2 - 1) ^ 4) :=
  entropyRate2_eq sigma rho1 rho2 7

/-- *Boundary case `n_s = 8` of `entropyRate2`.*  Companion of the
    `n_s = 4`-`7` variants.  Specialisation of `entropyRate2_eq` at
    `n_s = 8`; reduces by Nat computation. -/
theorem entropyRate2_at_eight_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 8
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((8 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 6
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 6
                  / (rho1.val ^ 2 - 1) ^ 5) :=
  entropyRate2_eq sigma rho1 rho2 8

/-- *Boundary case `n_s = 9` of `entropyRate2`.*  Companion of the
    `n_s = 4`-`8` variants.  Specialisation of `entropyRate2_eq` at
    `n_s = 9`; reduces by Nat computation. -/
theorem entropyRate2_at_nine_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 9
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((9 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 7
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 7
                  / (rho1.val ^ 2 - 1) ^ 6) :=
  entropyRate2_eq sigma rho1 rho2 9

/-- *Boundary case `n_s = 10` of `entropyRate2`.*  Companion of the
    `n_s = 4`-`9` variants.  Specialisation of `entropyRate2_eq` at
    `n_s = 10`; reduces by Nat computation. -/
theorem entropyRate2_at_ten_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 10
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((10 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 8
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 8
                  / (rho1.val ^ 2 - 1) ^ 7) :=
  entropyRate2_eq sigma rho1 rho2 10

/-- *Boundary case `n_s = 11` of `entropyRate2`.*  Companion of the
    `n_s = 4`-`10` variants.  Specialisation of `entropyRate2_eq` at
    `n_s = 11`; reduces by Nat computation. -/
theorem entropyRate2_at_eleven_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 11
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((11 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 9
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 9
                  / (rho1.val ^ 2 - 1) ^ 8) :=
  entropyRate2_eq sigma rho1 rho2 11

/-- *Boundary case `n_s = 12` of `entropyRate2`.*  Companion of the
    `n_s = 4`-`11` variants.  Specialisation of `entropyRate2_eq` at
    `n_s = 12`; reduces by Nat computation. -/
theorem entropyRate2_at_twelve_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 12
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((12 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 10
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 10
                  / (rho1.val ^ 2 - 1) ^ 9) :=
  entropyRate2_eq sigma rho1 rho2 12

/-- *Boundary case `n_s = 13` of `entropyRate2`.*  Companion of the
    `n_s = 4`-`12` variants.  Specialisation of `entropyRate2_eq` at
    `n_s = 13`; reduces by Nat computation. -/
theorem entropyRate2_at_thirteen_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 13
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((13 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 11
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 11
                  / (rho1.val ^ 2 - 1) ^ 10) :=
  entropyRate2_eq sigma rho1 rho2 13

/-- *Boundary case `n_s = 14` of `entropyRate2`.*  Companion of the
    `n_s = 4`-`13` variants.  Specialisation of `entropyRate2_eq` at
    `n_s = 14`; reduces by Nat computation. -/
theorem entropyRate2_at_fourteen_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 14
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((14 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 12
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 12
                  / (rho1.val ^ 2 - 1) ^ 11) :=
  entropyRate2_eq sigma rho1 rho2 14

/-- *Boundary case `n_s = 15` of `entropyRate2`.*  Companion of the
    `n_s = 4`-`14` variants.  Specialisation of `entropyRate2_eq` at
    `n_s = 15`; reduces by Nat computation. -/
theorem entropyRate2_at_fifteen_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 15
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((15 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 13
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 13
                  / (rho1.val ^ 2 - 1) ^ 12) :=
  entropyRate2_eq sigma rho1 rho2 15

/-- *Boundary case `n_s = 16` of `entropyRate2`.*  Companion of the
    `n_s = 4`-`15` variants.  Specialisation of `entropyRate2_eq` at
    `n_s = 16`; reduces by Nat computation. -/
theorem entropyRate2_at_sixteen_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 16
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((16 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 14
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 14
                  / (rho1.val ^ 2 - 1) ^ 13) :=
  entropyRate2_eq sigma rho1 rho2 16

/-- *Boundary case `n_s = 17` of `entropyRate2`.*  Companion of the
    `n_s = 4`-`16` variants.  Specialisation of `entropyRate2_eq` at
    `n_s = 17`; reduces by Nat computation. -/
theorem entropyRate2_at_seventeen_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 17
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((17 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 15
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 15
                  / (rho1.val ^ 2 - 1) ^ 14) :=
  entropyRate2_eq sigma rho1 rho2 17

/-- *Boundary case `n_s = 18` of `entropyRate2`.*  Companion of the
    `n_s = 4`-`17` variants.  Specialisation of `entropyRate2_eq` at
    `n_s = 18`; reduces by Nat computation. -/
theorem entropyRate2_at_eighteen_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 18
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((18 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 16
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 16
                  / (rho1.val ^ 2 - 1) ^ 15) :=
  entropyRate2_eq sigma rho1 rho2 18

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

/-- *Closed-form unfolding of `entropyRate2` evaluated at a block
    size.*  Specialisation of `entropyRate2_eq` to the sequence
    length `b.toNat`.  Definitional. -/
theorem entropyRate2_at_block_eq_log_form
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (b : BlockSize) :
    entropyRate2 sigma rho1 rho2 b.toNat
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * (b.toNat : Real)))
            * Real.log
                (- (rho2.val - 1) ^ (b.toNat - 2)
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (b.toNat - 2)
                  / (rho1.val ^ 2 - 1) ^ (b.toNat - 3)) :=
  entropyRate2_eq sigma rho1 rho2 b.toNat

/-- *Symmetric form of `entropyRate2_at_block_eq_log_form`.* -/
theorem entropyRate2_at_block_eq_log_form_symm
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (b : BlockSize) :
    (1 / 2 : Real)
        * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
      + (1 / (2 * (b.toNat : Real)))
          * Real.log
              (- (rho2.val - 1) ^ (b.toNat - 2)
                  * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (b.toNat - 2)
                / (rho1.val ^ 2 - 1) ^ (b.toNat - 3))
      = entropyRate2 sigma rho1 rho2 b.toNat :=
  entropyRate2_eq_symm sigma rho1 rho2 b.toNat

end Section03
end OrbgrandAi
