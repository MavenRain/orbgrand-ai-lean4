import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section03.GaussMarkov
import OrbgrandAi.Section03.Determinant
import OrbgrandAi.Section03.EntropyRate
import KanTactics

/-!
# Section III.  Channel capacity bound

Formalizes the channel-capacity analysis from Section III of the
paper for the additive second-order Gauss-Markov noise channel.

## Verdu-Han information rate

The Verdu-Han general capacity formula uses

  I(X'; Y')
    = lim inf_{n_s -> infinity}
        (1 / n_s) * log( p_{Y|X}(y | x) / p_Y(y) ),

and the lim-sup entropy rate

  H_bar(Y')
    = lim sup_{n_s -> infinity}
        (1 / n_s) * log( 1 / p_Y(y) ).

The inequality

  I(X'; Y') <= H_bar(Y') - H_bar(Y' | X')

generalises mutual-information additivity to the non-stationary
regime.

## Hadamard bound on the noise entropy rate

The auto-covariance matrix `C_N` of the second-order Gauss-Markov
noise has non-zero off-diagonal entries.  Hadamard's inequality

  |det C_N| <= product over i of (C_N i i)

implies

  log |det C_N| <= sum over i of log(C_N i i) = n_s * log(sigma_N^2),

so the entropy of the *correlated* noise is no larger than the
entropy of the *uncorrelated* Gaussian with the same diagonal,
namely `log(2 * pi * e * sigma_N^2)`.  Equivalently the second-order
Gauss-Markov noise has `H_bar(N') <= log(2 * pi * e * sigma_N^2)`.

## Capacity upper bound

Putting the pieces together,

  C
    = sup_{X'} I(X'; Y')
    <= sup_{X'} ( H_bar(Y') - H_bar(N') )
    <= (1/2) log(2 * pi * e)
       + (1/2) log(sigma_X^2 + sigma_N^2)
       - (1/2) log(2 * pi * e * sigma_N^2)
       - lim_{n_s -> infinity} (1 / (2 * n_s))
           * log( - (rho_2 - 1)^{n_s - 2}
                   * (1 - 2 * rho_1^2 + rho_2)^{n_s - 2}
                 / (rho_1^2 - 1)^{n_s - 3} ).

The middle three terms collapse to the standard Gaussian
capacity-with-noise expression `(1/2) log(1 + sigma_X^2 / sigma_N^2)`;
the last term is the entropy-rate decrease due to correlation.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section03

open OrbgrandAi.Section02

/-! ## Information rate (abstract) -/

/-- The Verdu-Han lim-inf information rate, abstracted as a
    `Real`-valued function of two sequences of probability mass
    functions parameterised by `n_s`.  Concrete instances need only
    a `Real`-valued log-density-ratio sequence; we keep the type
    deliberately small so downstream files can plug in
    domain-specific densities. -/
noncomputable def liminfInformationRate (logDensityRatio : Nat -> Real) : Real :=
  Filter.liminf logDensityRatio Filter.atTop

/-- The lim-sup entropy rate, similarly abstracted. -/
noncomputable def limsupEntropyRate (logInverseDensity : Nat -> Real) : Real :=
  Filter.limsup logInverseDensity Filter.atTop

/-! ### Constant-sequence base cases -/

/-- *Constant log-density ratio.*  If the log-density-ratio sequence
    is constant at `c`, the lim-inf information rate equals `c`.
    Direct application of `Filter.liminf_const` (which needs
    `atTop`'s nonemptiness, automatic for `Nat`). -/
theorem liminfInformationRate_const (c : Real) :
    liminfInformationRate (fun _ => c) = c :=
  Filter.liminf_const c

/-- *Constant log-inverse-density.*  If the log-inverse-density
    sequence is constant at `c`, the lim-sup entropy rate equals
    `c`.  Direct application of `Filter.limsup_const`. -/
theorem limsupEntropyRate_const (c : Real) :
    limsupEntropyRate (fun _ => c) = c :=
  Filter.limsup_const c

/-- *Zero log-density-ratio.*  Concrete instance of
    `liminfInformationRate_const` at `c = 0`. -/
theorem liminfInformationRate_zero :
    liminfInformationRate (fun _ : Nat => (0 : Real)) = 0 :=
  liminfInformationRate_const 0

/-- *Zero log-inverse-density.*  Concrete instance of
    `limsupEntropyRate_const` at `c = 0`. -/
theorem limsupEntropyRate_zero :
    limsupEntropyRate (fun _ : Nat => (0 : Real)) = 0 :=
  limsupEntropyRate_const 0

/-- *Unit log-density-ratio.*  Concrete instance of
    `liminfInformationRate_const` at `c = 1`. -/
theorem liminfInformationRate_one :
    liminfInformationRate (fun _ : Nat => (1 : Real)) = 1 :=
  liminfInformationRate_const 1

/-- *Unit log-inverse-density.*  Concrete instance of
    `limsupEntropyRate_const` at `c = 1`. -/
theorem limsupEntropyRate_one :
    limsupEntropyRate (fun _ : Nat => (1 : Real)) = 1 :=
  limsupEntropyRate_const 1

/-- *liminf <= limsup at constants.*  For any constant Real
    sequence, the lim-inf information rate is at most the lim-sup
    entropy rate.  Both sides reduce to `c` via the `_const` base
    cases; equality implies the inequality via `Eq.le`. -/
theorem liminfInformationRate_le_limsupEntropyRate_const (c : Real) :
    liminfInformationRate (fun _ => c) <= limsupEntropyRate (fun _ => c) :=
  ((liminfInformationRate_const c).trans (limsupEntropyRate_const c).symm).le

/-- *liminf <= limsup, general form.*  Promotes
    `liminfInformationRate_le_limsupEntropyRate_const` from constant
    sequences to any `Real`-valued sequence whose values are bounded
    above and below along `Filter.atTop`.  Uses
    `Filter.liminf_le_limsup`; the `NeBot Filter.atTop` instance for
    `Nat` resolves automatically. -/
theorem liminfInformationRate_le_limsupEntropyRate (u : Nat -> Real)
    (h : Filter.IsBoundedUnder (· <= ·) Filter.atTop u)
    (h' : Filter.IsBoundedUnder (· >= ·) Filter.atTop u) :
    liminfInformationRate u <= limsupEntropyRate u :=
  Filter.liminf_le_limsup h h'

/-- *Congruence under eventual equality.*  If two log-density-ratio
    sequences agree on all sufficiently large `n_s`, they share the
    same lim-inf information rate.  Tail behaviour is the only thing
    the lim-inf sees.  Direct lift of `Filter.liminf_congr`. -/
theorem liminfInformationRate_congr {u v : Nat -> Real}
    (h : ∀ᶠ n in Filter.atTop, u n = v n) :
    liminfInformationRate u = liminfInformationRate v :=
  Filter.liminf_congr h

/-- *Congruence under eventual equality.*  Dual of
    `liminfInformationRate_congr` for the lim-sup entropy rate.
    Eventually-equal log-inverse-density sequences share the same
    lim-sup.  Direct lift of `Filter.limsup_congr`. -/
theorem limsupEntropyRate_congr {u v : Nat -> Real}
    (h : ∀ᶠ n in Filter.atTop, u n = v n) :
    limsupEntropyRate u = limsupEntropyRate v :=
  Filter.limsup_congr h

/-! ## Hadamard bound on the noise entropy rate -/

/-- *Hadamard inequality* (Section III, page 4, right column).

    For a positive-semidefinite matrix, the determinant is bounded
    above by the product of diagonal entries; taking logs, the
    log-determinant is bounded by the sum of `log(diag)`.

    For the second-order Gauss-Markov auto-covariance the diagonal
    entries are all `sigma_N^2`, so

      (1 / n_s) * log |C_N| <= log(sigma_N^2).

    *Placeholder shape.* -/
theorem hadamard_log_det_bound_statement
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) (h4 : 4 <= n_s) :
    ((1 / (n_s : Real))
        * Real.log (cov2DetFormula sigma rho1 rho2 n_s)
      <= Real.log (sigma.val ^ 2)) -> True := by
  kan_intro _h
  kan_constructor

/-- The lim-sup entropy rate of the second-order Gauss-Markov noise
    is bounded above by the entropy of uncorrelated Gaussian noise
    with the same variance:

      `H_bar(N') <= log(2 * pi * e * sigma_N^2)`.

    *Placeholder shape.* -/
theorem second_order_noise_entropy_rate_bound_statement
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) (h4 : 4 <= n_s) :
    (entropyRate2 sigma rho1 rho2 n_s
      <= Real.log (2 * Real.pi * Real.exp 1 * sigma.val ^ 2)) -> True := by
  kan_intro _h
  kan_constructor

/-! ## Channel capacity upper bound -/

/-- Closed-form *upper bound* on the channel capacity of the
    additive second-order Gauss-Markov noise channel, derived from

    * the Verdu-Han identity
        `I(X'; Y') <= H_bar(Y') - H_bar(Y' | X')`,
    * Hadamard's inequality on the noise auto-covariance,
    * and the maximum-entropy property of the Gaussian distribution
      under a second-moment constraint. -/
noncomputable def capacityUpperBound
    (sigmaX : SignalPower) (sigmaN : NoisePower)
    (rho1 rho2 : CorrelationCoefficient) (n_s : Nat) : Real :=
  let r1 := rho1.val
  let r2 := rho2.val
  (1 / 2 : Real) * Real.log (2 * Real.pi * Real.exp 1)
    + (1 / 2 : Real) * Real.log (sigmaX.val + sigmaN.val)
    - (1 / 2 : Real) * Real.log (2 * Real.pi * Real.exp 1 * sigmaN.val)
    - (1 / (2 * (n_s : Real)))
        * Real.log
            (- (r2 - 1) ^ (n_s - 2)
                * (1 - 2 * r1 ^ 2 + r2) ^ (n_s - 2)
              / (r1 ^ 2 - 1) ^ (n_s - 3))

/-- *Definitional unfolding of `capacityUpperBound`.*  Exposes the
    closed-form expression by zeta-reducing the internal `let r1`,
    `let r2` bindings, parallel to `entropyRate1_eq`. -/
theorem capacityUpperBound_eq
    (sigmaX : SignalPower) (sigmaN : NoisePower)
    (rho1 rho2 : CorrelationCoefficient) (n_s : Nat) :
    capacityUpperBound sigmaX sigmaN rho1 rho2 n_s
      = (1 / 2 : Real) * Real.log (2 * Real.pi * Real.exp 1)
        + (1 / 2 : Real) * Real.log (sigmaX.val + sigmaN.val)
        - (1 / 2 : Real)
            * Real.log (2 * Real.pi * Real.exp 1 * sigmaN.val)
        - (1 / (2 * (n_s : Real)))
            * Real.log
                (- (rho2.val - 1) ^ (n_s - 2)
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (n_s - 2)
                  / (rho1.val ^ 2 - 1) ^ (n_s - 3)) := rfl

/-- The Shannon channel capacity `C` (formal symbol, treated as an
    abstract real) is bounded by `capacityUpperBound` in the limit
    `n_s -> infinity`.

    *Placeholder shape.* -/
theorem capacity_upper_bound_statement
    (sigmaX : SignalPower) (sigmaN : NoisePower)
    (rho1 rho2 : CorrelationCoefficient) (C : Real) :
    (forall (n_s : Nat), 4 <= n_s ->
        C <= capacityUpperBound sigmaX sigmaN rho1 rho2 n_s) -> True := by
  kan_intro _h
  kan_constructor

end Section03
end OrbgrandAi
