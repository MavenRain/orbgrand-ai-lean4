import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section02.LinearIsi
import KanTactics

/-!
# Section 0.  Probability layer

The probability layer underpins the Section IV BLER-equivalence claim
and the Section VI.B error-floor claim.  Both are intrinsically
probabilistic: they are claims about the distribution of the decoder's
output over Gaussian noise on `EuclideanSpace ℝ (Fin n_s)`.

This file imports the measure-theoretic dependencies once, in a single
module, so that the rest of the library can refer to a Gaussian noise
model without each consumer paying the Mathlib measure-theory compile
cost.

## What's here

* `noiseMeasure` -- the AWGN noise distribution on `EuclideanSpace ℝ (Fin n_s)`,
  built from `multivariateGaussian` with covariance `sigma.val * I_{n_s}`.
* `RealSymbolVector` -- a real-valued symbol vector type,
  parallel to `Section02.LinearIsi.SymbolVector` (which is `Complex`-valued)
  but living in the real Euclidean space `EuclideanSpace ℝ (Fin n_s)` where
  Mathlib's multivariate Gaussian is defined.
* `bler` -- the block error rate of a decoder `decode : RealSymbolVector n_s -> Bool`
  expressed as the noise measure of the decoder's failure set.

## What's not here yet

The concrete Gaussian-vs-decoder analyses (error-floor inequality,
symbol/bit-level equivalence) live in the Section IV and Section VI.B
files that consume this scaffolding.  This module only provides the
type-level interface and the Gaussian noise constructor.

## Why this file exists at "Section 0"

The paper does not have a numbered "probability" section; the noise
model is implicit throughout.  Promoting it to its own module keeps
the measure-theory imports paid exactly once, and lets the
Section IV / VI.B placeholder statements be re-formulated as actual
probabilistic claims rather than `(P -> True) -> True` shells.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section00

open MeasureTheory ProbabilityTheory
open OrbgrandAi.Section02

/-- A real-valued symbol vector of length `n_s`, living in the
    Euclidean space `EuclideanSpace ℝ (Fin n_s)`.  Mathlib's
    `multivariateGaussian` requires its support space to be
    `EuclideanSpace ℝ ι` for some index type `ι`, so we mirror the
    `Complex`-valued `Section02.LinearIsi.SymbolVector` on the real
    side for the noise model. -/
abbrev RealSymbolVector (n_s : Nat) : Type := EuclideanSpace ℝ (Fin n_s)

/-- The AWGN noise distribution on `RealSymbolVector n_s`, parameterised
    by the per-component noise power `sigma`.

    Built from Mathlib's `multivariateGaussian` with mean `0` and
    covariance matrix `sigma.val * I_{n_s}`, i.e.,
    `Matrix.diagonal (fun _ => sigma.val)`.

    Under the AWGN convention noise components are i.i.d. with variance
    `sigma.val`; the covariance matrix is therefore diagonal. -/
noncomputable def noiseMeasure
    (n_s : Nat) (sigma : NoisePower) :
    Measure (RealSymbolVector n_s) :=
  multivariateGaussian (0 : RealSymbolVector n_s)
    (Matrix.diagonal (fun _ : Fin n_s => sigma.val))

/-- The block error rate of a decoder.

    Given a decoder `decode : RealSymbolVector n_s -> Bool` (where
    `true` means "decoder produced the wrong codeword") and a noise
    measure, the BLER is the `noiseMeasure`-measure of the set on
    which `decode` returns `true`.

    The decoder type signature is intentionally abstract here;
    Section IV / VI.B consumers will instantiate `decode` as the
    composition of the actual ORBGRAND-AI decoder with a
    receiver-fixed reference codeword.

    Returns `Real` rather than `ℝ≥0∞` so downstream comparisons
    (`floor <= bler`) line up with the existing `Real`-valued
    statement shells. -/
noncomputable def bler
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) : Real :=
  (noiseMeasure n_s sigma { N | decode N = true }).toReal

/-- *Block error rate is non-negative.*  Immediate from
    `ENNReal.toReal_nonneg`: every `(_ : ℝ≥0∞).toReal` is `≥ 0`, so
    the noise-measure of any set, taken via `.toReal`, is non-negative. -/
theorem bler_nonneg
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    0 ≤ bler sigma decode :=
  ENNReal.toReal_nonneg

/-- *`noiseMeasure` is a Gaussian measure.*  Instance synthesis chain:
    `multivariateGaussian` is unconditionally `IsGaussian` (from
    Mathlib's `isGaussian_multivariateGaussian`), and `noiseMeasure` is
    literally a `multivariateGaussian`.

    Exposed as a named instance so downstream consumers
    (`bler_le_one`, the error-floor refactor) can pick up the
    probability-measure typeclass chain by inference. -/
instance noiseMeasure_isGaussian
    (n_s : Nat) (sigma : NoisePower) :
    ProbabilityTheory.IsGaussian (noiseMeasure n_s sigma) :=
  ProbabilityTheory.isGaussian_multivariateGaussian

/-- *Block error rate is at most one.*  Upper half of the
    `0 ≤ bler ≤ 1` sandwich.  Chain:

    1. `noiseMeasure_isGaussian` makes `noiseMeasure n_s sigma`
       a `ProbabilityTheory.IsGaussian`.
    2. `IsGaussian.toIsProbabilityMeasure` lifts that to
       `IsProbabilityMeasure (noiseMeasure n_s sigma)`.
    3. `IsProbabilityMeasure` lifts to `IsZeroOrProbabilityMeasure`
       via the default-priority instance.
    4. `MeasureTheory.measureReal_le_one` then gives
       `(noiseMeasure n_s sigma).real S ≤ 1` for every `S`, and
       `.real S = (· S).toReal` by definition, matching `bler`. -/
theorem bler_le_one
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma decode ≤ 1 :=
  MeasureTheory.measureReal_le_one

/-- *Saturating decoder.*  When the decoder reports failure on every input
    (`fun _ => true`), the failure set is all of `RealSymbolVector n_s`, so
    `bler = noiseMeasure(univ).toReal = 1.toReal = 1`.

    Term-mode chain:
    1. `Set.eq_univ_of_forall (fun _ => rfl)` identifies the failure set
       `{N | (fun _ => true) N = true}` with `Set.univ`.
    2. `MeasureTheory.measure_univ` gives `noiseMeasure Set.univ = 1`
       (via the `IsProbabilityMeasure` instance chain).
    3. `ENNReal.toReal_one` closes the conversion. -/
theorem bler_const_true
    {n_s : Nat} (sigma : NoisePower) :
    bler sigma (fun _ : RealSymbolVector n_s => true) = 1 :=
  let h_set :
      {N : RealSymbolVector n_s | (fun _ : RealSymbolVector n_s => true) N = true}
        = Set.univ :=
    Set.eq_univ_of_forall (fun _ => rfl)
  let h_meas :
      noiseMeasure n_s sigma
        {N : RealSymbolVector n_s | (fun _ : RealSymbolVector n_s => true) N = true}
        = 1 :=
    (congrArg (noiseMeasure n_s sigma) h_set).trans MeasureTheory.measure_univ
  (congrArg ENNReal.toReal h_meas).trans ENNReal.toReal_one

/-- *Non-failing decoder.*  When the decoder reports success on every input
    (`fun _ => false`), the failure set is empty, so
    `bler = noiseMeasure(∅).toReal = 0.toReal = 0`.

    Dual of `bler_const_true`.  Term-mode chain:
    1. `Set.eq_empty_of_forall_notMem` (with `Bool.noConfusion` on
       `false = true`) identifies the failure set with `∅`.
    2. `MeasureTheory.measure_empty` gives `noiseMeasure ∅ = 0`.
    3. `ENNReal.toReal_zero` closes the conversion. -/
theorem bler_const_false
    {n_s : Nat} (sigma : NoisePower) :
    bler sigma (fun _ : RealSymbolVector n_s => false) = 0 :=
  let h_set :
      {N : RealSymbolVector n_s | (fun _ : RealSymbolVector n_s => false) N = true}
        = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ h => Bool.noConfusion h
  let h_meas :
      noiseMeasure n_s sigma
        {N : RealSymbolVector n_s | (fun _ : RealSymbolVector n_s => false) N = true}
        = 0 :=
    (congrArg (noiseMeasure n_s sigma) h_set).trans MeasureTheory.measure_empty
  (congrArg ENNReal.toReal h_meas).trans ENNReal.toReal_zero

/-- *Monotonicity in decoder.*  If `decode1`'s failure set is contained in
    `decode2`'s (i.e., every `decode1`-failure is also a `decode2`-failure),
    then `bler sigma decode1 ≤ bler sigma decode2`.

    Term-mode chain:
    1. The hypothesis lifts to a `Set.subset` of failure sets.
    2. `MeasureTheory.measure_mono` gives the inequality on `ℝ≥0∞` measures.
    3. `MeasureTheory.measure_ne_top` (via the `IsFiniteMeasure` instance
       chain) provides the finiteness witness `noiseMeasure decode2 ≠ ∞`.
    4. `ENNReal.toReal_mono` closes the real-valued comparison. -/
theorem bler_monotone
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool)
    (h : forall N, decode1 N = true -> decode2 N = true) :
    bler sigma decode1 ≤ bler sigma decode2 :=
  let h_subset :
      {N : RealSymbolVector n_s | decode1 N = true}
        ⊆ {N : RealSymbolVector n_s | decode2 N = true} :=
    fun _ hN => h _ hN
  let h_meas_le :
      noiseMeasure n_s sigma {N | decode1 N = true}
        ≤ noiseMeasure n_s sigma {N | decode2 N = true} :=
    MeasureTheory.measure_mono h_subset
  let h_finite : noiseMeasure n_s sigma {N | decode2 N = true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  ENNReal.toReal_mono h_finite h_meas_le

/-- *Pointwise equality.*  If two decoders agree on every input, their
    `bler` values coincide.  Single-line `congrArg (bler sigma) ∘ funext`. -/
theorem bler_pointwise_eq
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool)
    (h : forall N, decode1 N = decode2 N) :
    bler sigma decode1 = bler sigma decode2 :=
  congrArg (bler sigma) (funext h)

/-- *Complement relation.*  Under a measurability hypothesis on the failure
    set, `bler decode + bler (!decode) = 1`.

    Term-mode chain:
    1. `Bool.not_eq_true' (decode N) : ((!decode N) = true) = (decode N = false)`
       and `Bool.not_eq_true (decode N) : ¬(decode N = true) = (decode N = false)`
       (both Lean-core Prop-level equations).  Chaining via
       `.trans (.symm)` gives `((!decode N) = true) = ¬(decode N = true)`.
    2. `Iff.of_eq` lifts to the `Iff` needed by `Set.ext`, identifying
       `{N | (!decode N) = true}` with `{N | decode N = true}ᶜ`.
    3. `MeasureTheory.measure_add_measure_compl h_meas` gives the
       additive partition `μ s + μ sᶜ = μ univ` on the ℝ≥0∞ side.
    4. `MeasureTheory.measure_univ` (via the `IsProbabilityMeasure`
       instance chain) gives `μ univ = 1`.
    5. `ENNReal.toReal_add` distributes `.toReal` over `+`, using
       finiteness from `MeasureTheory.measure_ne_top` (`IsFiniteMeasure`).
    6. `ENNReal.toReal_one` closes the final value. -/
theorem bler_compl_eq
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool)
    (h_meas : MeasurableSet {N : RealSymbolVector n_s | decode N = true}) :
    bler sigma decode + bler sigma (fun N => !decode N) = 1 :=
  let h_compl_set :
      {N : RealSymbolVector n_s | (fun N => !decode N) N = true}
        = {N : RealSymbolVector n_s | decode N = true}ᶜ :=
    Set.ext fun N =>
      Iff.of_eq
        ((Bool.not_eq_true' (decode N)).trans
          (Bool.not_eq_true (decode N)).symm)
  let h_meas_add :
      noiseMeasure n_s sigma {N | decode N = true}
        + noiseMeasure n_s sigma {N | (fun N => !decode N) N = true}
        = noiseMeasure n_s sigma Set.univ :=
    (congrArg (fun S => noiseMeasure n_s sigma {N | decode N = true}
                          + noiseMeasure n_s sigma S) h_compl_set).trans
      (MeasureTheory.measure_add_measure_compl h_meas)
  let h_one :
      noiseMeasure n_s sigma {N | decode N = true}
        + noiseMeasure n_s sigma {N | (fun N => !decode N) N = true}
        = 1 :=
    h_meas_add.trans MeasureTheory.measure_univ
  let h_finite1 :
      noiseMeasure n_s sigma {N : RealSymbolVector n_s | decode N = true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  let h_finite2 :
      noiseMeasure n_s sigma
          {N : RealSymbolVector n_s | (fun N => !decode N) N = true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  let h_toReal :
      (noiseMeasure n_s sigma {N | decode N = true}
        + noiseMeasure n_s sigma {N | (fun N => !decode N) N = true}).toReal
        = bler sigma decode + bler sigma (fun N => !decode N) :=
    ENNReal.toReal_add h_finite1 h_finite2
  h_toReal.symm.trans
    ((congrArg ENNReal.toReal h_one).trans ENNReal.toReal_one)

/-- *Complement equation.*  `bler decode = 1 - bler !decode` under the
    measurability hypothesis.  Corollary of `bler_compl_eq` via
    `eq_sub_of_add_eq`. -/
theorem bler_eq_one_sub_compl
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool)
    (h_meas : MeasurableSet {N : RealSymbolVector n_s | decode N = true}) :
    bler sigma decode = 1 - bler sigma (fun N => !decode N) :=
  eq_sub_of_add_eq (bler_compl_eq sigma decode h_meas)

/-- *Subadditivity under Boolean `||`.*  The BLER of the disjunctive
    decoder is at most the sum of individual BLERs:
    `bler (fun N => decode1 N || decode2 N) ≤ bler decode1 + bler decode2`.

    No measurability hypothesis needed — `MeasureTheory.measure_union_le`
    is subadditivity on outer measures.

    Term-mode chain:
    1. `Bool.or_eq_true_iff` identifies the failure set of `decode1 || decode2`
       with the union `{decode1} ∪ {decode2}` via `Set.ext`.
    2. `MeasureTheory.measure_union_le` gives subadditivity on `ℝ≥0∞`.
    3. `ENNReal.add_ne_top` (via `IsFiniteMeasure`) provides the
       finiteness witness for the sum.
    4. `ENNReal.toReal_mono` + `ENNReal.toReal_add` close the real-valued
       inequality. -/
theorem bler_or_le
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode1 N || decode2 N)
      ≤ bler sigma decode1 + bler sigma decode2 :=
  let h_set :
      {N : RealSymbolVector n_s | (fun N => decode1 N || decode2 N) N = true}
        = {N : RealSymbolVector n_s | decode1 N = true}
            ∪ {N : RealSymbolVector n_s | decode2 N = true} :=
    Set.ext fun _ => Bool.or_eq_true_iff
  let h_meas_le :
      noiseMeasure n_s sigma
          {N | (fun N => decode1 N || decode2 N) N = true}
        ≤ noiseMeasure n_s sigma {N | decode1 N = true}
            + noiseMeasure n_s sigma {N | decode2 N = true} :=
    h_set ▸ MeasureTheory.measure_union_le _ _
  let h_add_ne_top :
      noiseMeasure n_s sigma {N | decode1 N = true}
        + noiseMeasure n_s sigma {N | decode2 N = true} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨MeasureTheory.measure_ne_top _ _, MeasureTheory.measure_ne_top _ _⟩
  (ENNReal.toReal_mono h_add_ne_top h_meas_le).trans
    (le_of_eq
      (ENNReal.toReal_add (MeasureTheory.measure_ne_top _ _)
                          (MeasureTheory.measure_ne_top _ _)))

end Section00
end OrbgrandAi
