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

/-- *Reverse complement equation.*  `bler (fun N => !decode N)
    = 1 - bler sigma decode`.  Mirror of `bler_eq_one_sub_compl`
    isolating the complement decoder.  Corollary of `bler_compl_eq`
    via `eq_sub_of_add_eq'`. -/
theorem bler_compl_eq_one_sub_bler
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool)
    (h_meas : MeasurableSet {N : RealSymbolVector n_s | decode N = true}) :
    bler sigma (fun N => !decode N) = 1 - bler sigma decode :=
  eq_sub_of_add_eq' (bler_compl_eq sigma decode h_meas)

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

/-- *Disjunctive decoder dominates left.*  The OR-decoder fails
    whenever the left component does, so `bler decode1 ≤ bler
    (decode1 || decode2)`.  Monotonicity via `bler_monotone` with
    `Bool.or_eq_true_iff.mpr ∘ Or.inl` as the pointwise witness. -/
theorem bler_le_bler_or_left
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool) :
    bler sigma decode1
      ≤ bler sigma (fun N => decode1 N || decode2 N) :=
  bler_monotone sigma decode1 _
    fun _ h => Bool.or_eq_true_iff.mpr (Or.inl h)

/-- *Disjunctive decoder dominates right.*  Right-handed companion
    to `bler_le_bler_or_left`: every `decode2` failure triggers the
    disjunctive decoder via `Or.inr`. -/
theorem bler_le_bler_or_right
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool) :
    bler sigma decode2
      ≤ bler sigma (fun N => decode1 N || decode2 N) :=
  bler_monotone sigma decode2 _
    fun _ h => Bool.or_eq_true_iff.mpr (Or.inr h)

/-- *Monotonicity under Boolean `&&` (left).*  The BLER of the conjunctive
    decoder is at most the BLER of the left component:
    `bler (fun N => decode1 N && decode2 N) ≤ bler decode1`.

    Proof: the conjunctive failure set `{decode1 ∧ decode2}` is contained
    in `{decode1}`, so `bler_monotone` closes via `Bool.and_eq_true_iff`. -/
theorem bler_and_le_left
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode1 N && decode2 N) ≤ bler sigma decode1 :=
  bler_monotone sigma _ decode1 fun _ h =>
    (Bool.and_eq_true_iff.mp h).1

/-- *Monotonicity under Boolean `&&` (right).*  Dual of `bler_and_le_left`. -/
theorem bler_and_le_right
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode1 N && decode2 N) ≤ bler sigma decode2 :=
  bler_monotone sigma _ decode2 fun _ h =>
    (Bool.and_eq_true_iff.mp h).2

/-- *Double negation.*  Boolean double-negation leaves the decoder
    pointwise-unchanged (`!!b = b`), so `bler` is invariant.  One-line
    corollary of `bler_pointwise_eq` via `Bool.not_not`. -/
theorem bler_double_neg
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => !!decode N) = bler sigma decode :=
  bler_pointwise_eq sigma _ decode fun N => Bool.not_not (decode N)

/-- *XOR vanishes when decoders agree.*  If two decoders agree pointwise,
    the XOR-failure set is empty and `bler (fun N => xor (decode1 N) (decode2 N)) = 0`.
    Chain: `Bool.xor_self` makes the XOR vanish, `bler_pointwise_eq`
    transfers to the constant-false decoder, `bler_const_false` closes. -/
theorem bler_xor_eq_zero_of_pointwise_eq
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool)
    (h : forall N, decode1 N = decode2 N) :
    bler sigma (fun N => xor (decode1 N) (decode2 N)) = 0 :=
  let h_xor_zero :
      forall N, xor (decode1 N) (decode2 N) = false :=
    fun N => h N ▸ Bool.xor_self (decode1 N)
  (bler_pointwise_eq sigma _ (fun _ => false) h_xor_zero).trans
    (bler_const_false sigma)

/-- *Helper: XOR implies OR.*  Four-case Bool match: when `xor a b = true`,
    `a || b = true`.  Each arm closes by `rfl` or `Bool.noConfusion`. -/
private theorem xor_imp_or :
    forall (a b : Bool), (xor a b = true) -> ((a || b) = true)
  | true,  true,  h => Bool.noConfusion h
  | true,  false, _ => rfl
  | false, true,  _ => rfl
  | false, false, h => Bool.noConfusion h

/-- *Sub-additivity under Boolean XOR.*  The BLER of the symmetric-
    difference (XOR) decoder is at most the sum of individual BLERs.
    Chain: `bler_monotone` with the pointwise `xor_imp_or` Bool helper,
    then `bler_or_le` closes via sub-additivity of `||`. -/
theorem bler_xor_le
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (decode1 N) (decode2 N))
      ≤ bler sigma decode1 + bler sigma decode2 :=
  let h_xor_le_or :
      bler sigma (fun N => xor (decode1 N) (decode2 N))
        ≤ bler sigma (fun N => decode1 N || decode2 N) :=
    bler_monotone sigma _ _ (fun _N h => xor_imp_or _ _ h)
  h_xor_le_or.trans (bler_or_le sigma decode1 decode2)

/-- *Commutativity of disjunctive decoder.*  Swapping the two
    decoders inside `(· || ·)` leaves `bler` unchanged.  One-line
    corollary of `bler_pointwise_eq` via `Bool.or_comm`. -/
theorem bler_or_comm
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode1 N || decode2 N)
      = bler sigma (fun N => decode2 N || decode1 N) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.or_comm (decode1 N) (decode2 N)

/-- *Commutativity of conjunctive decoder.*  Dual of `bler_or_comm`.
    The conjunctive decoder is symmetric in its arguments, so its
    `bler` is invariant under swap.  One-line corollary of
    `bler_pointwise_eq` via `Bool.and_comm`. -/
theorem bler_and_comm
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode1 N && decode2 N)
      = bler sigma (fun N => decode2 N && decode1 N) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.and_comm (decode1 N) (decode2 N)

/-- *Or-idempotence.*  Boolean `||`-idempotence (`b || b = b`) leaves
    the decoder pointwise-unchanged, so `bler` is invariant.  One-line
    corollary of `bler_pointwise_eq` via `Bool.or_self`. -/
theorem bler_or_idem
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode N || decode N) = bler sigma decode :=
  bler_pointwise_eq sigma _ decode fun N => Bool.or_self (decode N)

/-- *And-idempotence.*  Boolean `&&`-idempotence (`b && b = b`) leaves
    the decoder pointwise-unchanged, so `bler` is invariant.  One-line
    corollary of `bler_pointwise_eq` via `Bool.and_self`. -/
theorem bler_and_idem
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode N && decode N) = bler sigma decode :=
  bler_pointwise_eq sigma _ decode fun N => Bool.and_self (decode N)

/-- *Associativity of disjunctive decoder.*  Reparenthesizing the
    three-way `||` chain leaves `bler` unchanged.  One-line
    corollary of `bler_pointwise_eq` via `Bool.or_assoc`. -/
theorem bler_or_assoc
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => (d1 N || d2 N) || d3 N)
      = bler sigma (fun N => d1 N || (d2 N || d3 N)) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.or_assoc (d1 N) (d2 N) (d3 N)

/-- *Associativity of conjunctive decoder.*  Reparenthesizing the
    three-way `&&` chain leaves `bler` unchanged.  One-line
    corollary of `bler_pointwise_eq` via `Bool.and_assoc`. -/
theorem bler_and_assoc
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => (d1 N && d2 N) && d3 N)
      = bler sigma (fun N => d1 N && (d2 N && d3 N)) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.and_assoc (d1 N) (d2 N) (d3 N)

/-- *Commutativity of XOR decoder.*  Swapping the two decoders inside
    `xor` leaves `bler` unchanged.  One-line corollary of
    `bler_pointwise_eq` via `Bool.xor_comm`. -/
theorem bler_xor_comm
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (decode1 N) (decode2 N))
      = bler sigma (fun N => xor (decode2 N) (decode1 N)) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.xor_comm (decode1 N) (decode2 N)

/-- *Associativity of XOR decoder.*  Reparenthesizing the three-way
    XOR chain leaves `bler` unchanged.  One-line corollary of
    `bler_pointwise_eq` via `Bool.xor_assoc`. -/
theorem bler_xor_assoc
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (xor (d1 N) (d2 N)) (d3 N))
      = bler sigma (fun N => xor (d1 N) (xor (d2 N) (d3 N))) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.xor_assoc (d1 N) (d2 N) (d3 N)

/-- *Or-with-negation is total failure.*  `decode N || !decode N = true`
    pointwise (Boolean excluded middle), so the OR-decoder always
    reports failure and `bler = 1`.  One-line corollary of
    `bler_pointwise_eq` via `Bool.or_not_self`, chained into
    `bler_const_true`. -/
theorem bler_or_not_self
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode N || !decode N) = 1 :=
  (bler_pointwise_eq sigma _ (fun _ => true)
      (fun N => Bool.or_not_self (decode N))).trans
    (bler_const_true sigma)

/-- *And-with-negation vanishes.*  `decode N && !decode N = false`
    pointwise (Boolean non-contradiction), so the AND-decoder never
    reports failure and `bler = 0`.  Dual of `bler_or_not_self`.
    One-line corollary of `bler_pointwise_eq` via `Bool.and_not_self`,
    chained into `bler_const_false`. -/
theorem bler_and_not_self
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode N && !decode N) = 0 :=
  (bler_pointwise_eq sigma _ (fun _ => false)
      fun N => Bool.and_not_self (decode N)).trans
    (bler_const_false sigma)

/-- *Annihilation by `||`-true.*  `decode N || true = true` pointwise,
    so the OR-decoder is constantly `true` and `bler = 1`.  One-line
    corollary chaining `bler_pointwise_eq` via `Bool.or_true` with
    `bler_const_true`. -/
theorem bler_or_true
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode N || true) = 1 :=
  (bler_pointwise_eq sigma _ (fun _ => true)
      fun N => Bool.or_true (decode N)).trans
    (bler_const_true sigma)

/-- *Annihilation by `&&`-false.*  `decode N && false = false`
    pointwise, so the AND-decoder is constantly `false` and `bler = 0`.
    Dual of `bler_or_true`.  One-line corollary chaining
    `bler_pointwise_eq` via `Bool.and_false` with `bler_const_false`. -/
theorem bler_and_false
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode N && false) = 0 :=
  (bler_pointwise_eq sigma _ (fun _ => false)
      fun N => Bool.and_false (decode N)).trans
    (bler_const_false sigma)

/-- *Identity by `||`-false on the right.*  `decode N || false = decode N`
    pointwise, so the OR-decoder agrees with the original.  One-line
    corollary of `bler_pointwise_eq` via `Bool.or_false`. -/
theorem bler_or_false
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode N || false) = bler sigma decode :=
  bler_pointwise_eq sigma _ decode fun N => Bool.or_false (decode N)

/-- *Identity by `&&`-true on the right.*  `decode N && true = decode N`
    pointwise, so the AND-decoder agrees with the original.  One-line
    corollary of `bler_pointwise_eq` via `Bool.and_true`. -/
theorem bler_and_true
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode N && true) = bler sigma decode :=
  bler_pointwise_eq sigma _ decode fun N => Bool.and_true (decode N)

/-- *Identity by `||`-false on the left.*  `false || decode N = decode N`
    pointwise.  Left-handed companion to `bler_or_false`. -/
theorem bler_false_or
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => false || decode N) = bler sigma decode :=
  bler_pointwise_eq sigma _ decode fun N => Bool.false_or (decode N)

/-- *Identity by `&&`-true on the left.*  `true && decode N = decode N`
    pointwise.  Left-handed companion to `bler_and_true`. -/
theorem bler_true_and
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => true && decode N) = bler sigma decode :=
  bler_pointwise_eq sigma _ decode fun N => Bool.true_and (decode N)

/-- *Left annihilation by `||`-true.*  `true || decode N = true`
    pointwise, so `bler = 1`.  Left-handed companion to `bler_or_true`. -/
theorem bler_true_or
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => true || decode N) = 1 :=
  (bler_pointwise_eq sigma _ (fun _ => true)
      fun N => Bool.true_or (decode N)).trans
    (bler_const_true sigma)

/-- *Left annihilation by `&&`-false.*  `false && decode N = false`
    pointwise, so `bler = 0`.  Left-handed companion to `bler_and_false`. -/
theorem bler_false_and
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => false && decode N) = 0 :=
  (bler_pointwise_eq sigma _ (fun _ => false)
      fun N => Bool.false_and (decode N)).trans
    (bler_const_false sigma)

/-- *XOR with self vanishes.*  `xor (decode N) (decode N) = false`
    pointwise, so the failure set is empty and `bler = 0`.  Degenerate
    case of `bler_xor_eq_zero_of_pointwise_eq` (decode1 = decode2). -/
theorem bler_xor_self
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (decode N) (decode N)) = 0 :=
  (bler_pointwise_eq sigma _ (fun _ => false)
      fun N => Bool.xor_self (decode N)).trans
    (bler_const_false sigma)

/-- *XOR with `false` on the right is identity.*  `xor (decode N) false
    = decode N` pointwise.  One-line corollary of `bler_pointwise_eq`
    via `Bool.xor_false`. -/
theorem bler_xor_false_right
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (decode N) false) = bler sigma decode :=
  bler_pointwise_eq sigma _ decode fun N => Bool.xor_false (decode N)

/-- *XOR with `false` on the left is identity.*  `xor false (decode N)
    = decode N` pointwise.  Left-handed companion to
    `bler_xor_false_right`. -/
theorem bler_false_xor
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor false (decode N)) = bler sigma decode :=
  bler_pointwise_eq sigma _ decode fun N => Bool.false_xor (decode N)

/-- *DeMorgan over `||`.*  `!(decode1 N || decode2 N) = !decode1 N
    && !decode2 N` pointwise, so `bler` is invariant under the
    DeMorgan rewrite.  One-line corollary of `bler_pointwise_eq` via
    `Bool.not_or`. -/
theorem bler_not_or
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => !(d1 N || d2 N))
      = bler sigma (fun N => !d1 N && !d2 N) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.not_or (d1 N) (d2 N)

/-- *DeMorgan over `&&`.*  `!(decode1 N && decode2 N) = !decode1 N
    || !decode2 N` pointwise.  Dual of `bler_not_or`.  One-line
    corollary of `bler_pointwise_eq` via `Bool.not_and`. -/
theorem bler_not_and
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => !(d1 N && d2 N))
      = bler sigma (fun N => !d1 N || !d2 N) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.not_and (d1 N) (d2 N)

/-- *XOR with `true` on the right is negation.*  `xor (decode N) true
    = !decode N` pointwise, so the XOR-with-true decoder has the
    same `bler` as the negated decoder.  One-line corollary of
    `bler_pointwise_eq` via `Bool.xor_true`. -/
theorem bler_xor_true_right
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (decode N) true)
      = bler sigma (fun N => !decode N) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.xor_true (decode N)

/-- *XOR-true on the right equals `1 - bler decode`.*  Chains
    `bler_xor_true_right` (collapse XOR-true to negation) with
    `bler_compl_eq` (sum of decoder and complement is `1`,
    requires measurability) to obtain the closed-form
    `1 - bler sigma decode`. -/
theorem bler_xor_true_right_eq_one_sub
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool)
    (h_meas :
      MeasurableSet {N : RealSymbolVector n_s | decode N = true}) :
    bler sigma (fun N => xor (decode N) true) = 1 - bler sigma decode :=
  (bler_xor_true_right sigma decode).trans
    (eq_sub_of_add_eq' (bler_compl_eq sigma decode h_meas))

/-- *XOR with `true` on the left is negation.*  `xor true (decode N)
    = !decode N` pointwise.  Left-handed companion to
    `bler_xor_true_right`.  One-line corollary of `bler_pointwise_eq`
    via `Bool.true_xor`. -/
theorem bler_true_xor
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor true (decode N))
      = bler sigma (fun N => !decode N) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.true_xor (decode N)

/-- *XOR-of-NOT-with-self is total failure.*  `xor (!decode N)
    (decode N) = true` pointwise, so the XOR-decoder is constantly
    `true` and `bler = 1`.  Chain `bler_pointwise_eq` via
    `Bool.not_xor_self` with `bler_const_true`. -/
theorem bler_not_xor_self
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (!decode N) (decode N)) = 1 :=
  (bler_pointwise_eq sigma _ (fun _ => true)
      fun N => Bool.not_xor_self (decode N)).trans
    (bler_const_true sigma)

/-- *XOR-with-NOT-of-self is total failure.*  `xor (decode N)
    (!decode N) = true` pointwise.  Right-handed companion to
    `bler_not_xor_self`.  Chain via `Bool.xor_not_self` and
    `bler_const_true`. -/
theorem bler_xor_not_self
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (decode N) (!decode N)) = 1 :=
  (bler_pointwise_eq sigma _ (fun _ => true)
      fun N => Bool.xor_not_self (decode N)).trans
    (bler_const_true sigma)

/-- *NOT-XOR identity.*  `xor (!d1 N) (d2 N) = !(xor (d1 N) (d2 N))`
    pointwise.  Pushing a NOT through the left XOR argument is
    equivalent to negating the whole XOR.  One-line corollary of
    `bler_pointwise_eq` via `Bool.not_xor`. -/
theorem bler_not_xor
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (!d1 N) (d2 N))
      = bler sigma (fun N => !(xor (d1 N) (d2 N))) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.not_xor (d1 N) (d2 N)

/-- *XOR-NOT identity.*  `xor (d1 N) (!d2 N) = !(xor (d1 N) (d2 N))`
    pointwise.  Right-handed companion to `bler_not_xor`.  One-line
    corollary of `bler_pointwise_eq` via `Bool.xor_not`. -/
theorem bler_xor_not
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (d1 N) (!d2 N))
      = bler sigma (fun N => !(xor (d1 N) (d2 N))) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.xor_not (d1 N) (d2 N)

/-- *Double-NOT under XOR.*  `xor (!d1 N) (!d2 N) = xor (d1 N) (d2 N)`
    pointwise.  Two NOTs on the inputs cancel under XOR.  One-line
    corollary of `bler_pointwise_eq` via `Bool.not_xor_not`. -/
theorem bler_not_xor_not
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (!d1 N) (!d2 N))
      = bler sigma (fun N => xor (d1 N) (d2 N)) :=
  bler_pointwise_eq sigma _ _ fun N => Bool.not_xor_not (d1 N) (d2 N)

/-- *Distributivity of `&&` over `||` on the left.*  `a && (b || c)
    = (a && b) || (a && c)` pointwise.  One-line corollary of
    `bler_pointwise_eq` via `Bool.and_or_distrib_left`. -/
theorem bler_and_or_distrib_left
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => d1 N && (d2 N || d3 N))
      = bler sigma (fun N => (d1 N && d2 N) || (d1 N && d3 N)) :=
  bler_pointwise_eq sigma _ _ fun N =>
    Bool.and_or_distrib_left (d1 N) (d2 N) (d3 N)

/-- *Distributivity of `&&` over `||` on the right.*  `(a || b) && c
    = (a && c) || (b && c)` pointwise.  One-line corollary of
    `bler_pointwise_eq` via `Bool.and_or_distrib_right`. -/
theorem bler_and_or_distrib_right
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => (d1 N || d2 N) && d3 N)
      = bler sigma (fun N => (d1 N && d3 N) || (d2 N && d3 N)) :=
  bler_pointwise_eq sigma _ _ fun N =>
    Bool.and_or_distrib_right (d1 N) (d2 N) (d3 N)

/-- *Distributivity of `||` over `&&` on the left.*  `a || (b && c)
    = (a || b) && (a || c)` pointwise.  One-line corollary of
    `bler_pointwise_eq` via `Bool.or_and_distrib_left`. -/
theorem bler_or_and_distrib_left
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => d1 N || (d2 N && d3 N))
      = bler sigma (fun N => (d1 N || d2 N) && (d1 N || d3 N)) :=
  bler_pointwise_eq sigma _ _ fun N =>
    Bool.or_and_distrib_left (d1 N) (d2 N) (d3 N)

/-- *Distributivity of `||` over `&&` on the right.*  `(a && b) || c
    = (a || c) && (b || c)` pointwise.  One-line corollary of
    `bler_pointwise_eq` via `Bool.or_and_distrib_right`. -/
theorem bler_or_and_distrib_right
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => (d1 N && d2 N) || d3 N)
      = bler sigma (fun N => (d1 N || d3 N) && (d2 N || d3 N)) :=
  bler_pointwise_eq sigma _ _ fun N =>
    Bool.or_and_distrib_right (d1 N) (d2 N) (d3 N)

/-- *Helper: absorption `a || (a && b) = a`.*  Four-case Bool match,
    each arm closes by `rfl` (the `a = true` case collapses the `||`
    to `true`; the `a = false` case collapses the `&&` to `false`,
    then the `||` to `false`). -/
private theorem or_and_self_bool :
    forall (a b : Bool), (a || (a && b)) = a
  | true,  true  => rfl
  | true,  false => rfl
  | false, true  => rfl
  | false, false => rfl

/-- *Helper: absorption `a && (a || b) = a`.*  Four-case Bool match,
    each arm closes by `rfl`. -/
private theorem and_or_self_bool :
    forall (a b : Bool), (a && (a || b)) = a
  | true,  true  => rfl
  | true,  false => rfl
  | false, true  => rfl
  | false, false => rfl

/-- *Absorption: `a || (a && b)` collapses to `a`.*  Boolean
    absorption pointwise, so `bler` is invariant.  One-line
    corollary of `bler_pointwise_eq` via the `or_and_self_bool`
    helper. -/
theorem bler_or_and_absorb
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => d1 N || (d1 N && d2 N))
      = bler sigma d1 :=
  bler_pointwise_eq sigma _ d1 fun N => or_and_self_bool (d1 N) (d2 N)

/-- *Absorption: `a && (a || b)` collapses to `a`.*  Dual to
    `bler_or_and_absorb`.  One-line corollary of `bler_pointwise_eq`
    via the `and_or_self_bool` helper. -/
theorem bler_and_or_absorb
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => d1 N && (d1 N || d2 N))
      = bler sigma d1 :=
  bler_pointwise_eq sigma _ d1 fun N => and_or_self_bool (d1 N) (d2 N)

/-- *XOR decoder bounded by OR decoder.*  Boolean `xor a b = true`
    implies `a || b = true` (the `xor_imp_or` helper), so the XOR-
    failure set is contained in the OR-failure set.  Exposed as
    its own named lemma — the intermediate step inside
    `bler_xor_le`. -/
theorem bler_xor_le_bler_or
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (decode1 N) (decode2 N))
      ≤ bler sigma (fun N => decode1 N || decode2 N) :=
  bler_monotone sigma _ _ (fun _N h => xor_imp_or _ _ h)

/-- *AND decoder bounded by OR decoder.*  Conjunctive failure set is
    contained in the left component's failure set via
    `bler_and_le_left`, which is in turn contained in the disjunctive
    failure set via `bler_le_bler_or_left`.  Transitivity closes. -/
theorem bler_and_le_bler_or
    {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => decode1 N && decode2 N)
      ≤ bler sigma (fun N => decode1 N || decode2 N) :=
  le_trans (bler_and_le_left sigma decode1 decode2)
           (bler_le_bler_or_left sigma decode1 decode2)

/-- *NOT-left and NOT-right XOR collapse to the same BLER.*  Both
    `xor (!d1 N) (d2 N)` and `xor (d1 N) (!d2 N)` equal `!(xor (d1 N)
    (d2 N))` pointwise.  Chain `bler_not_xor` with `(bler_xor_not).symm`. -/
theorem bler_not_xor_eq_xor_not
    {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : RealSymbolVector n_s -> Bool) :
    bler sigma (fun N => xor (!d1 N) (d2 N))
      = bler sigma (fun N => xor (d1 N) (!d2 N)) :=
  (bler_not_xor sigma d1 d2).trans (bler_xor_not sigma d1 d2).symm

end Section00
end OrbgrandAi
