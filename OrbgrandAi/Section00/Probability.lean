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
    the noise-measure of any set, taken via `.toReal`, is non-negative.

    This is the lower half of the `0 ≤ bler ≤ 1` sandwich.  The upper
    half requires the `IsProbabilityMeasure` instance for the
    `multivariateGaussian` and is deferred. -/
theorem bler_nonneg
    {n_s : Nat} (sigma : NoisePower)
    (decode : RealSymbolVector n_s -> Bool) :
    0 ≤ bler sigma decode :=
  ENNReal.toReal_nonneg

end Section00
end OrbgrandAi
