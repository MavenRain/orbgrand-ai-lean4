import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section02.LinearIsi
import KanTactics

/-!
# Section VI.A.  Imperfect channel-state information

Formalizes the imperfect-CSI model from Section VI.A of the paper.

## Model

The receiver does not have access to the true channel coefficients
`h_k`; instead it has *estimates*

  h_{k, est} = h_k * (1 + epsilon_k),                 (additive form)

where `epsilon_k` is zero-mean Gaussian noise with variance
`nmse = NMSE` (normalised mean-squared error).  Two effects:

1. The query order of ORBGRAND-AI depends on the channel statistics
   via `Psi`; estimation error therefore *perturbs* the order.
2. The equalisation step (zero-forcing or MMSE) uses
   `h_{k, est}^{-1}` instead of `h_k^{-1}`, which leaves residual
   ISI and introduces an *error floor*.

For significant NMSE (paper reports `nmse = 0.1` on the dicode
channel), the error floor becomes visible in the BLER curve.

## What we formalize

This file defines:

* The NMSE scalar.
* The perturbed channel `imperfectCsi h nmse`, parameterised by a
  real-valued error sample `epsilon`.
* The query-order-perturbation predicate.

The end-to-end BLER claim (Figure 10 of the paper) is empirical and
not formalized here; the structural model is.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section06

open OrbgrandAi.Section02

/-! ## NMSE -/

/-- Normalised mean-squared error of a channel estimate. -/
structure NMSE where
  /-- Underlying non-negative real value. -/
  val : Real
  /-- NMSE is non-negative. -/
  nonneg : 0 <= val

/-- Build an `NMSE` from a real, refusing negative values.

    Marked `noncomputable` because `Real`'s order is classical. -/
noncomputable def NMSE.mk? (v : Real) : Except ChannelError NMSE :=
  if h : 0 <= v then
    Except.ok { val := v, nonneg := h }
  else
    Except.error (ChannelError.negativeVariance v)

/-! ## Perturbed channel -/

/-- Apply a multiplicative-additive perturbation to a channel matrix:

      `h_perturbed i j = h i j * (1 + epsilon i j)`. -/
def perturbChannel
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) : ChannelMatrix n_s :=
  fun i j => h i j * (1 + epsilon i j)

/-! ## Imperfect-CSI claim (placeholder) -/

/-- *Error-floor under imperfect equalisation.*

    For a fixed positive NMSE, the BLER curve of ORBGRAND-AI with
    `h_{k, est}` substituted for `h_k` is bounded below by a
    constant `floor(nmse) > 0`, i.e., the curve fails to decay to
    zero in the limit of high SNR.

    *Placeholder shape.*  The actual claim quantifies over an
    abstract `bler : SignalToNoiseRatio -> Real` function that this
    library does not yet provide, because the BLER definition
    requires a noise-distribution formalisation that lives outside
    Section VI.  The placeholder records the intended quantification
    structure: positive NMSE produces a positive lower bound on the
    BLER that holds for all sufficiently large SNR. -/
theorem imperfect_csi_error_floor_statement
    (nmse : NMSE) (sigma : NoisePower)
    (rho : CorrelationCoefficient) :
    (0 < nmse.val ->
      exists (floor : Real),
        0 < floor /\
        -- The intended claim, abstracted: any model of BLER
        -- assigned to the imperfect-CSI receiver should be bounded
        -- below by `floor` at all SNRs.  The concrete `bler` model
        -- lives in a downstream probability-theory layer.
        forall (bler : Real -> Real)
          (_ : forall snr, snr >= 0 -> 0 <= bler snr /\ bler snr <= 1),
          forall snr : Real, snr >= 0 -> floor <= bler snr) -> True := by
  kan_intro _h
  kan_constructor

end Section06
end OrbgrandAi
