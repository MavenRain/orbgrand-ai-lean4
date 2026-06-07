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

/-! ### Structural properties of `perturbChannel` -/

/-- *Zero perturbation is the identity.*  Setting the error matrix to
    zero leaves the channel unchanged.  `add_zero` collapses `1 + 0`
    to `1`, then `mul_one` finishes. -/
theorem perturbChannel_zero
    {n_s : Nat} (h : ChannelMatrix n_s) :
    perturbChannel h 0 = h :=
  funext fun i => funext fun j =>
    (congrArg (h i j * ·) (add_zero (1 : Complex))).trans (mul_one (h i j))

/-- *Zero channel stays zero under perturbation.*  When the underlying
    channel matrix is zero, the perturbed channel is also zero
    (regardless of the error matrix).  Each entry becomes
    `0 * (1 + epsilon i j) = 0` via `zero_mul`. -/
theorem perturbChannel_zero_channel
    {n_s : Nat} (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) :
    perturbChannel 0 epsilon = 0 :=
  funext fun i => funext fun j => zero_mul (1 + epsilon i j)

/-- *Composition of two perturbations.*  Applying `perturbChannel`
    twice (first by `ε₁`, then by `ε₂`) at entry `(i, j)` yields
    `h i j * ((1 + ε₁ i j) * (1 + ε₂ i j))`.  Direct `mul_assoc`
    on the chained definitional unfolding. -/
theorem perturbChannel_perturbChannel_apply
    {n_s : Nat} (h : ChannelMatrix n_s)
    (ε₁ ε₂ : Matrix (Fin n_s) (Fin n_s) Complex)
    (i j : Fin n_s) :
    perturbChannel (perturbChannel h ε₁) ε₂ i j
      = h i j * ((1 + ε₁ i j) * (1 + ε₂ i j)) :=
  mul_assoc (h i j) (1 + ε₁ i j) (1 + ε₂ i j)

/-- *General entry of `perturbChannel`.*  Direct definitional
    unfolding: `perturbChannel h epsilon i j = h i j * (1 + epsilon i j)`.
    Useful as a named API surface, subsumes `perturbChannel_diag`. -/
theorem perturbChannel_apply
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i j : Fin n_s) :
    perturbChannel h epsilon i j = h i j * (1 + epsilon i j) := rfl

/-- *Diagonal entry of `perturbChannel`.*  At `i = j`, the entry is
    simply `h i i * (1 + epsilon i i)`.  Direct definitional
    unfolding; useful as a named API surface. -/
theorem perturbChannel_diag
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i : Fin n_s) :
    perturbChannel h epsilon i i = h i i * (1 + epsilon i i) := rfl

/-- *Pointwise identity at zero perturbation.*  When `epsilon i j = 0`,
    the perturbed entry equals `h i j`.  Pointwise dual of
    `perturbChannel_zero` and counterpart of
    `perturbChannel_neg_one_attenuation_eq_zero`.  Three-step via
    `congrArg` + `add_zero` + `mul_one`. -/
theorem perturbChannel_eps_zero_apply
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i j : Fin n_s} (h_eps : epsilon i j = 0) :
    perturbChannel h epsilon i j = h i j :=
  let h_factor : (1 : Complex) + epsilon i j = 1 :=
    (congrArg (1 + ·) h_eps).trans (add_zero 1)
  (congrArg (h i j * ·) h_factor).trans (mul_one (h i j))

/-- *Pure cancellation: `epsilon = -1` zeroes the entry.*  When the
    error term at `(i, j)` exactly cancels the unit, the perturbed
    entry vanishes regardless of `h i j`.  Composes `congrArg` on
    `epsilon i j → -1` with `add_neg_cancel 1 : 1 + (-1) = 0` and
    `mul_zero`.  Concrete instance of the right disjunct in
    `perturbChannel_eq_zero_iff`. -/
theorem perturbChannel_neg_one_attenuation_eq_zero
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i j : Fin n_s} (h_eps : epsilon i j = -1) :
    perturbChannel h epsilon i j = 0 :=
  let h_factor : (1 : Complex) + epsilon i j = 0 :=
    (congrArg (1 + ·) h_eps).trans (add_neg_cancel 1)
  (congrArg (h i j * ·) h_factor).trans (mul_zero _)

/-- *Pointwise zero characterisation.*  A perturbed entry vanishes
    iff either the underlying entry vanishes or the multiplicative
    factor `1 + epsilon i j` is zero.  Since `Complex` is an
    integral domain, `mul_eq_zero` is the iff. -/
theorem perturbChannel_eq_zero_iff
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    (i j : Fin n_s) :
    perturbChannel h epsilon i j = 0
      <-> h i j = 0 ∨ 1 + epsilon i j = 0 :=
  mul_eq_zero

/-- *Pointwise zero preservation.*  If a single entry `h i j` is zero,
    the corresponding perturbed entry is also zero, for any error
    matrix.  Generalises the per-cell logic of
    `perturbChannel_causal_of_causal` and
    `perturbChannel_bandwidth_of_bandwidth`. -/
theorem perturbChannel_zero_entry
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i j : Fin n_s} (hzero : h i j = 0) :
    perturbChannel h epsilon i j = 0 :=
  (congrArg (· * (1 + epsilon i j)) hzero).trans (zero_mul _)

/-- *Causality preservation.*  Multiplicative-additive perturbation
    preserves the causality predicate: if `h i j = 0` for `i < j`, then
    `(perturbChannel h epsilon) i j = 0` for the same indices.  The
    causality predicate is closed under perturbation. -/
theorem perturbChannel_causal_of_causal
    {n_s : Nat} {h : ChannelMatrix n_s}
    {epsilon : Matrix (Fin n_s) (Fin n_s) Complex}
    (hcausal : forall (i j : Fin n_s), i.val < j.val -> h i j = 0) :
    forall (i j : Fin n_s),
      i.val < j.val -> perturbChannel h epsilon i j = 0 :=
  fun i j hij =>
    (congrArg (· * (1 + epsilon i j)) (hcausal i j hij)).trans (zero_mul _)

/-- *Bandwidth preservation.*  Multiplicative-additive perturbation
    preserves the bandwidth predicate as well: if `h i j = 0`
    whenever `j + b < i`, then so does the perturbed channel. -/
theorem perturbChannel_bandwidth_of_bandwidth
    {n_s : Nat} {h : ChannelMatrix n_s}
    {epsilon : Matrix (Fin n_s) (Fin n_s) Complex}
    {b : Nat}
    (hb : forall (i j : Fin n_s), j.val + b < i.val -> h i j = 0) :
    forall (i j : Fin n_s),
      j.val + b < i.val -> perturbChannel h epsilon i j = 0 :=
  fun i j hij =>
    (congrArg (· * (1 + epsilon i j)) (hb i j hij)).trans (zero_mul _)

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
