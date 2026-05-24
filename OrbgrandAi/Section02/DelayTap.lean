import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section02.LinearIsi
import KanTactics

/-!
# Section II.A.  Delay-tap channel model

Formalizes the delay-tap impulse response from Section II.A:

  h_{k', j} = sum_{d = 1}^{p_{k', j}} a_{k', j, d} * sinc(tau_{k', j, d} * f_s - k')

where

* `d in {1, ..., p_{k', j}}` indexes the propagation path,
* `a_{k', j, d} in C` is the complex attenuation of path `d`,
* `tau_{k', j, d} in R` is the delay of path `d` in seconds,
* `f_s` is the sampling frequency in Hz,
* `sinc(x) = sin(pi x) / (pi x)` with the convention `sinc(0) = 1`.

The delay spread `tau_d`, defined as the maximum difference among
delays for a fixed `(k', j)`, is on the order of 1 microsecond for
terrestrial outdoor systems (paper, Section II.A).

This file defines:

* The normalised `sinc` function (using Mathlib's `Real.sin`).
* A path-component record holding `(a, tau)`.
* The aggregate impulse response `delayTapImpulseResponse`.
* The wrapped channel matrix `delayTapMatrix`.

The dicode and RFView channels are special cases of this model;
see `Section02.Dicode` and `Section02.RFView`.
-/

set_option autoImplicit false
open scoped Real

namespace OrbgrandAi
namespace Section02

/-! ## Normalised sinc -/

/-- The normalised sinc function:

      `sinc(x) = sin(pi * x) / (pi * x)`  for `x <> 0`,
      `sinc(0) = 1`.

    The branch on `x = 0` is taken explicitly rather than relying on
    the limiting value because `Real.sin 0 / 0` is `0 / 0 = 0` in
    Lean's convention.  This produces the mathematically correct
    `sinc(0) = 1`. -/
noncomputable def sinc (x : Real) : Real :=
  if x = 0 then 1 else Real.sin (Real.pi * x) / (Real.pi * x)

/-! ## Delay-tap path component -/

/-- A single propagation path: a complex attenuation `a` and a real
    delay `tau` (in seconds). -/
structure DelayTapPath where
  /-- Complex attenuation `a_d` of this path. -/
  attenuation : Complex
  /-- Delay `tau_d` in seconds.  A negative delay would represent a
      path arriving "before" the reference path; we permit it for
      generality. -/
  delay : Real

/-! ## Aggregate impulse response -/

/-- The delay-tap impulse response coefficient

      `h_{k', j} = sum_{d = 1}^{p} a_d * sinc(tau_d * f_s - k')`,

    as a function of the per-path data and the sampling frequency.
    The sum index `d` ranges over `Fin p` for a fixed number of paths
    `p`.  `k'` is the symbol time index. -/
noncomputable def delayTapImpulseResponse
    {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (k' : SymbolIndex) : Complex :=
  Finset.univ.sum fun d =>
    let path := paths d
    path.attenuation *
      ((sinc (path.delay * f_s.val - (k'.toNat : Real)) : Real) : Complex)

/-! ## Delay-tap channel matrix -/

/-- The `n_s x n_s` delay-tap channel matrix.  Each entry
    `delayTapMatrix paths f_s i j = h_{i, i - j}` when the channel is
    causal and the delay is `i - j`; otherwise the entry is taken to
    be zero.

    This makes `delayTapMatrix` lower-triangular by construction.
    Concrete instances (dicode, RFView) override this with their
    own structure. -/
noncomputable def delayTapMatrix
    (n_s : Nat) {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) : ChannelMatrix n_s :=
  fun i j =>
    if h : j.val <= i.val then
      let delay : Nat := i.val - j.val
      delayTapImpulseResponse paths f_s { toNat := delay }
    else
      (0 : Complex)

/-! ## Structural placeholders -/

/-- The delay-tap channel matrix is causal: entries strictly above
    the diagonal vanish.

    The `dif` discriminant is `j.val ≤ i.val`; under `i.val < j.val`
    this fails, so the `else` branch (which returns `0`) is taken. -/
theorem delayTap_causal
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (hij : i.val < j.val) :
    delayTapMatrix n_s paths f_s i j = (0 : Complex) :=
  show (if h : j.val <= i.val then
          let delay : Nat := i.val - j.val
          delayTapImpulseResponse paths f_s { toNat := delay }
        else (0 : Complex)) = (0 : Complex) from
    dif_neg (Nat.not_le_of_lt hij)

/-- `sinc(0) = 1` by the explicit branch in the definition.

    Resolved via `if_pos rfl` on the decidable predicate `(0 : Real) = 0`. -/
theorem sinc_zero : sinc 0 = 1 :=
  show (if (0 : Real) = 0 then (1 : Real)
        else Real.sin (Real.pi * 0) / (Real.pi * 0)) = 1 from
    if_pos rfl

/-- *Zero-attenuation delay-tap impulse response.*  When every path's
    attenuation coefficient `a_d` is zero, the aggregate impulse
    response vanishes for all symbol times.  Each summand becomes
    `0 * sinc(...) = 0`, and `Finset.sum_eq_zero` finishes. -/
theorem delayTapImpulseResponse_zero_attenuations
    {p : Nat} (paths : Fin p -> DelayTapPath)
    (h_zero : forall d, (paths d).attenuation = 0)
    (f_s : SamplingFreq) (k' : SymbolIndex) :
    delayTapImpulseResponse paths f_s k' = 0 :=
  Finset.sum_eq_zero fun d _ =>
    (congrArg (· * _) (h_zero d)).trans (zero_mul _)

/-- *Empty delay-tap impulse response.*  With zero paths (`p = 0`),
    the sum is over the empty Finset and collapses to `0`. -/
theorem delayTapImpulseResponse_empty
    (paths : Fin 0 -> DelayTapPath)
    (f_s : SamplingFreq) (k' : SymbolIndex) :
    delayTapImpulseResponse paths f_s k' = 0 :=
  Fin.sum_univ_zero _

end Section02
end OrbgrandAi
