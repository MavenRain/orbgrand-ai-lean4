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

/-- *`sinc(1) = 0`.*  Since `1 ≠ 0`, the `if`-branch evaluates to
    `sin(pi * 1) / (pi * 1) = sin(pi) / pi = 0 / pi = 0`.  Chains
    `if_neg one_ne_zero`, `mul_one`, `Real.sin_pi`, and `zero_div`. -/
theorem sinc_one : sinc 1 = 0 :=
  let h_ne : (1 : Real) ≠ 0 := one_ne_zero
  let step1 : sinc 1 = Real.sin (Real.pi * 1) / (Real.pi * 1) :=
    if_neg h_ne
  let pi_eq : Real.pi * 1 = Real.pi := mul_one Real.pi
  let step2 : Real.sin (Real.pi * 1) / (Real.pi * 1)
            = Real.sin Real.pi / Real.pi :=
    congrArg₂ (· / ·) (congrArg Real.sin pi_eq) pi_eq
  let step3 : Real.sin Real.pi / Real.pi = (0 : Real) / Real.pi :=
    congrArg (· / Real.pi) Real.sin_pi
  let step4 : (0 : Real) / Real.pi = 0 := zero_div Real.pi
  step1.trans (step2.trans (step3.trans step4))

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

/-- *Single-path delay-tap impulse response.*  With exactly one path
    (`p = 1`), the universal sum collapses to the single summand at
    `d = 0`, yielding the explicit `attenuation * sinc(delay)` form. -/
theorem delayTapImpulseResponse_single
    (paths : Fin 1 -> DelayTapPath)
    (f_s : SamplingFreq) (k' : SymbolIndex) :
    delayTapImpulseResponse paths f_s k'
      = (paths 0).attenuation *
        (((sinc ((paths 0).delay * f_s.val - (k'.toNat : Real))
          : Real)) : Complex) :=
  Fin.sum_univ_one _

/-- *Diagonal entry of `delayTapMatrix`.*  At `i = j` the dependent
    `if` discriminant `j.val ≤ i.val` holds reflexively; the inner
    delay `i.val - j.val` collapses to `0`, giving
    `delayTapImpulseResponse paths f_s ⟨0⟩`.  Composes
    `dif_pos (le_refl _)` with `Nat.sub_self`. -/
theorem delayTapMatrix_diag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i : Fin n_s) :
    delayTapMatrix n_s paths f_s i i
      = delayTapImpulseResponse paths f_s { toNat := 0 } :=
  let hle : i.val ≤ i.val := le_refl _
  let step1 : delayTapMatrix n_s paths f_s i i
            = delayTapImpulseResponse paths f_s
                { toNat := i.val - i.val } :=
    dif_pos hle
  let hsub : i.val - i.val = 0 := Nat.sub_self _
  let step2 : delayTapImpulseResponse paths f_s
                { toNat := i.val - i.val }
            = delayTapImpulseResponse paths f_s { toNat := 0 } :=
    congrArg (fun n => delayTapImpulseResponse paths f_s { toNat := n }) hsub
  step1.trans step2

/-- *Lower-triangular branch of `delayTapMatrix`.*  Whenever
    `j.val ≤ i.val`, the matrix entry is the impulse response at
    delay `i.val - j.val`.  This is `dif_pos` applied directly,
    surfacing the natural lookup parameter.  Use
    `delayTapMatrix_at_subdiag` when an explicit `d` is known. -/
theorem delayTapMatrix_apply_le
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : j.val ≤ i.val) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s
          { toNat := i.val - j.val } :=
  dif_pos h

/-- *General sub-diagonal entry of `delayTapMatrix`.*  For any
    delay `d` with `i.val = j.val + d`, the matrix entry is the
    impulse response at delay `d`.  Subsumes `delayTapMatrix_diag`
    (`d = 0`) and `delayTapMatrix_first_subdiag` (`d = 1`) as
    instances.  Same proof structure: `dif_pos` plus
    `Nat.add_sub_cancel_left`. -/
theorem delayTapMatrix_at_subdiag
    {n_s p d : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + d) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := d } :=
  let hle : j.val ≤ i.val := h.symm ▸ Nat.le_add_right j.val d
  let step1 : delayTapMatrix n_s paths f_s i j
            = delayTapImpulseResponse paths f_s
                { toNat := i.val - j.val } :=
    dif_pos hle
  let hsub : i.val - j.val = d :=
    h.symm ▸ Nat.add_sub_cancel_left j.val d
  let step2 : delayTapImpulseResponse paths f_s
                { toNat := i.val - j.val }
            = delayTapImpulseResponse paths f_s { toNat := d } :=
    congrArg (fun n => delayTapImpulseResponse paths f_s { toNat := n }) hsub
  step1.trans step2

/-- *First sub-diagonal of `delayTapMatrix`.*  When `i.val = j.val + 1`,
    the dependent `if` reduces (since `j.val ≤ i.val`) and the inner
    delay `i.val - j.val` collapses to `1`, giving the impulse
    response at delay 1.  Parallels `rfViewMatrix_first_subdiag`. -/
theorem delayTapMatrix_first_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 1) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 1 } :=
  let hle : j.val ≤ i.val := h.symm ▸ Nat.le_succ j.val
  let step1 : delayTapMatrix n_s paths f_s i j
            = delayTapImpulseResponse paths f_s
                { toNat := i.val - j.val } :=
    dif_pos hle
  let hsub : i.val - j.val = 1 :=
    h.symm ▸ Nat.add_sub_cancel_left j.val 1
  let step2 : delayTapImpulseResponse paths f_s
                { toNat := i.val - j.val }
            = delayTapImpulseResponse paths f_s { toNat := 1 } :=
    congrArg (fun n => delayTapImpulseResponse paths f_s { toNat := n }) hsub
  step1.trans step2

/-- *Diagonal entry via val-equality.*  When `i.val = j.val` (not
    necessarily `i = j` syntactically), the entry collapses to the
    impulse response at delay 0.  Useful when working with index
    values directly.  One-liner via `delayTapMatrix_at_subdiag` at
    `d = 0`. -/
theorem delayTapMatrix_at_diag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 0 } :=
  delayTapMatrix_at_subdiag paths f_s i j
    (h.trans (Nat.add_zero j.val).symm)

/-- *Diagonal collapse via val-equality.*  When `i.val = j.val`, the
    off-diagonal entry equals the on-diagonal entry at `i i`.
    Two-step chain: `delayTapMatrix_at_diag` (collapse to delay-0
    impulse) and `(delayTapMatrix_diag _ _ _).symm` (re-package as
    `i i`). -/
theorem delayTapMatrix_diag_of_val_eq
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val) :
    delayTapMatrix n_s paths f_s i j
      = delayTapMatrix n_s paths f_s i i :=
  (delayTapMatrix_at_diag paths f_s i j h).trans
    (delayTapMatrix_diag paths f_s i).symm

/-- *Second sub-diagonal of `delayTapMatrix`.*  When `i.val = j.val
    + 2`, the entry is the impulse response at delay 2.  One-liner
    via the general `delayTapMatrix_at_subdiag`. -/
theorem delayTapMatrix_second_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 2) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 2 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Third sub-diagonal of `delayTapMatrix`.*  When `i.val = j.val
    + 3`, the entry is the impulse response at delay 3.  Same
    pattern via `delayTapMatrix_at_subdiag`. -/
theorem delayTapMatrix_third_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 3) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 3 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Fourth sub-diagonal of `delayTapMatrix`.*  When `i.val = j.val
    + 4`, the entry is the impulse response at delay 4.  Same
    pattern via `delayTapMatrix_at_subdiag`. -/
theorem delayTapMatrix_fourth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 4) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 4 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Fifth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 5. -/
theorem delayTapMatrix_fifth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 5) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 5 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Sixth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 6. -/
theorem delayTapMatrix_sixth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 6) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 6 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Seventh sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 7. -/
theorem delayTapMatrix_seventh_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 7) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 7 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Eighth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 8. -/
theorem delayTapMatrix_eighth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 8) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 8 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Ninth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 9. -/
theorem delayTapMatrix_ninth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 9) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 9 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Tenth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 10. -/
theorem delayTapMatrix_tenth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 10) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 10 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Eleventh sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 11. -/
theorem delayTapMatrix_eleventh_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 11) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 11 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Twelfth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 12. -/
theorem delayTapMatrix_twelfth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 12) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 12 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Thirteenth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 13. -/
theorem delayTapMatrix_thirteenth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 13) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 13 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Fourteenth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 14. -/
theorem delayTapMatrix_fourteenth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 14) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 14 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Fifteenth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 15. -/
theorem delayTapMatrix_fifteenth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 15) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 15 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Sixteenth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 16. -/
theorem delayTapMatrix_sixteenth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 16) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 16 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Seventeenth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 17. -/
theorem delayTapMatrix_seventeenth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 17) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 17 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Eighteenth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 18. -/
theorem delayTapMatrix_eighteenth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 18) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 18 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Nineteenth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 19. -/
theorem delayTapMatrix_nineteenth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 19) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 19 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Twentieth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 20. -/
theorem delayTapMatrix_twentieth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 20) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 20 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Twenty-first sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 21. -/
theorem delayTapMatrix_twenty_first_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 21) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 21 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Twenty-second sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 22. -/
theorem delayTapMatrix_twenty_second_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 22) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 22 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Twenty-third sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 23. -/
theorem delayTapMatrix_twenty_third_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 23) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 23 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Twenty-fourth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 24. -/
theorem delayTapMatrix_twenty_fourth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 24) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 24 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Twenty-fifth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 25. -/
theorem delayTapMatrix_twenty_fifth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 25) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 25 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Twenty-sixth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 26. -/
theorem delayTapMatrix_twenty_sixth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 26) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 26 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Twenty-seventh sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 27. -/
theorem delayTapMatrix_twenty_seventh_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 27) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 27 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Twenty-eighth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 28. -/
theorem delayTapMatrix_twenty_eighth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 28) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 28 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Twenty-ninth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 29. -/
theorem delayTapMatrix_twenty_ninth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 29) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 29 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Thirtieth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 30. -/
theorem delayTapMatrix_thirtieth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 30) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 30 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Thirty-first sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 31. -/
theorem delayTapMatrix_thirty_first_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 31) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 31 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Thirty-second sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 32. -/
theorem delayTapMatrix_thirty_second_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 32) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 32 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Thirty-third sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 33. -/
theorem delayTapMatrix_thirty_third_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 33) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 33 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- *Delay-tap matrix entry above diagonal is zero.*  This is the
    same statement as `delayTap_causal` (which packages the result
    into `LinearIsi.causal`), restated as a direct matrix-entry
    equation for convenience. -/
theorem delayTapMatrix_zero_above_diag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (hij : i.val < j.val) :
    delayTapMatrix n_s paths f_s i j = (0 : Complex) :=
  delayTap_causal paths f_s i j hij

/-- *Zero-attenuation delay-tap matrix is zero.*  Composing
    `delayTapImpulseResponse_zero_attenuations` up to the matrix
    level: every entry vanishes when each path has zero attenuation.
    Splits on `j.val ≤ i.val`: the lower-triangular branch uses the
    impulse-response lemma; the upper-triangular branch is `0` via
    `dif_neg`. -/
theorem delayTapMatrix_zero_attenuations
    {n_s p : Nat} (paths : Fin p -> DelayTapPath)
    (h_zero : forall d, (paths d).attenuation = 0)
    (f_s : SamplingFreq) (i j : Fin n_s) :
    delayTapMatrix n_s paths f_s i j = (0 : Complex) :=
  if h : j.val <= i.val then
    let step1 : delayTapMatrix n_s paths f_s i j
              = delayTapImpulseResponse paths f_s
                  { toNat := i.val - j.val } :=
      dif_pos h
    step1.trans
      (delayTapImpulseResponse_zero_attenuations paths h_zero f_s _)
  else
    dif_neg h

/-- *Empty delay-tap matrix is zero.*  With zero paths (`p = 0`),
    every entry vanishes.  Lower-triangular branch chains through
    `delayTapImpulseResponse_empty`; upper-triangular branch is
    `0` via `dif_neg`. -/
theorem delayTapMatrix_empty
    {n_s : Nat} (paths : Fin 0 -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) :
    delayTapMatrix n_s paths f_s i j = (0 : Complex) :=
  if h : j.val <= i.val then
    let step1 : delayTapMatrix n_s paths f_s i j
              = delayTapImpulseResponse paths f_s
                  { toNat := i.val - j.val } :=
      dif_pos h
    step1.trans (delayTapImpulseResponse_empty paths f_s _)
  else
    dif_neg h

/-- *Thirty-fourth sub-diagonal of `delayTapMatrix`.*  Same pattern at
    delay 34. -/
theorem delayTapMatrix_thirty_fourth_subdiag
    {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 34) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 34 } :=
  delayTapMatrix_at_subdiag paths f_s i j h

end Section02
end OrbgrandAi
