import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section02.LinearIsi
import KanTactics

/-!
# Section II.C.  RFView ISI channel

Formalizes the RFView channel from Section II.C of the paper.  The
RFView dataset is a physics-based RF simulation; for each Coherent
Processing Interval (CPI) it provides

* 32 antenna channels,
* 64 pulses,
* 2335 impulse-response samples sampled at 10 MHz.

The paper processes one antenna element from one CPI (single-input
single-output).  After matched filtering and downsampling along the
impulse-response axis (factor `L = 467`), the post-processing
yields six channel taps `h_{k', j}` for `j in {1, ..., 6}`.  The
6-tap structure is encoded as a banded lower-triangular matrix:

  h_RFV =
    [ h_{1,1}   0        0       ...                 0
      h_{2,2}   h_{2,1}  0       ...                 0
      h_{3,3}   h_{3,2}  h_{3,1} ...                 0
       ...                                          ...
       0        ...      h_{n_s, 6}  ...   h_{n_s, 1} ]

This is the channel matrix `LinearIsi.bandwidth 6 = True` instance.

This file defines:

* The taps record `RFViewTaps` carrying the six complex taps for one
  row of the matrix.
* The `rfViewMatrix` constructor that lays the taps out in the
  6-banded lower-triangular pattern.
* The `rfView` `LinearIsi` packaging with a placeholder white noise
  auto-covariance; the noise model itself is approximated by the
  AR(2) process in `Section06.Ar2Approximation`.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section02

/-! ## RFView tap record -/

/-- The six taps `(h_{k', 1}, ..., h_{k', 6})` of a single RFView
    channel row. -/
structure RFViewTaps where
  /-- Tap with delay `j = 1`. -/
  tap1 : Complex
  /-- Tap with delay `j = 2`. -/
  tap2 : Complex
  /-- Tap with delay `j = 3`. -/
  tap3 : Complex
  /-- Tap with delay `j = 4`. -/
  tap4 : Complex
  /-- Tap with delay `j = 5`. -/
  tap5 : Complex
  /-- Tap with delay `j = 6`. -/
  tap6 : Complex

/-- Look up a tap by delay index `j in {1, ..., 6}`.  Returns
    `Option Complex`; values outside `{1, ..., 6}` yield `none`. -/
def RFViewTaps.tap? (t : RFViewTaps) (j : Nat) : Option Complex :=
  match j with
  | 1 => some t.tap1
  | 2 => some t.tap2
  | 3 => some t.tap3
  | 4 => some t.tap4
  | 5 => some t.tap5
  | 6 => some t.tap6
  | _ => none

/-! ### Base-case lemmas for `RFViewTaps.tap?` -/

/-- `tap?` at index `0` is `none` (matches the `_` catch-all). -/
theorem RFViewTaps.tap?_zero (t : RFViewTaps) : t.tap? 0 = none := rfl

/-- `tap?` at index `1` returns `tap1`. -/
theorem RFViewTaps.tap?_one (t : RFViewTaps) : t.tap? 1 = some t.tap1 := rfl

/-- `tap?` at index `2` returns `tap2`. -/
theorem RFViewTaps.tap?_two (t : RFViewTaps) : t.tap? 2 = some t.tap2 := rfl

/-- `tap?` at index `3` returns `tap3`. -/
theorem RFViewTaps.tap?_three (t : RFViewTaps) : t.tap? 3 = some t.tap3 := rfl

/-- `tap?` at index `4` returns `tap4`. -/
theorem RFViewTaps.tap?_four (t : RFViewTaps) : t.tap? 4 = some t.tap4 := rfl

/-- `tap?` at index `5` returns `tap5`. -/
theorem RFViewTaps.tap?_five (t : RFViewTaps) : t.tap? 5 = some t.tap5 := rfl

/-- `tap?` at index `6` returns `tap6`. -/
theorem RFViewTaps.tap?_six (t : RFViewTaps) : t.tap? 6 = some t.tap6 := rfl

/-- For `7 ≤ n`, `RFViewTaps.tap? t n = none`.

    The `match` is defined by case analysis on `n` against the
    numerals `1, ..., 6` with `_ ↦ none` as the catch-all.  For
    `n = k + 7` the catch-all branch fires by structural reduction,
    so the equation is `rfl`.  For `n ∈ {0, 1, ..., 6}` the
    hypothesis `7 ≤ n` is inhabited only by an impossible chain of
    `Nat.le.step`s; `nomatch h` discharges each case. -/
theorem RFViewTaps.tap?_of_ge_seven (t : RFViewTaps) :
    forall (n : Nat), 7 <= n -> t.tap? n = none
  | 0,     h => nomatch h
  | 1,     h => nomatch h
  | 2,     h => nomatch h
  | 3,     h => nomatch h
  | 4,     h => nomatch h
  | 5,     h => nomatch h
  | 6,     h => nomatch h
  | _ + 7, _ => rfl

/-! ## The RFView channel matrix -/

/-- The RFView channel matrix of block length `n_s`, with per-row
    taps supplied by `rowTaps : Fin n_s -> RFViewTaps`.

    Matrix entry `(i, j)` is `rowTaps i .tap_{i - j + 1}` when
    `j <= i < j + 6`, and `0` otherwise.  This is the 6-banded
    lower-triangular pattern from the paper. -/
def rfViewMatrix
    (n_s : Nat) (rowTaps : Fin n_s -> RFViewTaps) : ChannelMatrix n_s :=
  fun i j =>
    if j.val <= i.val then
      ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
    else
      (0 : Complex)

/-! ## The RFView `LinearIsi` instance -/

/-- The RFView `LinearIsi` packaging.  The pre-equalisation noise
    covariance is white with variance `sigma^2`; the
    post-equalisation coloured covariance is computed in
    Section VI.B (`Section06.Ar2Approximation`). -/
def rfView
    (n_s : Nat) (rowTaps : Fin n_s -> RFViewTaps)
    (sigma : NoisePower) : LinearIsi n_s :=
  { channel := rfViewMatrix n_s rowTaps,
    noiseCov := fun i j =>
      if i.val = j.val then (sigma.val : Complex) else (0 : Complex) }

/-! ## Structural placeholders -/

/-- *Diagonal entry of `rfViewMatrix`.*  At the diagonal `i = j`, the
    delay is `d = 1` and `(rowTaps i).tap? 1 = some (rowTaps i).tap1`,
    so `Option.getD` returns `(rowTaps i).tap1`. -/
theorem rfViewMatrix_diag
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i : Fin n_s) :
    rfViewMatrix n_s rowTaps i i = (rowTaps i).tap1 :=
  let hle : i.val ≤ i.val := Nat.le_refl _
  let hsub : i.val - i.val + 1 = 1 :=
    congrArg (· + 1) (Nat.sub_self _)
  let htap : (rowTaps i).tap? (i.val - i.val + 1)
           = some (rowTaps i).tap1 :=
    hsub.symm ▸ RFViewTaps.tap?_one (rowTaps i)
  let step1 : (if i.val <= i.val then
                ((rowTaps i).tap? (i.val - i.val + 1)).getD (0 : Complex)
              else (0 : Complex))
            = ((rowTaps i).tap? (i.val - i.val + 1)).getD (0 : Complex) :=
    if_pos hle
  let step2 : ((rowTaps i).tap? (i.val - i.val + 1)).getD (0 : Complex)
            = (rowTaps i).tap1 :=
    htap ▸ rfl
  step1.trans step2

/-- *First sub-diagonal entry of `rfViewMatrix`.*  When `i.val = j.val + 1`,
    the delay is `d = 2` and the entry equals `(rowTaps i).tap2`. -/
theorem rfViewMatrix_first_subdiag
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (h : i.val = j.val + 1) :
    rfViewMatrix n_s rowTaps i j = (rowTaps i).tap2 :=
  let hle : j.val ≤ i.val := h.symm ▸ Nat.le_succ j.val
  let hd_inner : i.val - j.val = 1 :=
    h.symm ▸ Nat.add_sub_cancel_left j.val 1
  let hd : i.val - j.val + 1 = 2 :=
    congrArg (· + 1) hd_inner
  let htap : (rowTaps i).tap? (i.val - j.val + 1)
           = some (rowTaps i).tap2 :=
    hd.symm ▸ RFViewTaps.tap?_two (rowTaps i)
  let step1 : (if j.val <= i.val then
                ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
              else (0 : Complex))
            = ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex) :=
    if_pos hle
  let step2 : ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
            = (rowTaps i).tap2 :=
    htap ▸ rfl
  step1.trans step2

/-- *Second sub-diagonal entry of `rfViewMatrix`.*  When `i.val = j.val + 2`,
    the delay is `d = 3` and the entry equals `(rowTaps i).tap3`. -/
theorem rfViewMatrix_second_subdiag
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (h : i.val = j.val + 2) :
    rfViewMatrix n_s rowTaps i j = (rowTaps i).tap3 :=
  let hle : j.val ≤ i.val := h.symm ▸ Nat.le_add_right j.val 2
  let hd_inner : i.val - j.val = 2 :=
    h.symm ▸ Nat.add_sub_cancel_left j.val 2
  let hd : i.val - j.val + 1 = 3 :=
    congrArg (· + 1) hd_inner
  let htap : (rowTaps i).tap? (i.val - j.val + 1)
           = some (rowTaps i).tap3 :=
    hd.symm ▸ RFViewTaps.tap?_three (rowTaps i)
  let step1 : (if j.val <= i.val then
                ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
              else (0 : Complex))
            = ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex) :=
    if_pos hle
  let step2 : ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
            = (rowTaps i).tap3 :=
    htap ▸ rfl
  step1.trans step2

/-- *Third sub-diagonal entry of `rfViewMatrix`.*  When `i.val = j.val + 3`,
    the delay is `d = 4` and the entry equals `(rowTaps i).tap4`. -/
theorem rfViewMatrix_third_subdiag
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (h : i.val = j.val + 3) :
    rfViewMatrix n_s rowTaps i j = (rowTaps i).tap4 :=
  let hle : j.val ≤ i.val := h.symm ▸ Nat.le_add_right j.val 3
  let hd_inner : i.val - j.val = 3 :=
    h.symm ▸ Nat.add_sub_cancel_left j.val 3
  let hd : i.val - j.val + 1 = 4 :=
    congrArg (· + 1) hd_inner
  let htap : (rowTaps i).tap? (i.val - j.val + 1)
           = some (rowTaps i).tap4 :=
    hd.symm ▸ RFViewTaps.tap?_four (rowTaps i)
  let step1 : (if j.val <= i.val then
                ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
              else (0 : Complex))
            = ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex) :=
    if_pos hle
  let step2 : ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
            = (rowTaps i).tap4 :=
    htap ▸ rfl
  step1.trans step2

/-- *Fourth sub-diagonal entry of `rfViewMatrix`.*  When `i.val = j.val + 4`,
    the delay is `d = 5` and the entry equals `(rowTaps i).tap5`. -/
theorem rfViewMatrix_fourth_subdiag
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (h : i.val = j.val + 4) :
    rfViewMatrix n_s rowTaps i j = (rowTaps i).tap5 :=
  let hle : j.val ≤ i.val := h.symm ▸ Nat.le_add_right j.val 4
  let hd_inner : i.val - j.val = 4 :=
    h.symm ▸ Nat.add_sub_cancel_left j.val 4
  let hd : i.val - j.val + 1 = 5 :=
    congrArg (· + 1) hd_inner
  let htap : (rowTaps i).tap? (i.val - j.val + 1)
           = some (rowTaps i).tap5 :=
    hd.symm ▸ RFViewTaps.tap?_five (rowTaps i)
  let step1 : (if j.val <= i.val then
                ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
              else (0 : Complex))
            = ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex) :=
    if_pos hle
  let step2 : ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
            = (rowTaps i).tap5 :=
    htap ▸ rfl
  step1.trans step2

/-- *Fifth sub-diagonal entry of `rfViewMatrix`.*  When `i.val = j.val + 5`,
    the delay is `d = 6` and the entry equals `(rowTaps i).tap6`. -/
theorem rfViewMatrix_fifth_subdiag
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (h : i.val = j.val + 5) :
    rfViewMatrix n_s rowTaps i j = (rowTaps i).tap6 :=
  let hle : j.val ≤ i.val := h.symm ▸ Nat.le_add_right j.val 5
  let hd_inner : i.val - j.val = 5 :=
    h.symm ▸ Nat.add_sub_cancel_left j.val 5
  let hd : i.val - j.val + 1 = 6 :=
    congrArg (· + 1) hd_inner
  let htap : (rowTaps i).tap? (i.val - j.val + 1)
           = some (rowTaps i).tap6 :=
    hd.symm ▸ RFViewTaps.tap?_six (rowTaps i)
  let step1 : (if j.val <= i.val then
                ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
              else (0 : Complex))
            = ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex) :=
    if_pos hle
  let step2 : ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
            = (rowTaps i).tap6 :=
    htap ▸ rfl
  step1.trans step2

/-- *Sixth-position-below entry of `rfViewMatrix` is zero.*  When
    `i.val = j.val + 6`, the delay `d = 7` falls past the explicit
    tap range (1..6), so `tap?_of_ge_seven` returns `none` and
    `Option.getD` returns the default `0`.  This is the boundary
    just inside the "out of band" region. -/
theorem rfViewMatrix_at_six_below_diag
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (h : i.val = j.val + 6) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  let hle : j.val ≤ i.val := h.symm ▸ Nat.le_add_right j.val 6
  let hd_inner : i.val - j.val = 6 :=
    h.symm ▸ Nat.add_sub_cancel_left j.val 6
  let hd : i.val - j.val + 1 = 7 :=
    congrArg (· + 1) hd_inner
  let htap : (rowTaps i).tap? (i.val - j.val + 1) = none :=
    hd.symm ▸ RFViewTaps.tap?_of_ge_seven (rowTaps i) 7 (Nat.le_refl 7)
  let step1 : (if j.val <= i.val then
                ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
              else (0 : Complex))
            = ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex) :=
    if_pos hle
  let step2 : ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
            = (0 : Complex) :=
    htap ▸ rfl
  step1.trans step2

/-- The RFView channel is causal: entries above the diagonal vanish.

    Direct from the `if j.val ≤ i.val` discriminant: under `i < j`,
    the if takes the `else` branch which returns `0`. -/
theorem rfView_causal
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).causal := fun i j hij =>
  show (if j.val <= i.val then
          ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
        else (0 : Complex)) = (0 : Complex) from
    if_neg (Nat.not_le_of_lt hij)

/-- *RFView bandwidth bound.*

    For an entry `(i, j)` with `j + 6 < i`, the running delay
    `d = i - j + 1 ≥ 8 > 6` falls outside `RFViewTaps.tap?`'s
    explicit `1..6` patterns and hits the `_ ↦ none` branch, so the
    outer `match` returns `0`.

    Proof chain:
    * `j + 6 < i`  defeq  `j + 7 ≤ i`  (definition of `<` on `ℕ`).
    * `j + 7 ≤ i`  ⇒  `7 + j ≤ i`  (`Nat.add_comm`).
    * `7 + j ≤ i`  ⇒  `7 ≤ i - j`  (`Nat.le_sub_of_add_le`).
    * `7 ≤ i - j`  ⇒  `7 ≤ i - j + 1`  (`Nat.le_succ_of_le`).
    * `(rowTaps i).tap? (i - j + 1) = none`  (`tap?_of_ge_seven`).
    * Match collapses, outer `if` collapses via `if_pos`. -/
theorem rfView_bandwidth
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 6 := fun i j hij =>
  let hle : j.val <= i.val :=
    Nat.le_trans (Nat.le_add_right j.val 6) (Nat.le_of_lt hij)
  let h7add : 7 + j.val <= i.val :=
    Nat.add_comm j.val 7 ▸ (hij : j.val + 7 <= i.val)
  let hsub : 7 <= i.val - j.val := Nat.le_sub_of_add_le h7add
  let h8 : 7 <= i.val - j.val + 1 := Nat.le_succ_of_le hsub
  let htap : (rowTaps i).tap? (i.val - j.val + 1) = none :=
    RFViewTaps.tap?_of_ge_seven (rowTaps i) (i.val - j.val + 1) h8
  -- After if_pos, the goal reduces (via zeta on the `let`) to:
  --   match (rowTaps i).tap? (i.val - j.val + 1) with ... = 0
  -- The let-binding is eliminated by spelling out the matched
  -- subject explicitly in `step1.trans`, which keeps `htap`'s
  -- LHS `(rowTaps i).tap? (i.val - j.val + 1)` syntactically
  -- present in the goal so that `htap ▸ rfl` can synthesize
  -- the motive `fun x => (match x with ...) = 0`.
  let step1 : (if j.val <= i.val then
                ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
              else (0 : Complex))
            = ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex) :=
    if_pos hle
  let step2 : ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
            = (0 : Complex) :=
    htap ▸ rfl
  step1.trans step2

/-- *RFView bandwidth widens to `7`.*  One-line corollary of
    `rfView_bandwidth` composed with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_seven
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 7 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth rowTaps sigma)

/-- *RFView bandwidth widens to `8`.*  One-line corollary of
    `rfView_bandwidth_seven` composed with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_eight
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 8 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth_seven rowTaps sigma)

/-- *RFView bandwidth widens to `9`.*  Two-step corollary chaining
    `rfView_bandwidth_seven` with `LinearIsi.bandwidth_succ_succ`. -/
theorem rfView_bandwidth_nine
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 9 :=
  LinearIsi.bandwidth_succ_succ (rfView_bandwidth_seven rowTaps sigma)

/-- *RFView bandwidth widens by any additive offset.*  General
    additive form: composes `rfView_bandwidth` with
    `LinearIsi.bandwidth_add`. -/
theorem rfView_bandwidth_add
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower)
    (k : Nat) :
    (rfView n_s rowTaps sigma).bandwidth (6 + k) :=
  LinearIsi.bandwidth_add k (rfView_bandwidth rowTaps sigma)

/-- *RFView bandwidth widens to `10`.*  One-line corollary chaining
    `rfView_bandwidth_nine` with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_ten
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 10 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth_nine rowTaps sigma)

/-- *RFView bandwidth widens to `11`.*  Two-step corollary chaining
    `rfView_bandwidth_nine` with `LinearIsi.bandwidth_succ_succ`. -/
theorem rfView_bandwidth_eleven
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 11 :=
  LinearIsi.bandwidth_succ_succ (rfView_bandwidth_nine rowTaps sigma)

/-- *RFView bandwidth widens to `12`.*  Three-step corollary chaining
    `rfView_bandwidth_nine` with `LinearIsi.bandwidth_succ_succ_succ`. -/
theorem rfView_bandwidth_twelve
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 12 :=
  LinearIsi.bandwidth_succ_succ_succ (rfView_bandwidth_nine rowTaps sigma)

/-- *RFView bandwidth widens to `13`.*  One-line corollary chaining
    `rfView_bandwidth_twelve` with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_thirteen
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 13 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth_twelve rowTaps sigma)

/-- *RFView bandwidth widens to `14`.*  Two-step corollary chaining
    `rfView_bandwidth_twelve` with `LinearIsi.bandwidth_succ_succ`. -/
theorem rfView_bandwidth_fourteen
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 14 :=
  LinearIsi.bandwidth_succ_succ (rfView_bandwidth_twelve rowTaps sigma)

/-- *RFView bandwidth widens to `15`.*  Three-step corollary chaining
    `rfView_bandwidth_twelve` with `LinearIsi.bandwidth_succ_succ_succ`. -/
theorem rfView_bandwidth_fifteen
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 15 :=
  LinearIsi.bandwidth_succ_succ_succ (rfView_bandwidth_twelve rowTaps sigma)

/-- *RFView bandwidth widens to `16`.*  Chain `rfView_bandwidth_fifteen`
    with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_sixteen
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 16 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth_fifteen rowTaps sigma)

/-- *RFView bandwidth widens to `17`.*  Chain `rfView_bandwidth_fifteen`
    with `LinearIsi.bandwidth_succ_succ`. -/
theorem rfView_bandwidth_seventeen
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 17 :=
  LinearIsi.bandwidth_succ_succ (rfView_bandwidth_fifteen rowTaps sigma)

/-- *RFView bandwidth widens to `18`.*  Chain `rfView_bandwidth_fifteen`
    with `LinearIsi.bandwidth_succ_succ_succ`. -/
theorem rfView_bandwidth_eighteen
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 18 :=
  LinearIsi.bandwidth_succ_succ_succ (rfView_bandwidth_fifteen rowTaps sigma)

/-- *RFView bandwidth widens to `19`.*  Chain `rfView_bandwidth_eighteen`
    with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_nineteen
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 19 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth_eighteen rowTaps sigma)

/-- *RFView bandwidth widens to `20`.*  Chain `rfView_bandwidth_nineteen`
    with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_twenty
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 20 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth_nineteen rowTaps sigma)

/-- *RFView bandwidth widens to `21`.*  Chain `rfView_bandwidth_twenty`
    with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_twenty_one
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 21 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth_twenty rowTaps sigma)

/-- *RFView bandwidth widens to `22`.*  Chain `rfView_bandwidth_twenty_one`
    with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_twenty_two
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 22 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth_twenty_one rowTaps sigma)

/-- *RFView bandwidth widens to `23`.*  Chain `rfView_bandwidth_twenty_two`
    with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_twenty_three
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 23 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth_twenty_two rowTaps sigma)

/-- *RFView bandwidth widens to `24`.*  Chain `rfView_bandwidth_twenty_three`
    with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_twenty_four
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 24 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth_twenty_three rowTaps sigma)

/-- *RFView bandwidth widens to `25`.*  Chain `rfView_bandwidth_twenty_four`
    with `LinearIsi.bandwidth_succ`. -/
theorem rfView_bandwidth_twenty_five
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 25 :=
  LinearIsi.bandwidth_succ (rfView_bandwidth_twenty_four rowTaps sigma)

/-- *Matrix-level out-of-band statement.*  Strict bandwidth-6 form
    at the `rfViewMatrix` level (without the `LinearIsi` wrapper):
    every entry with `j + 6 < i` vanishes.  Reuses `rfView_bandwidth`
    by feeding the wrapper a zero-power `sigma`; the noise covariance
    does not enter the bandwidth proof.  Result type unifies with
    `rfViewMatrix _ _ _ _ = 0` by definitional unfolding of
    `(rfView _ _ _).channel`. -/
theorem rfViewMatrix_out_of_band
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (hij : j.val + 6 < i.val) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  rfView_bandwidth rowTaps ⟨0, le_refl 0⟩ i j hij

/-- *Zero-tap lookup is zero after `getD`.*  When every tap of `t` is
    zero, the `getD`-extracted value at any delay is zero: in-band
    delays `1..6` unwrap to `some 0`, while out-of-band delays
    (`0` or `≥ 7`) unwrap from `none` to the default `0`.  This
    is the key composition lemma for showing that a zero row of
    `rfViewMatrix` is entirely zero. -/
theorem RFViewTaps.tap?_getD_zero_of_all_zero
    (t : RFViewTaps)
    (h1 : t.tap1 = 0) (h2 : t.tap2 = 0) (h3 : t.tap3 = 0)
    (h4 : t.tap4 = 0) (h5 : t.tap5 = 0) (h6 : t.tap6 = 0) :
    forall (d : Nat), (t.tap? d).getD (0 : Complex) = (0 : Complex)
  | 0     => rfl
  | 1     => h1
  | 2     => h2
  | 3     => h3
  | 4     => h4
  | 5     => h5
  | 6     => h6
  | _ + 7 => rfl

/-- *Row of `rfViewMatrix` is zero when its taps are all zero.*
    Given a row `i` whose six taps are individually zero, every
    entry `rfViewMatrix _ rowTaps i j` is zero, regardless of `j`.
    Splits on `j.val ≤ i.val`: the lower-triangular branch uses
    `tap?_getD_zero_of_all_zero`; the upper-triangular branch is
    `0` by `if_neg`. -/
theorem rfViewMatrix_row_zero_of_taps_zero
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i : Fin n_s)
    (h1 : (rowTaps i).tap1 = 0) (h2 : (rowTaps i).tap2 = 0)
    (h3 : (rowTaps i).tap3 = 0) (h4 : (rowTaps i).tap4 = 0)
    (h5 : (rowTaps i).tap5 = 0) (h6 : (rowTaps i).tap6 = 0)
    (j : Fin n_s) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  if hle : j.val <= i.val then
    let step1 : (if j.val <= i.val then
                  ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
                else (0 : Complex))
              = ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex) :=
      if_pos hle
    let step2 : ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
              = (0 : Complex) :=
      RFViewTaps.tap?_getD_zero_of_all_zero (rowTaps i)
        h1 h2 h3 h4 h5 h6 (i.val - j.val + 1)
    step1.trans step2
  else
    if_neg hle

/-- *`rfViewMatrix` is strictly lower-triangular.*  Direct entry-level
    statement of the causality property (entries strictly above the
    diagonal vanish) at the `rfViewMatrix` level, without going
    through the `LinearIsi` wrapper.  One-line proof via `if_neg`
    on the `j.val ≤ i.val` guard of the matrix definition. -/
theorem rfViewMatrix_is_lower_triangular
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (hij : i.val < j.val) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  if_neg (Nat.not_le_of_lt hij)

/-- *Combined below-6-band zero.*  Every entry with `j + 6 ≤ i` is
    zero.  Dispatches the strict case (`j + 6 < i`) to
    `rfViewMatrix_out_of_band` and the boundary case (`j + 6 = i`)
    to `rfViewMatrix_at_six_below_diag`, via `Nat.lt_or_eq_of_le`. -/
theorem rfViewMatrix_below_6band
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (h : j.val + 6 ≤ i.val) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  match Nat.lt_or_eq_of_le h with
  | Or.inl h_lt => rfViewMatrix_out_of_band rowTaps i j h_lt
  | Or.inr h_eq =>
      rfViewMatrix_at_six_below_diag rowTaps i j h_eq.symm

/-- *Outside-band zero.*  Every entry strictly above the diagonal or
    strictly past the 5th sub-diagonal vanishes.  The 6-band region
    is exactly the complement: `j ≤ i ≤ j + 5`.  Or-elimination over
    `rfViewMatrix_is_lower_triangular` (above-diagonal) and
    `rfViewMatrix_below_6band` (below 5th sub-diagonal). -/
theorem rfViewMatrix_outside_band
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (h : i.val < j.val ∨ j.val + 6 <= i.val) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  match h with
  | Or.inl h_lt => rfViewMatrix_is_lower_triangular rowTaps i j h_lt
  | Or.inr h_ge => rfViewMatrix_below_6band rowTaps i j h_ge

/-- *Lower-triangular branch of `rfViewMatrix`.*  Whenever
    `j.val ≤ i.val`, the matrix entry is the `getD`-extracted tap
    at delay `i.val - j.val + 1`.  Direct `if_pos` exposure,
    parallel to `delayTapMatrix_apply_le`.  Useful when the
    in-band lookup needs to be reasoned about explicitly. -/
theorem rfViewMatrix_apply_le
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (h : j.val ≤ i.val) :
    rfViewMatrix n_s rowTaps i j
      = ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex) :=
  if_pos h

/-- *General sub-diagonal entry of `rfViewMatrix` via tap lookup.*
    For any offset `d` with `i.val = j.val + d`, the matrix entry
    is `((rowTaps i).tap? (d + 1)).getD 0`.  Generalises
    `rfViewMatrix_first_subdiag` through `_fifth_subdiag` and
    `rfViewMatrix_at_six_below_diag` as `d = 1, 2, 3, 4, 5, 6`
    instances; parallels `delayTapMatrix_at_subdiag`. -/
theorem rfViewMatrix_at_subdiag_via_tap
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (i j : Fin n_s) (d : Nat) (h : i.val = j.val + d) :
    rfViewMatrix n_s rowTaps i j
      = ((rowTaps i).tap? (d + 1)).getD (0 : Complex) :=
  let hle : j.val ≤ i.val := h.symm ▸ Nat.le_add_right j.val d
  let hd_inner : i.val - j.val = d :=
    h.symm ▸ Nat.add_sub_cancel_left j.val d
  let hd : i.val - j.val + 1 = d + 1 :=
    congrArg (· + 1) hd_inner
  let step1 : rfViewMatrix n_s rowTaps i j
            = ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex) :=
    rfViewMatrix_apply_le rowTaps i j hle
  let step2 : ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
            = ((rowTaps i).tap? (d + 1)).getD (0 : Complex) :=
    congrArg (fun n => ((rowTaps i).tap? n).getD (0 : Complex)) hd
  step1.trans step2

/-! ## Definitional projections of `rfView` -/

/-- *Channel of `rfView` is `rfViewMatrix`.*  Direct projection of the
    structure; parallel to `dicode_channel`.  Useful as a named API
    surface when rewriting through `rfView.channel`. -/
theorem rfView_channel
    (n_s : Nat) (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).channel = rfViewMatrix n_s rowTaps := rfl

/-- *Noise covariance of `rfView`.*  Direct projection of the
    structure, exposing the diagonal `sigma`-valued / off-diagonal
    zero white-noise pattern as a lambda.  Parallel to
    `dicode_noiseCov`; the per-entry forms are `rfView_noiseCov_diag`
    and `rfView_noiseCov_off`. -/
theorem rfView_noiseCov
    (n_s : Nat) (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).noiseCov
      = fun i j =>
          if i.val = j.val then (sigma.val : Complex) else (0 : Complex) :=
  rfl

/-! ## `rfView.noiseCov` entries -/

/-- *Diagonal entry of the rfView noise covariance.*  The
    pre-equalisation noise is white with variance `sigma^2`, so the
    diagonal of `rfView.noiseCov` is `sigma.val`.  Direct unfolding
    via `if_pos rfl`. -/
theorem rfView_noiseCov_diag
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (sigma : NoisePower) (i : Fin n_s) :
    (rfView n_s rowTaps sigma).noiseCov i i = (sigma.val : Complex) :=
  if_pos rfl

/-- *Off-diagonal entry of the rfView noise covariance.*  Whiteness
    means zero correlation between distinct sample times.  Direct
    unfolding via `if_neg`. -/
theorem rfView_noiseCov_off
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps)
    (sigma : NoisePower) (i j : Fin n_s) (h : i.val ≠ j.val) :
    (rfView n_s rowTaps sigma).noiseCov i j = (0 : Complex) :=
  if_neg h

/-- *Structural summary of `rfView`.*  Packages the two structural
    properties of the RFView channel (causality and bandwidth ≤ 6)
    into a single conjunction.  Useful when downstream code needs
    both predicates simultaneously without re-deriving each. -/
theorem rfView_structural
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).causal
      /\ (rfView n_s rowTaps sigma).bandwidth 6 :=
  ⟨rfView_causal rowTaps sigma, rfView_bandwidth rowTaps sigma⟩

end Section02
end OrbgrandAi
