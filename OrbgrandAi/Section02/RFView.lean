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
      let d : Nat := i.val - j.val + 1
      match (rowTaps i).tap? d with
      | some c => c
      | none   => (0 : Complex)
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

/-- The RFView channel is causal: entries above the diagonal vanish.

    Direct from the `if j.val ≤ i.val` discriminant: under `i < j`,
    the if takes the `else` branch which returns `0`. -/
theorem rfView_causal
    {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).causal := fun i j hij =>
  show (if j.val <= i.val then
          let d : Nat := i.val - j.val + 1
          match (rowTaps i).tap? d with
          | some c => c
          | none   => (0 : Complex)
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
                let d : Nat := i.val - j.val + 1
                match (rowTaps i).tap? d with
                | some c => c
                | none   => (0 : Complex)
              else (0 : Complex))
            = (match (rowTaps i).tap? (i.val - j.val + 1) with
               | some c => c
               | none   => (0 : Complex)) :=
    if_pos hle
  let step2 : (match (rowTaps i).tap? (i.val - j.val + 1) with
               | some c => c
               | none   => (0 : Complex))
            = (0 : Complex) :=
    htap ▸ rfl
  step1.trans step2

end Section02
end OrbgrandAi
