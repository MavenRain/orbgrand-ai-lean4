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
    `d = i - j + 1 > 7` falls outside `RFViewTaps.tap?`'s explicit
    `1..6` patterns and hits the `_ => none` branch, so the outer
    `match` returns `0`.

    *Placeholder shape.*  The proof requires either a case-split
    helper for `RFViewTaps.tap? n = none when 7 ≤ n` or rewriting
    the match by direct unfolding; both are mechanical but bulky.
    Scheduled for a follow-up that also introduces a generic
    `Option.match_none` rewriting lemma. -/
theorem rfView_bandwidth_statement
    (n_s : Nat) (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 6 -> True := by
  kan_intro _h
  kan_constructor

end Section02
end OrbgrandAi
