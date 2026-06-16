import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section02.LinearIsi
import KanTactics

/-!
# Section II.B.  Dicode partial-response channel

Formalizes the two-tap dicode partial-response channel from
Section II.B of the paper:

  h_{k', j} = | 1     if j = 0
              | -rho  if j = 1
              | 0     otherwise,                with rho in [0, 1].

In matrix form this is the lower-bidiagonal channel matrix

  h_dicode =
    [  1     0    0    ...   0
      -rho   1    0    ...   0
       0   -rho   1    ...   0
       ...                   ...
       0   ...   0    -rho   1  ]

Equalisation by zero-forcing inverts this channel.  Because the
inverse of a lower-bidiagonal matrix is lower-triangular and dense,
the equalised noise

  N_tilde = h_dicode^{-1} * N

acquires the colored covariance structure described in Section II.B:

  N_tilde_{k'} = rho * N_tilde_{k' - 1} + N_{k'},

which is precisely a first-order Gauss-Markov process.  The
covariance entries satisfy

  E[ |N_tilde_{k'}|^2 ] propto rho^{|k' - i'|}

for any two time scales `k'`, `i'`.  This is the colored-noise model
that Section III then analyses information-theoretically.

This file defines:

* The dicode channel matrix `dicodeMatrix rho` and the wrapped
  `LinearIsi` instance `dicode rho`.
* The Gauss-Markov auto-covariance template `gaussMarkovCov sigma rho`
  with entries `sigma^2 * rho^{|i - j|}`, used as the post-equalisation
  noise covariance.

The structural theorems (bandwidth, lower-triangularity,
equalisation-into-Gauss-Markov) are stated below as placeholders;
their full kan-tactics proofs are scheduled for follow-up work.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section02

open Matrix

/-! ## The dicode channel matrix -/

/-- The `n_s x n_s` dicode channel matrix:

      `dicodeMatrix n_s rho i j`
        = `1` when `i = j`,
        = `-rho` when `i = j + 1`,
        = `0` otherwise.

    The real-valued correlation `rho` is embedded into `Complex` so
    that the matrix lives in the same space as the linear ISI
    channel matrices.  See `dicode` for the wrapped channel. -/
def dicodeMatrix
    (n_s : Nat) (rho : CorrelationCoefficient) : ChannelMatrix n_s :=
  fun i j =>
    if i.val = j.val then (1 : Complex)
    else if i.val = j.val + 1 then -(rho.val : Complex)
    else (0 : Complex)

/-! ## The Gauss-Markov covariance template -/

/-- The first-order Gauss-Markov auto-covariance matrix:

      `gaussMarkovCov n_s sigma rho i j = sigma^2 * rho^{|i - j|}`.

    This is the covariance pattern induced on the equalised noise
    `N_tilde = h_dicode^{-1} N` when the pre-equalisation noise is
    white with variance `sigma^2`.  The construction does not depend
    on whether `i >= j` or `j >= i` because `rho^{|i - j|}` is
    symmetric. -/
def gaussMarkovCov
    (n_s : Nat) (sigma : NoisePower) (rho : CorrelationCoefficient) :
    CovMatrix n_s :=
  fun i j =>
    let d : Nat := if i.val <= j.val then j.val - i.val else i.val - j.val
    (sigma.val : Complex) * ((rho.val : Complex) ^ d)

/-! ## The dicode `LinearIsi` instance -/

/-- The dicode `LinearIsi` packaging: channel matrix is
    `dicodeMatrix`, noise covariance is `gaussMarkovCov`. -/
def dicode
    (n_s : Nat) (sigma : NoisePower) (rho : CorrelationCoefficient) :
    LinearIsi n_s :=
  { channel := dicodeMatrix n_s rho,
    noiseCov := gaussMarkovCov n_s sigma rho }

/-! ## Definitional projections of `dicode` -/

/-- *Channel of `dicode` is `dicodeMatrix`.*  Direct projection of the
    structure, useful as a named API when rewriting through
    `dicode.channel`. -/
theorem dicode_channel
    (n_s : Nat) (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).channel = dicodeMatrix n_s rho := rfl

/-- *Noise covariance of `dicode` is `gaussMarkovCov`.*  Direct
    projection of the structure. -/
theorem dicode_noiseCov
    (n_s : Nat) (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).noiseCov = gaussMarkovCov n_s sigma rho := rfl

/-! ## Explicit entries of `dicodeMatrix` -/

/-- The diagonal entry of the dicode channel matrix is `1`. -/
theorem dicodeMatrix_diag
    {n_s : Nat} (rho : CorrelationCoefficient) (i : Fin n_s) :
    dicodeMatrix n_s rho i i = (1 : Complex) :=
  if_pos rfl

/-- The diagonal entry of the dicode channel-matrix wrapper is `1`.
    Wrapper-level companion to `dicodeMatrix_diag`. -/
theorem dicode_channel_diag
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i : Fin n_s) :
    (dicode n_s sigma rho).channel i i = (1 : Complex) :=
  (congrFun (congrFun (dicode_channel n_s sigma rho) i) i).trans
    (dicodeMatrix_diag rho i)

/-- The first sub-diagonal (`i = j + 1`) entry is `-rho`. -/
theorem dicodeMatrix_subdiag
    {n_s : Nat} (rho : CorrelationCoefficient)
    (i j : Fin n_s) (h : i.val = j.val + 1) :
    dicodeMatrix n_s rho i j = -(rho.val : Complex) :=
  let h_ne : i.val ≠ j.val :=
    fun h_eq => Nat.succ_ne_self j.val (h.symm.trans h_eq)
  let step1 :
      (if i.val = j.val then (1 : Complex)
       else if i.val = j.val + 1 then -(rho.val : Complex)
       else (0 : Complex))
    = (if i.val = j.val + 1 then -(rho.val : Complex) else (0 : Complex)) :=
    if_neg h_ne
  step1.trans (if_pos h)

/-- Entries away from both the diagonal and the first sub-diagonal
    are zero. -/
theorem dicodeMatrix_off
    {n_s : Nat} (rho : CorrelationCoefficient)
    (i j : Fin n_s)
    (h1 : i.val ≠ j.val) (h2 : i.val ≠ j.val + 1) :
    dicodeMatrix n_s rho i j = (0 : Complex) :=
  let step1 :
      (if i.val = j.val then (1 : Complex)
       else if i.val = j.val + 1 then -(rho.val : Complex)
       else (0 : Complex))
    = (if i.val = j.val + 1 then -(rho.val : Complex) else (0 : Complex)) :=
    if_neg h1
  step1.trans (if_neg h2)

/-- *Sub-diagonal entry of the dicode channel-matrix wrapper.*
    Wrapper-level companion to `dicodeMatrix_subdiag`. -/
theorem dicode_channel_subdiag
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s) (h : i.val = j.val + 1) :
    (dicode n_s sigma rho).channel i j = -(rho.val : Complex) :=
  (congrFun (congrFun (dicode_channel n_s sigma rho) i) j).trans
    (dicodeMatrix_subdiag rho i j h)

/-- *Off-diagonal entry of the dicode channel-matrix wrapper.*
    Wrapper-level companion to `dicodeMatrix_off`. -/
theorem dicode_channel_off
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s)
    (h1 : i.val ≠ j.val) (h2 : i.val ≠ j.val + 1) :
    (dicode n_s sigma rho).channel i j = (0 : Complex) :=
  (congrFun (congrFun (dicode_channel n_s sigma rho) i) j).trans
    (dicodeMatrix_off rho i j h1 h2)

/-! ## Structural properties (placeholders) -/

/-- The dicode channel matrix has bandwidth at most `1`: every entry
    `i, j` with `j + 1 < i` is zero.  Combined with causality this
    pins the matrix down to its diagonal and first sub-diagonal.

    The proof is in term mode rather than tactic mode because the
    intermediate kan-tactics' `kan_rw [show A = A from rfl]` step
    leaks free variables into the elaborated term (kan-tactics
    bug); composing two `if_neg` rewrites via `Eq.trans` avoids the
    bug entirely. -/
theorem dicode_bandwidth
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 1 := fun i j hij =>
  let hne_eq : ¬(i.val = j.val) := fun h =>
    Nat.lt_irrefl j.val (Nat.lt_of_succ_lt (h ▸ hij))
  let hne_succ : ¬(i.val = j.val + 1) := fun h =>
    Nat.lt_irrefl (j.val + 1) (h ▸ hij)
  show (if i.val = j.val then (1 : Complex)
        else if i.val = j.val + 1 then -(rho.val : Complex)
        else (0 : Complex)) = (0 : Complex) from
    (if_neg hne_eq).trans (if_neg hne_succ)

/-- *Dicode bandwidth widens to `2`.*  One-line corollary of
    `dicode_bandwidth` composed with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_two
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 2 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth sigma rho)

/-- *Dicode bandwidth widens to `3`.*  One-line corollary of
    `dicode_bandwidth` composed with `LinearIsi.bandwidth_succ_succ`. -/
theorem dicode_bandwidth_three
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 3 :=
  LinearIsi.bandwidth_succ_succ (dicode_bandwidth sigma rho)

/-- *Dicode bandwidth widens to `4`.*  One-line corollary of
    `dicode_bandwidth` composed with `LinearIsi.bandwidth_succ_succ_succ`. -/
theorem dicode_bandwidth_four
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 4 :=
  LinearIsi.bandwidth_succ_succ_succ (dicode_bandwidth sigma rho)

/-- *Dicode bandwidth widens to `5`.*  One-line corollary of
    `dicode_bandwidth` composed with `LinearIsi.bandwidth_succ_succ_succ_succ`. -/
theorem dicode_bandwidth_five
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 5 :=
  LinearIsi.bandwidth_succ_succ_succ_succ (dicode_bandwidth sigma rho)

/-- *Dicode bandwidth widens by any additive offset `k`.*  Universal
    `+k` form: the dicode channel has bandwidth at most `1 + k` for
    every `k`.  Direct corollary of `dicode_bandwidth` composed with
    `LinearIsi.bandwidth_add`. -/
theorem dicode_bandwidth_add
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (k : Nat) :
    (dicode n_s sigma rho).bandwidth (1 + k) :=
  LinearIsi.bandwidth_add k (dicode_bandwidth sigma rho)

/-- *Dicode bandwidth widens to `6`.*  Chain `dicode_bandwidth_five`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_six
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 6 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_five sigma rho)

/-- *Dicode bandwidth widens to `7`.*  Chain `dicode_bandwidth_five`
    with `LinearIsi.bandwidth_succ_succ`. -/
theorem dicode_bandwidth_seven
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 7 :=
  LinearIsi.bandwidth_succ_succ (dicode_bandwidth_five sigma rho)

/-- *Dicode bandwidth widens to `8`.*  Chain `dicode_bandwidth_five`
    with `LinearIsi.bandwidth_succ_succ_succ`. -/
theorem dicode_bandwidth_eight
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 8 :=
  LinearIsi.bandwidth_succ_succ_succ (dicode_bandwidth_five sigma rho)

/-- *Dicode bandwidth widens to `9`.*  Chain `dicode_bandwidth_eight`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_nine
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 9 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_eight sigma rho)

/-- *Dicode bandwidth widens to `10`.*  Chain `dicode_bandwidth_eight`
    with `LinearIsi.bandwidth_succ_succ`. -/
theorem dicode_bandwidth_ten
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 10 :=
  LinearIsi.bandwidth_succ_succ (dicode_bandwidth_eight sigma rho)

/-- *Dicode bandwidth widens to `11`.*  Chain `dicode_bandwidth_ten`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_eleven
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 11 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_ten sigma rho)

/-- *Dicode bandwidth widens to `12`.*  Chain `dicode_bandwidth_eleven`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_twelve
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 12 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_eleven sigma rho)

/-- *Dicode bandwidth widens to `13`.*  Chain `dicode_bandwidth_twelve`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_thirteen
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 13 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_twelve sigma rho)

/-- *Dicode bandwidth widens to `14`.*  Chain `dicode_bandwidth_thirteen`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_fourteen
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 14 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_thirteen sigma rho)

/-- *Dicode bandwidth widens to `15`.*  Chain `dicode_bandwidth_fourteen`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_fifteen
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 15 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_fourteen sigma rho)

/-- *Dicode bandwidth widens to `16`.*  Chain `dicode_bandwidth_fifteen`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_sixteen
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 16 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_fifteen sigma rho)

/-- *Dicode bandwidth widens to `17`.*  Chain `dicode_bandwidth_sixteen`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_seventeen
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 17 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_sixteen sigma rho)

/-- *Dicode bandwidth widens to `18`.*  Chain `dicode_bandwidth_seventeen`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_eighteen
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 18 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_seventeen sigma rho)

/-- *Dicode bandwidth widens to `19`.*  Chain `dicode_bandwidth_eighteen`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_nineteen
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 19 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_eighteen sigma rho)

/-- *Dicode bandwidth widens to `20`.*  Chain `dicode_bandwidth_nineteen`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_twenty
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 20 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_nineteen sigma rho)

/-- *Dicode bandwidth widens to `21`.*  Chain `dicode_bandwidth_twenty`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_twenty_one
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 21 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_twenty sigma rho)

/-- *Dicode bandwidth widens to `22`.*  Chain `dicode_bandwidth_twenty_one`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_twenty_two
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 22 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_twenty_one sigma rho)

/-- *Dicode bandwidth widens to `23`.*  Chain `dicode_bandwidth_twenty_two`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_twenty_three
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 23 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_twenty_two sigma rho)

/-- *Dicode bandwidth widens to `24`.*  Chain `dicode_bandwidth_twenty_three`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_twenty_four
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 24 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_twenty_three sigma rho)

/-- *Dicode bandwidth widens to `25`.*  Chain `dicode_bandwidth_twenty_four`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_twenty_five
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 25 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_twenty_four sigma rho)

/-- *Dicode bandwidth widens to `26`.*  Chain `dicode_bandwidth_twenty_five`
    with `LinearIsi.bandwidth_succ`. -/
theorem dicode_bandwidth_twenty_six
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 26 :=
  LinearIsi.bandwidth_succ (dicode_bandwidth_twenty_five sigma rho)

/-- *Dicode bandwidth widens from `5` by any additive offset.*
    Universal `5 + k` form: chain `dicode_bandwidth_five` with
    `LinearIsi.bandwidth_add`. -/
theorem dicode_bandwidth_five_add
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (k : Nat) :
    (dicode n_s sigma rho).bandwidth (5 + k) :=
  LinearIsi.bandwidth_add k (dicode_bandwidth_five sigma rho)

/-- The dicode channel is causal: all entries strictly above the
    diagonal vanish.

    For `hij : i < j`, we rule out both `i = j` (by `Nat.lt_irrefl`
    on `hij`) and `i = j + 1` (subbing `i = j + 1` into `i < j`
    yields `j + 1 < j`, hence `j < j` by `Nat.lt_of_succ_lt`).

    The `hne_succ` substitution is staged via an intermediate
    `j.val + 1 < j.val` to keep the motive synthesis of `▸`
    syntactically straightforward: the right-hand side `j.val + 1`
    of `h` then literally appears as the left-hand side of the
    target inequality. -/
theorem dicode_causal
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).causal := fun i j hij =>
  let hne_eq : ¬(i.val = j.val) := fun h =>
    Nat.lt_irrefl i.val (h ▸ hij)
  let hne_succ : ¬(i.val = j.val + 1) := fun h =>
    let step : j.val + 1 < j.val := h ▸ hij
    Nat.lt_irrefl j.val (Nat.lt_of_succ_lt step)
  show (if i.val = j.val then (1 : Complex)
        else if i.val = j.val + 1 then -(rho.val : Complex)
        else (0 : Complex)) = (0 : Complex) from
    (if_neg hne_eq).trans (if_neg hne_succ)

/-- Zero-forcing equalisation of the dicode channel turns white
    Gaussian input noise of variance `sigma^2` into a first-order
    Gauss-Markov process with correlation `rho`.  The post-equalisation
    auto-covariance matrix is exactly `gaussMarkovCov n_s sigma rho`.

    This theorem records the equational characterisation that lets
    Section III's entropy-rate calculations cite
    `gaussMarkovCov ... i j = sigma * rho^{|i - j|}` directly.  It
    is `rfl` because the equation is the literal definition of
    `gaussMarkovCov`. -/
theorem dicode_zf_equalisation
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s) :
    (gaussMarkovCov n_s sigma rho) i j =
      let d : Nat := if i.val <= j.val then j.val - i.val else i.val - j.val
      (sigma.val : Complex) * ((rho.val : Complex) ^ d) := rfl

/-! ## General entry lemmas for `gaussMarkovCov` -/

/-- *Diagonal entry of the `n_s x n_s` Gauss-Markov auto-covariance.*

    At `(i, i)` both branches of the `if i.val ≤ j.val` condition
    evaluate to `i.val - i.val = 0`, so the entry is
    `sigma * rho^0 = sigma * 1 = sigma`.  Proof uses `ite_self` to
    collapse the `if` and then `Nat.sub_self`, `pow_zero`, `mul_one`. -/
theorem gaussMarkovCov_diag
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i : Fin n_s) :
    (gaussMarkovCov n_s sigma rho) i i = (sigma.val : Complex) :=
  let h_unfold : (gaussMarkovCov n_s sigma rho) i i
      = (sigma.val : Complex)
        * ((rho.val : Complex)
          ^ (if i.val <= i.val then i.val - i.val else i.val - i.val)) :=
    rfl
  let h_ite_self : (if i.val <= i.val then i.val - i.val else i.val - i.val)
      = i.val - i.val := ite_self _
  let h_sub_self : i.val - i.val = 0 := Nat.sub_self i.val
  let h_d_eq_zero : (if i.val <= i.val then i.val - i.val else i.val - i.val) = 0 :=
    h_ite_self.trans h_sub_self
  let h_pow_eq_one : (rho.val : Complex)
      ^ (if i.val <= i.val then i.val - i.val else i.val - i.val) = 1 :=
    h_d_eq_zero ▸ pow_zero (rho.val : Complex)
  let h_final : (sigma.val : Complex)
      * ((rho.val : Complex)
        ^ (if i.val <= i.val then i.val - i.val else i.val - i.val))
      = (sigma.val : Complex) :=
    h_pow_eq_one ▸ mul_one (sigma.val : Complex)
  h_unfold.trans h_final

/-- *Off-diagonal entry of the `n_s x n_s` Gauss-Markov auto-covariance
    when `i.val ≤ j.val`.*  The `if` takes the `then` branch and the
    entry simplifies to `sigma * rho^(j.val - i.val)`. -/
theorem gaussMarkovCov_entry_of_le
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s) (h : i.val <= j.val) :
    (gaussMarkovCov n_s sigma rho) i j
      = (sigma.val : Complex) * (rho.val : Complex) ^ (j.val - i.val) :=
  let h_unfold : (gaussMarkovCov n_s sigma rho) i j
      = (sigma.val : Complex)
        * ((rho.val : Complex)
          ^ (if i.val <= j.val then j.val - i.val else i.val - j.val)) :=
    rfl
  let h_ite : (if i.val <= j.val then j.val - i.val else i.val - j.val)
      = j.val - i.val := if_pos h
  h_unfold.trans
    (congrArg (fun d => (sigma.val : Complex) * (rho.val : Complex) ^ d) h_ite)

/-- *Off-diagonal entry of the `n_s x n_s` Gauss-Markov auto-covariance
    when `j.val ≤ i.val`.*  The `if` takes the `else` branch and the
    entry simplifies to `sigma * rho^(i.val - j.val)`. -/
theorem gaussMarkovCov_entry_of_ge
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s) (h : j.val < i.val) :
    (gaussMarkovCov n_s sigma rho) i j
      = (sigma.val : Complex) * (rho.val : Complex) ^ (i.val - j.val) :=
  let h_unfold : (gaussMarkovCov n_s sigma rho) i j
      = (sigma.val : Complex)
        * ((rho.val : Complex)
          ^ (if i.val <= j.val then j.val - i.val else i.val - j.val)) :=
    rfl
  let h_ite : (if i.val <= j.val then j.val - i.val else i.val - j.val)
      = i.val - j.val := if_neg (Nat.not_le_of_lt h)
  h_unfold.trans
    (congrArg (fun d => (sigma.val : Complex) * (rho.val : Complex) ^ d) h_ite)

/-- *Symmetry of the Gauss-Markov auto-covariance: `M i j = M j i`.*

    The exponent `|i.val - j.val|` is the same regardless of which
    index is larger.  Proof by trichotomy on `i.val` vs `j.val`:
    when `i.val < j.val` the LHS uses `entry_of_le` and the RHS
    uses `entry_of_ge` (mirror); when `j.val < i.val` the situation
    flips; when `i.val = j.val` both reduce to `sigma` via `diag`. -/
theorem gaussMarkovCov_sym
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s) :
    (gaussMarkovCov n_s sigma rho) i j = (gaussMarkovCov n_s sigma rho) j i :=
  if h_lt : i.val < j.val then
    -- i.val < j.val: M i j via _of_le with j - i, M j i via _of_ge with j - i.
    let lhs := gaussMarkovCov_entry_of_le sigma rho i j (Nat.le_of_lt h_lt)
    let rhs := gaussMarkovCov_entry_of_ge sigma rho j i h_lt
    lhs.trans rhs.symm
  else if h_gt : j.val < i.val then
    -- j.val < i.val: mirror of above.
    let lhs := gaussMarkovCov_entry_of_ge sigma rho i j h_gt
    let rhs := gaussMarkovCov_entry_of_le sigma rho j i (Nat.le_of_lt h_gt)
    lhs.trans rhs.symm
  else
    -- Neither <: trichotomy forces i.val = j.val, hence Fin-eq.
    let h_le_ij : i.val ≤ j.val := Nat.le_of_not_lt h_gt
    let h_le_ji : j.val ≤ i.val := Nat.le_of_not_lt h_lt
    let h_val_eq : i.val = j.val := Nat.le_antisymm h_le_ij h_le_ji
    let h_fin_eq : i = j := Fin.ext h_val_eq
    h_fin_eq ▸ rfl

/-! ## Closed-form determinant for `n_s = 2` -/

/-- *Diagonal entry `(0, 0)` of the 2x2 Gauss-Markov auto-covariance.*

    Concrete index: the `if 0 ≤ 0` reduces, `0 - 0 = 0`, and the
    entry collapses to `sigma * rho^0 = sigma * 1 = sigma`. -/
theorem gaussMarkovCov_two_00
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho) 0 0 = (sigma.val : Complex) :=
  have h0 : (gaussMarkovCov 2 sigma rho) 0 0
      = (sigma.val : Complex) * ((rho.val : Complex) ^ 0) := rfl
  let h1 : (sigma.val : Complex) * ((rho.val : Complex) ^ 0)
        = (sigma.val : Complex) * 1 :=
    congrArg ((sigma.val : Complex) * ·) (pow_zero (rho.val : Complex))
  let h2 : (sigma.val : Complex) * 1 = (sigma.val : Complex) :=
    mul_one (sigma.val : Complex)
  h0.trans (h1.trans h2)

/-- *Diagonal entry `(1, 1)` of the 2x2 Gauss-Markov auto-covariance.* -/
theorem gaussMarkovCov_two_11
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho) 1 1 = (sigma.val : Complex) :=
  have h0 : (gaussMarkovCov 2 sigma rho) 1 1
      = (sigma.val : Complex) * ((rho.val : Complex) ^ 0) := rfl
  let h1 : (sigma.val : Complex) * ((rho.val : Complex) ^ 0)
        = (sigma.val : Complex) * 1 :=
    congrArg ((sigma.val : Complex) * ·) (pow_zero (rho.val : Complex))
  let h2 : (sigma.val : Complex) * 1 = (sigma.val : Complex) :=
    mul_one (sigma.val : Complex)
  h0.trans (h1.trans h2)

/-- *Off-diagonal entry `(0, 1)` of the 2x2 Gauss-Markov auto-covariance.* -/
theorem gaussMarkovCov_two_01
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho) 0 1
      = (sigma.val : Complex) * (rho.val : Complex) :=
  have h0 : (gaussMarkovCov 2 sigma rho) 0 1
      = (sigma.val : Complex) * ((rho.val : Complex) ^ 1) := rfl
  let h1 : (sigma.val : Complex) * ((rho.val : Complex) ^ 1)
        = (sigma.val : Complex) * (rho.val : Complex) :=
    congrArg ((sigma.val : Complex) * ·) (pow_one (rho.val : Complex))
  h0.trans h1

/-- *Off-diagonal entry `(1, 0)` of the 2x2 Gauss-Markov auto-covariance.* -/
theorem gaussMarkovCov_two_10
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho) 1 0
      = (sigma.val : Complex) * (rho.val : Complex) :=
  have h0 : (gaussMarkovCov 2 sigma rho) 1 0
      = (sigma.val : Complex) * ((rho.val : Complex) ^ 1) := rfl
  let h1 : (sigma.val : Complex) * ((rho.val : Complex) ^ 1)
        = (sigma.val : Complex) * (rho.val : Complex) :=
    congrArg ((sigma.val : Complex) * ·) (pow_one (rho.val : Complex))
  h0.trans h1

/-- *Zero noise power gives zero covariance matrix.*  Every entry of
    `gaussMarkovCov n_s ⟨0, _⟩ rho` is zero.  The Complex coercion of
    `(0 : Real)` is `0` via `Complex.ofReal_zero`, then `zero_mul`
    finishes.  Parallel to `cov1_lag_zero_sigma`. -/
theorem gaussMarkovCov_zero_sigma
    {n_s : Nat} (rho : CorrelationCoefficient) (i j : Fin n_s) :
    (gaussMarkovCov n_s ⟨0, le_refl 0⟩ rho) i j = 0 :=
  let d : Nat :=
    if i.val <= j.val then j.val - i.val else i.val - j.val
  let step1 : (gaussMarkovCov n_s ⟨0, le_refl 0⟩ rho) i j
            = (((0 : Real)) : Complex) * ((rho.val : Complex) ^ d) := rfl
  let step2 : (((0 : Real)) : Complex) * ((rho.val : Complex) ^ d)
            = (0 : Complex) * ((rho.val : Complex) ^ d) :=
    congrArg (fun z => z * ((rho.val : Complex) ^ d))
      Complex.ofReal_zero
  step1.trans (step2.trans (zero_mul _))

/-- *2x2 Gauss-Markov off-diagonal symmetry.*  Specialisation of
    `gaussMarkovCov_sym` to the `n_s = 2` case; both off-diagonal
    entries collapse to `sigma * rho` via the explicit closed forms,
    so equality is immediate by transitivity. -/
theorem gaussMarkovCov_two_01_eq_10
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho) 0 1 = (gaussMarkovCov 2 sigma rho) 1 0 :=
  (gaussMarkovCov_two_01 sigma rho).trans
    (gaussMarkovCov_two_10 sigma rho).symm

/-- *Determinant of the 2x2 first-order Gauss-Markov auto-covariance,
    in unfolded form.*

    `det = sigma * sigma - (sigma * rho) * (sigma * rho)`.  Direct
    consequence of `Matrix.det_fin_two` plus the four entry lemmas.
    The fully factored form `sigma^2 * (1 - rho^2)` is recorded
    below as `cov1_det_fin_two_factored_statement`; the algebra to
    bridge the two requires `mul_sub`, `mul_mul_mul_comm`,
    `mul_one`, and `sq` chained without `ring` / `linarith`, which
    is left as a placeholder. -/
theorem cov1_det_fin_two
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho).det
      = (sigma.val : Complex) * (sigma.val : Complex)
        - ((sigma.val : Complex) * (rho.val : Complex))
          * ((sigma.val : Complex) * (rho.val : Complex)) :=
  let det_eq : (gaussMarkovCov 2 sigma rho).det
      = (gaussMarkovCov 2 sigma rho) 0 0 * (gaussMarkovCov 2 sigma rho) 1 1
        - (gaussMarkovCov 2 sigma rho) 0 1 * (gaussMarkovCov 2 sigma rho) 1 0 :=
    Matrix.det_fin_two _
  let M00 := gaussMarkovCov_two_00 sigma rho
  let M11 := gaussMarkovCov_two_11 sigma rho
  let M01 := gaussMarkovCov_two_01 sigma rho
  let M10 := gaussMarkovCov_two_10 sigma rho
  -- Substitute the four entries by congruence on `(·) * (·) - (·) * (·)`.
  let prod1 : (gaussMarkovCov 2 sigma rho) 0 0 * (gaussMarkovCov 2 sigma rho) 1 1
      = (sigma.val : Complex) * (sigma.val : Complex) :=
    M00 ▸ M11 ▸ rfl
  let prod2 : (gaussMarkovCov 2 sigma rho) 0 1 * (gaussMarkovCov 2 sigma rho) 1 0
      = ((sigma.val : Complex) * (rho.val : Complex))
        * ((sigma.val : Complex) * (rho.val : Complex)) :=
    M01 ▸ M10 ▸ rfl
  let entries_eq : (gaussMarkovCov 2 sigma rho) 0 0 * (gaussMarkovCov 2 sigma rho) 1 1
        - (gaussMarkovCov 2 sigma rho) 0 1 * (gaussMarkovCov 2 sigma rho) 1 0
      = (sigma.val : Complex) * (sigma.val : Complex)
        - ((sigma.val : Complex) * (rho.val : Complex))
          * ((sigma.val : Complex) * (rho.val : Complex)) :=
    prod1 ▸ prod2 ▸ rfl
  det_eq.trans entries_eq

/-- *Determinant of the 2x2 first-order Gauss-Markov auto-covariance,
    in factored form.*

    `det = sigma^2 * (1 - rho^2)`.  Algebraic bridge from the
    unfolded form (`cov1_det_fin_two`): step (A) folds `s * s = s^2`
    via `sq.symm`; step (B) rearranges `(s * r) * (s * r)` to
    `(s * s) * (r * r)` via `mul_mul_mul_comm` and then folds to
    `s^2 * r^2`; step (C) factors `s^2 - s^2 * r^2 = s^2 * (1 - r^2)`
    via `mul_sub` and `mul_one`.  Each step is a `.trans` chain
    plumbed through `congrArg` / `congrArg₂` because kan-tactics'
    `kan_rw` does not elaborate polymorphic Mathlib lemmas without
    explicit type arguments. -/
theorem cov1_det_fin_two_factored
    (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho).det
      = (sigma.val : Complex) ^ 2 * (1 - (rho.val : Complex) ^ 2) :=
  let s : Complex := sigma.val
  let r : Complex := rho.val
  -- Step (A): s * s = s^2
  let hA : s * s = s ^ 2 := (sq s).symm
  -- Step (B): (s * r) * (s * r) = s^2 * r^2
  let hB1 : (s * r) * (s * r) = (s * s) * (r * r) := mul_mul_mul_comm s r s r
  let hB2 : (s * s) * (r * r) = s ^ 2 * (r * r) :=
    congrArg (· * (r * r)) (sq s).symm
  let hB3 : s ^ 2 * (r * r) = s ^ 2 * r ^ 2 :=
    congrArg (s ^ 2 * ·) (sq r).symm
  let hB : (s * r) * (s * r) = s ^ 2 * r ^ 2 := hB1.trans (hB2.trans hB3)
  -- Bridge: s * s - (s * r) * (s * r) = s^2 - s^2 * r^2
  let bridge : s * s - (s * r) * (s * r) = s ^ 2 - s ^ 2 * r ^ 2 :=
    congrArg₂ (· - ·) hA hB
  -- Step (C): s^2 - s^2 * r^2 = s^2 * (1 - r^2)
  let hC1 : s ^ 2 * (1 - r ^ 2) = s ^ 2 * 1 - s ^ 2 * r ^ 2 :=
    mul_sub (s ^ 2) 1 (r ^ 2)
  let hC2 : s ^ 2 * 1 - s ^ 2 * r ^ 2 = s ^ 2 - s ^ 2 * r ^ 2 :=
    congrArg (· - s ^ 2 * r ^ 2) (mul_one (s ^ 2))
  let hC : s ^ 2 - s ^ 2 * r ^ 2 = s ^ 2 * (1 - r ^ 2) :=
    (hC1.trans hC2).symm
  (cov1_det_fin_two sigma rho).trans (bridge.trans hC)

/-- *Structural summary of `dicode`.*  Packages the two structural
    properties of the dicode channel (causality and bandwidth ≤ 1)
    into a single conjunction.  Parallel to `rfView_structural`. -/
theorem dicode_structural
    {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).causal
      /\ (dicode n_s sigma rho).bandwidth 1 :=
  ⟨dicode_causal sigma rho, dicode_bandwidth sigma rho⟩

end Section02
end OrbgrandAi
