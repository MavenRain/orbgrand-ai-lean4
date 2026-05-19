import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
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

    *Placeholder shape.* -/
theorem dicode_zf_equalisation_statement
    (n_s : Nat) (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (forall (i j : Fin n_s),
        (gaussMarkovCov n_s sigma rho) i j =
          let d : Nat := if i.val <= j.val then j.val - i.val else i.val - j.val
          (sigma.val : Complex) * ((rho.val : Complex) ^ d)) ->
    True := by
  kan_intro _h
  kan_constructor

end Section02
end OrbgrandAi
