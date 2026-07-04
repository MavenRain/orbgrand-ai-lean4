import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import OrbgrandAi.Section00.Probability
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

/-- *Alternate form of `perturbChannel_zero`.*  Reads the identity
    in the opposite direction: the original channel `h` equals its
    zero-perturbed form.  Pure `.symm` of `perturbChannel_zero`. -/
theorem perturbChannel_zero_eq_self
    {n_s : Nat} (h : ChannelMatrix n_s) :
    h = perturbChannel h 0 :=
  (perturbChannel_zero h).symm

/-- *Pointwise zero perturbation is the identity.*  Entry form of
    `perturbChannel_zero`: the zero-perturbed channel agrees with
    `h i j` entrywise.  Pure `congrFun` cascade. -/
theorem perturbChannel_zero_apply
    {n_s : Nat} (h : ChannelMatrix n_s) (i j : Fin n_s) :
    perturbChannel h 0 i j = h i j :=
  congrFun (congrFun (perturbChannel_zero h) i) j

/-- *Diagonal pointwise zero perturbation.*  Specialisation of
    `perturbChannel_zero_apply` at `i = j`. -/
theorem perturbChannel_zero_apply_diag
    {n_s : Nat} (h : ChannelMatrix n_s) (i : Fin n_s) :
    perturbChannel h 0 i i = h i i :=
  perturbChannel_zero_apply h i i

/-- *Pointwise reverse-direction zero perturbation.*  Entry form
    of `perturbChannel_zero_eq_self`: the original entry `h i j`
    equals the zero-perturbed entry.  Pure `congrFun` cascade. -/
theorem perturbChannel_zero_eq_self_apply
    {n_s : Nat} (h : ChannelMatrix n_s) (i j : Fin n_s) :
    h i j = perturbChannel h 0 i j :=
  congrFun (congrFun (perturbChannel_zero_eq_self h) i) j

/-- *Diagonal reverse-direction zero perturbation.*  Specialisation
    of `perturbChannel_zero_eq_self_apply` at `i = j`: the original
    diagonal entry `h i i` equals the zero-perturbed diagonal entry. -/
theorem perturbChannel_zero_eq_self_apply_diag
    {n_s : Nat} (h : ChannelMatrix n_s) (i : Fin n_s) :
    h i i = perturbChannel h 0 i i :=
  perturbChannel_zero_eq_self_apply h i i

/-- *Zero channel stays zero under perturbation.*  When the underlying
    channel matrix is zero, the perturbed channel is also zero
    (regardless of the error matrix).  Each entry becomes
    `0 * (1 + epsilon i j) = 0` via `zero_mul`. -/
theorem perturbChannel_zero_channel
    {n_s : Nat} (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) :
    perturbChannel 0 epsilon = 0 :=
  funext fun i => funext fun j => zero_mul (1 + epsilon i j)

/-- *Pointwise zero-channel under perturbation.*  Entry form of
    `perturbChannel_zero_channel`: each entry of the zero-channel
    perturbed by any `epsilon` is `0`.  Pure `congrFun` cascade. -/
theorem perturbChannel_zero_channel_apply
    {n_s : Nat} (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    (i j : Fin n_s) :
    perturbChannel 0 epsilon i j = (0 : ChannelMatrix n_s) i j :=
  congrFun (congrFun (perturbChannel_zero_channel epsilon) i) j

/-- *Diagonal zero-channel under perturbation.*  Specialisation of
    `perturbChannel_zero_channel_apply` at `i = j`. -/
theorem perturbChannel_zero_channel_apply_diag
    {n_s : Nat} (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    (i : Fin n_s) :
    perturbChannel 0 epsilon i i = (0 : ChannelMatrix n_s) i i :=
  perturbChannel_zero_channel_apply epsilon i i

/-- *Diagonal reverse-direction zero-channel under perturbation.*
    Reverse of `perturbChannel_zero_channel_apply_diag`: the zero-channel
    diagonal entry equals the perturbed-zero-channel diagonal entry. -/
theorem perturbChannel_zero_channel_eq_self_apply_diag
    {n_s : Nat} (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    (i : Fin n_s) :
    (0 : ChannelMatrix n_s) i i = perturbChannel 0 epsilon i i :=
  (perturbChannel_zero_channel_apply_diag epsilon i).symm

/-- *Pointwise zero-channel under zero perturbation.*  Joint
    specialisation of `perturbChannel_zero_channel_apply` at
    `epsilon = 0`: when both the channel and the perturbation are
    zero, every entry is the zero-matrix entry. -/
theorem perturbChannel_zero_channel_zero_apply
    {n_s : Nat} (i j : Fin n_s) :
    perturbChannel (0 : ChannelMatrix n_s) 0 i j
      = (0 : ChannelMatrix n_s) i j :=
  perturbChannel_zero_channel_apply 0 i j

/-- *Diagonal specialisation of `perturbChannel_zero_channel_zero_apply`.*
    When both the channel and the perturbation are zero, the diagonal
    entry `(i, i)` agrees with the zero-matrix diagonal entry. -/
theorem perturbChannel_zero_channel_zero_apply_diag
    {n_s : Nat} (i : Fin n_s) :
    perturbChannel (0 : ChannelMatrix n_s) 0 i i
      = (0 : ChannelMatrix n_s) i i :=
  perturbChannel_zero_channel_zero_apply i i

/-- *Matrix-level zero-channel under zero perturbation.*  Specialisation
    of `perturbChannel_zero_channel` at `epsilon = 0`: when both the
    channel and the perturbation are zero matrices, the perturbed
    channel is the zero matrix. -/
theorem perturbChannel_zero_channel_zero
    {n_s : Nat} :
    perturbChannel (0 : ChannelMatrix n_s) 0 = 0 :=
  perturbChannel_zero_channel 0

/-- *Matrix-level reverse form of `perturbChannel_zero_channel_zero`.*
    The zero matrix equals the doubly-zero-perturbed channel.  Pure
    `.symm`. -/
theorem perturbChannel_zero_channel_zero_eq_self
    {n_s : Nat} :
    (0 : ChannelMatrix n_s) = perturbChannel (0 : ChannelMatrix n_s) 0 :=
  perturbChannel_zero_channel_zero.symm

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

/-- *Diagonal entry of composed perturbation.*  Specialisation of
    `perturbChannel_perturbChannel_apply` at `i = j`. -/
theorem perturbChannel_perturbChannel_apply_diag
    {n_s : Nat} (h : ChannelMatrix n_s)
    (ε₁ ε₂ : Matrix (Fin n_s) (Fin n_s) Complex)
    (i : Fin n_s) :
    perturbChannel (perturbChannel h ε₁) ε₂ i i
      = h i i * ((1 + ε₁ i i) * (1 + ε₂ i i)) :=
  perturbChannel_perturbChannel_apply h ε₁ ε₂ i i

/-- *Right-identity of composed perturbation.*  Composing a
    perturbation with the zero perturbation on the right collapses
    to the original perturbation.  Direct one-line specialisation
    of `perturbChannel_zero` to the already-perturbed channel. -/
theorem perturbChannel_perturbChannel_zero_right
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) :
    perturbChannel (perturbChannel h epsilon) 0 = perturbChannel h epsilon :=
  perturbChannel_zero (perturbChannel h epsilon)

/-- *Left-identity of composed perturbation.*  Perturbing first by
    the zero matrix and then by `epsilon` is equivalent to
    perturbing once by `epsilon`.  One-line `congrArg` rewriting
    the inner `perturbChannel h 0` to `h` via `perturbChannel_zero`. -/
theorem perturbChannel_perturbChannel_zero_left
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) :
    perturbChannel (perturbChannel h 0) epsilon = perturbChannel h epsilon :=
  congrArg (fun H => perturbChannel H epsilon) (perturbChannel_zero h)

/-- *Zero-zero composition collapses to identity.*  Composing two
    zero perturbations leaves the channel unchanged.  Lift the
    inner perturbation to `h` via `congrArg` + `perturbChannel_zero`,
    then collapse the outer perturbation by `perturbChannel_zero`. -/
theorem perturbChannel_perturbChannel_zero_zero
    {n_s : Nat} (h : ChannelMatrix n_s) :
    perturbChannel (perturbChannel h 0) 0 = h :=
  (congrArg (fun H => perturbChannel H 0) (perturbChannel_zero h)).trans
    (perturbChannel_zero h)

/-- *Triple zero-perturbation collapses to identity.*  Composing three
    zero perturbations on `h` leaves the channel unchanged.  Extends
    the binary form `perturbChannel_perturbChannel_zero_zero` to a
    third layer. -/
theorem perturbChannel_perturbChannel_perturbChannel_zero_zero_zero
    {n_s : Nat} (h : ChannelMatrix n_s) :
    perturbChannel (perturbChannel (perturbChannel h 0) 0) 0 = h :=
  (perturbChannel_zero (perturbChannel (perturbChannel h 0) 0)).trans
    (perturbChannel_perturbChannel_zero_zero h)

/-- *Pointwise triple zero-perturbation collapse.*  Entry form of
    `perturbChannel_perturbChannel_perturbChannel_zero_zero_zero`. -/
theorem perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_apply
    {n_s : Nat} (h : ChannelMatrix n_s) (i j : Fin n_s) :
    perturbChannel (perturbChannel (perturbChannel h 0) 0) 0 i j = h i j :=
  congrFun
    (congrFun (perturbChannel_perturbChannel_perturbChannel_zero_zero_zero h) i) j

/-- *Diagonal pointwise triple zero-perturbation collapse.*
    Specialisation at `i = j`. -/
theorem perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_apply_diag
    {n_s : Nat} (h : ChannelMatrix n_s) (i : Fin n_s) :
    perturbChannel (perturbChannel (perturbChannel h 0) 0) 0 i i = h i i :=
  perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_apply h i i

/-- *Reverse-direction matrix-level zero-zero composition.*  Reads
    the identity `perturbChannel (perturbChannel h 0) 0 = h` in the
    canonical "expand `h` into its doubly-zero-perturbed form"
    direction.  Pure `.symm` of
    `perturbChannel_perturbChannel_zero_zero`. -/
theorem perturbChannel_perturbChannel_zero_zero_eq_self
    {n_s : Nat} (h : ChannelMatrix n_s) :
    h = perturbChannel (perturbChannel h 0) 0 :=
  (perturbChannel_perturbChannel_zero_zero h).symm

/-- *Pointwise zero-zero composition.*  Entry form of
    `perturbChannel_perturbChannel_zero_zero`: composing two zero
    perturbations recovers the original entry `h i j`.  One-line
    `congrFun` cascade over the matrix-level equality. -/
theorem perturbChannel_perturbChannel_zero_zero_apply
    {n_s : Nat} (h : ChannelMatrix n_s) (i j : Fin n_s) :
    perturbChannel (perturbChannel h 0) 0 i j = h i j :=
  congrFun (congrFun (perturbChannel_perturbChannel_zero_zero h) i) j

/-- *Pointwise reverse-direction zero-zero composition.*  Entry form
    of the reverse-direction zero-zero composition equality: the
    original entry `h i j` equals the doubly-zero-perturbed entry.
    Pure `.symm` of `perturbChannel_perturbChannel_zero_zero_apply`. -/
theorem perturbChannel_perturbChannel_zero_zero_eq_self_apply
    {n_s : Nat} (h : ChannelMatrix n_s) (i j : Fin n_s) :
    h i j = perturbChannel (perturbChannel h 0) 0 i j :=
  (perturbChannel_perturbChannel_zero_zero_apply h i j).symm

/-- *Zero channel survives double perturbation.*  Composing two
    perturbations on the zero channel still yields the zero channel,
    regardless of either error matrix.  Symmetric counterpart of
    `perturbChannel_perturbChannel_zero_zero` (which fixes the two
    error matrices at zero): here the underlying channel is fixed at
    zero and the error matrices are arbitrary.  Lift the inner
    `perturbChannel 0 ε₁ = 0` via `congrArg`, then collapse the
    outer perturbation by `perturbChannel_zero_channel`. -/
theorem perturbChannel_perturbChannel_zero_channel
    {n_s : Nat} (ε₁ ε₂ : Matrix (Fin n_s) (Fin n_s) Complex) :
    perturbChannel (perturbChannel 0 ε₁) ε₂ = 0 :=
  (congrArg (fun H => perturbChannel H ε₂) (perturbChannel_zero_channel ε₁)).trans
    (perturbChannel_zero_channel ε₂)

/-- *Pointwise double-perturbation of the zero channel.*  Entry
    form of `perturbChannel_perturbChannel_zero_channel`: each entry
    of the doubly-perturbed zero channel agrees with the corresponding
    entry of the zero channel.  Pure `congrFun` cascade. -/
theorem perturbChannel_perturbChannel_zero_channel_apply
    {n_s : Nat} (ε₁ ε₂ : Matrix (Fin n_s) (Fin n_s) Complex)
    (i j : Fin n_s) :
    perturbChannel (perturbChannel 0 ε₁) ε₂ i j
      = (0 : ChannelMatrix n_s) i j :=
  congrFun (congrFun (perturbChannel_perturbChannel_zero_channel ε₁ ε₂) i) j

/-- *Diagonal entry under double zero-channel perturbation.*
    Specialisation of `perturbChannel_perturbChannel_zero_channel_apply`
    at `i = j`: the doubly-perturbed zero channel agrees with the
    zero channel on the diagonal. -/
theorem perturbChannel_perturbChannel_zero_channel_apply_diag
    {n_s : Nat} (ε₁ ε₂ : Matrix (Fin n_s) (Fin n_s) Complex)
    (i : Fin n_s) :
    perturbChannel (perturbChannel 0 ε₁) ε₂ i i
      = (0 : ChannelMatrix n_s) i i :=
  perturbChannel_perturbChannel_zero_channel_apply ε₁ ε₂ i i

/-- *Diagonal entry under double zero-zero composition.*
    Specialisation of `perturbChannel_perturbChannel_zero_zero_apply`
    at `i = j`. -/
theorem perturbChannel_perturbChannel_zero_zero_apply_diag
    {n_s : Nat} (h : ChannelMatrix n_s) (i : Fin n_s) :
    perturbChannel (perturbChannel h 0) 0 i i = h i i :=
  perturbChannel_perturbChannel_zero_zero_apply h i i

/-- *Diagonal reverse-direction zero-zero composition.*  Reverse of
    `perturbChannel_perturbChannel_zero_zero_apply_diag`: the original
    diagonal entry equals the doubly-zero-perturbed diagonal entry. -/
theorem perturbChannel_perturbChannel_zero_zero_eq_self_apply_diag
    {n_s : Nat} (h : ChannelMatrix n_s) (i : Fin n_s) :
    h i i = perturbChannel (perturbChannel h 0) 0 i i :=
  (perturbChannel_perturbChannel_zero_zero_apply_diag h i).symm

/-- *Pointwise right-identity of composed perturbation.*  Entry
    form of `perturbChannel_perturbChannel_zero_right`: composing a
    perturbation with the zero perturbation on the right leaves the
    entry unchanged.  Pure `congrFun` cascade. -/
theorem perturbChannel_perturbChannel_zero_right_apply
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i j : Fin n_s) :
    perturbChannel (perturbChannel h epsilon) 0 i j
      = perturbChannel h epsilon i j :=
  congrFun (congrFun (perturbChannel_perturbChannel_zero_right h epsilon) i) j

/-- *Diagonal right-identity of composed perturbation.*
    Specialisation of `perturbChannel_perturbChannel_zero_right_apply`
    at `i = j`. -/
theorem perturbChannel_perturbChannel_zero_right_apply_diag
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i : Fin n_s) :
    perturbChannel (perturbChannel h epsilon) 0 i i
      = perturbChannel h epsilon i i :=
  perturbChannel_perturbChannel_zero_right_apply h epsilon i i

/-- *Pointwise left-identity of composed perturbation.*  Entry
    form of `perturbChannel_perturbChannel_zero_left`: perturbing
    first by zero and then by `epsilon` agrees with a single
    `epsilon` perturbation entrywise.  Pure `congrFun` cascade. -/
theorem perturbChannel_perturbChannel_zero_left_apply
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i j : Fin n_s) :
    perturbChannel (perturbChannel h 0) epsilon i j
      = perturbChannel h epsilon i j :=
  congrFun (congrFun (perturbChannel_perturbChannel_zero_left h epsilon) i) j

/-- *Diagonal left-identity of composed perturbation.*
    Specialisation of `perturbChannel_perturbChannel_zero_left_apply`
    at `i = j`. -/
theorem perturbChannel_perturbChannel_zero_left_apply_diag
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i : Fin n_s) :
    perturbChannel (perturbChannel h 0) epsilon i i
      = perturbChannel h epsilon i i :=
  perturbChannel_perturbChannel_zero_left_apply h epsilon i i

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

/-- *Diagonal pointwise identity at zero perturbation.*
    Specialisation of `perturbChannel_eps_zero_apply` at `i = j`:
    when the diagonal error `epsilon i i` vanishes, the perturbed
    diagonal entry equals `h i i`. -/
theorem perturbChannel_eps_zero_apply_diag
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i : Fin n_s} (h_eps : epsilon i i = 0) :
    perturbChannel h epsilon i i = h i i :=
  perturbChannel_eps_zero_apply h epsilon h_eps

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

/-- *Diagonal pure cancellation: `epsilon i i = -1` zeroes the diagonal
    entry.*  Specialisation of `perturbChannel_neg_one_attenuation_eq_zero`
    at `i = j`. -/
theorem perturbChannel_neg_one_attenuation_eq_zero_apply_diag
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i : Fin n_s} (h_eps : epsilon i i = -1) :
    perturbChannel h epsilon i i = 0 :=
  perturbChannel_neg_one_attenuation_eq_zero h epsilon h_eps

/-- *Factor-zero zeroes the entry.*  When the multiplicative factor
    `1 + epsilon i j` vanishes, the perturbed entry is zero
    regardless of `h i j`.  Generalisation of
    `perturbChannel_neg_one_attenuation_eq_zero` that takes the
    factor-zero hypothesis directly. -/
theorem perturbChannel_factor_zero_apply
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i j : Fin n_s} (h_factor : (1 : Complex) + epsilon i j = 0) :
    perturbChannel h epsilon i j = 0 :=
  (congrArg (h i j * ·) h_factor).trans (mul_zero (h i j))

/-- *Diagonal factor-zero zeroes the entry.*  Specialisation of
    `perturbChannel_factor_zero_apply` at `i = j`: when the diagonal
    multiplicative factor `1 + epsilon i i` vanishes, the perturbed
    diagonal entry is zero regardless of `h i i`. -/
theorem perturbChannel_factor_zero_apply_diag
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i : Fin n_s} (h_factor : (1 : Complex) + epsilon i i = 0) :
    perturbChannel h epsilon i i = 0 :=
  perturbChannel_factor_zero_apply h epsilon h_factor

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

/-- *Diagonal zero characterisation.*  Specialisation of
    `perturbChannel_eq_zero_iff` at `i = j`: a perturbed diagonal
    entry vanishes iff either the underlying diagonal entry vanishes
    or the diagonal multiplicative factor `1 + epsilon i i` is zero. -/
theorem perturbChannel_eq_zero_iff_diag
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    (i : Fin n_s) :
    perturbChannel h epsilon i i = 0
      <-> h i i = 0 ∨ 1 + epsilon i i = 0 :=
  perturbChannel_eq_zero_iff h epsilon i i

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

/-- *Diagonal pointwise zero preservation.*  Specialisation of
    `perturbChannel_zero_entry` at `i = j`: if a single diagonal entry
    `h i i` is zero, the corresponding perturbed diagonal entry is
    also zero, for any error matrix. -/
theorem perturbChannel_zero_entry_diag
    {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i : Fin n_s} (hzero : h i i = 0) :
    perturbChannel h epsilon i i = 0 :=
  perturbChannel_zero_entry h epsilon hzero

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

    *Statement form, probabilistic.*  Now that
    `OrbgrandAi.Section00.Probability` provides the AWGN noise measure
    and the `bler` operator, this theorem quantifies over the actual
    decoder under imperfect CSI, and asks for a positive lower bound
    on `Section00.bler sigma decode` uniformly in the per-SNR
    decoder family.

    The decoder family is parameterised by a per-SNR-`sigma`
    `decoder` function returning a `Bool`-valued failure indicator
    on `RealSymbolVector n_s`; this is the receiver-side projection
    of an imperfect-CSI ORBGRAND-AI run with reference codeword
    fixed.  The probabilistic content lives in `bler`, not the
    decoder itself.

    *Why deferred to `True`.*  The actual proof of the error-floor
    inequality requires the analytic apparatus of Section VI.B (the
    AR(2) residual bound) plus the Gaussian tail estimate; both are
    out of scope for this statement file, which only locks the
    quantifier shape.  Once those are in place the closing
    `True` may be replaced by a real claim. -/
theorem imperfect_csi_error_floor_statement
    (nmse : NMSE) (sigma : NoisePower)
    (rho : CorrelationCoefficient) :
    (0 < nmse.val ->
      exists (floor : Real),
        0 < floor /\
        forall {n_s : Nat}
          (decoder : NoisePower -> Section00.RealSymbolVector n_s -> Bool),
          forall (snrSigma : NoisePower), snrSigma.val <= sigma.val ->
            floor <= Section00.bler snrSigma (decoder snrSigma)) -> True := by
  kan_intro _h
  kan_constructor

/-- *Quadruple zero-perturbation collapses to identity.*  Composing four
    zero perturbations on `h` leaves the channel unchanged.  Extends the
    triple form `perturbChannel_perturbChannel_perturbChannel_zero_zero_zero`
    to a fourth layer. -/
theorem perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero
    {n_s : Nat} (h : ChannelMatrix n_s) :
    perturbChannel (perturbChannel (perturbChannel (perturbChannel h 0) 0) 0) 0 = h :=
  (perturbChannel_zero (perturbChannel (perturbChannel (perturbChannel h 0) 0) 0)).trans
    (perturbChannel_perturbChannel_perturbChannel_zero_zero_zero h)

/-- *Quintuple zero-perturbation collapses to identity.*  Composing five
    zero perturbations on `h` leaves the channel unchanged.  Extends the
    quadruple form `perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero`
    to a fifth layer. -/
theorem perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero_zero
    {n_s : Nat} (h : ChannelMatrix n_s) :
    perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel h 0) 0) 0) 0) 0 = h :=
  (perturbChannel_zero (perturbChannel (perturbChannel (perturbChannel (perturbChannel h 0) 0) 0) 0)).trans
    (perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero h)

/-- *Sextuple zero-perturbation collapses to identity.*  Composing six
    zero perturbations on `h` leaves the channel unchanged.  Extends the
    quintuple form `perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero_zero`
    to a sixth layer. -/
theorem perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero_zero_zero
    {n_s : Nat} (h : ChannelMatrix n_s) :
    perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel h 0) 0) 0) 0) 0) 0 = h :=
  (perturbChannel_zero (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel h 0) 0) 0) 0) 0)).trans
    (perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero_zero h)

/-- *Septuple zero-perturbation collapses to identity.*  Composing seven
    zero perturbations on `h` leaves the channel unchanged.  Extends the
    sextuple form `perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero_zero_zero`
    to a seventh layer. -/
theorem perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero_zero_zero_zero
    {n_s : Nat} (h : ChannelMatrix n_s) :
    perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel h 0) 0) 0) 0) 0) 0) 0 = h :=
  (perturbChannel_zero (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel h 0) 0) 0) 0) 0) 0)).trans
    (perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero_zero_zero h)

/-- *Octuple zero-perturbation collapses to identity.*  Composing eight
    zero perturbations on `h` leaves the channel unchanged.  Extends the
    septuple form `perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero_zero_zero_zero`
    to an eighth layer. -/
theorem perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero_zero_zero_zero_zero
    {n_s : Nat} (h : ChannelMatrix n_s) :
    perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel h 0) 0) 0) 0) 0) 0) 0) 0 = h :=
  (perturbChannel_zero (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel (perturbChannel h 0) 0) 0) 0) 0) 0) 0)).trans
    (perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_perturbChannel_zero_zero_zero_zero_zero_zero_zero h)

end Section06
end OrbgrandAi
