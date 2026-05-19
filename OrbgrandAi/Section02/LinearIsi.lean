import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import OrbgrandAi.Section02.Basic
import KanTactics

/-!
# Section II.  Linear ISI channel

Formalizes Section II.A of the paper.  The scalar receiver model
(eq. unnumbered above eq. (1)) is

  Y_{k'} = sum_{j >= 0} h_{k', j} * X_{k' - j} + N_{k'}

where `k' in N` is the symbol time index, `X_{k'}` is the complex
transmitted symbol, `N_{k'}` is complex additive white Gaussian
noise, and `h_{k', j}` is the channel impulse response at time `k'`
for delay `j`.

For a block of length `n_s` the model is matricised as

  Y^{n_s} = h^{n_s x n_s} * X^{n_s} + N^{n_s}                    (1)

with `h^{n_s x n_s}` lower triangular (the channel is causal:
`h_{k', j} = 0` for `j > k' - 1` in the block).

The auto-covariance of `N` is denoted `C_N^{n_s x n_s}`.  Before
equalisation the paper takes `C_N = sigma_N^2 * I` for white noise;
the colouring caused by zero-forcing equalisation is covered in
`Section02.Dicode`.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section02

open Matrix

/-! ## Vectors and matrices over the complex field -/

/-- A length-`n_s` vector of complex symbols. -/
abbrev SymbolVector (n_s : Nat) := Fin n_s -> Complex

/-- An `n_s x n_s` complex channel matrix. -/
abbrev ChannelMatrix (n_s : Nat) := Matrix (Fin n_s) (Fin n_s) Complex

/-- An `n_s x n_s` complex auto-covariance matrix. -/
abbrev CovMatrix (n_s : Nat) := Matrix (Fin n_s) (Fin n_s) Complex

/-! ## Linear ISI channel -/

/-- A linear ISI channel of block length `n_s`, carrying the channel
    matrix `h` and the noise auto-covariance `C_N`. -/
structure LinearIsi (n_s : Nat) where
  /-- The channel matrix `h^{n_s x n_s}`. -/
  channel : ChannelMatrix n_s
  /-- The noise auto-covariance `C_N^{n_s x n_s}`. -/
  noiseCov : CovMatrix n_s

/-- The receiver model `Y = h * X + N`, eq. (1) of the paper. -/
def LinearIsi.receive
    {n_s : Nat} (ch : LinearIsi n_s)
    (X : SymbolVector n_s) (N : SymbolVector n_s) : SymbolVector n_s :=
  fun k => ch.channel.mulVec X k + N k

/-! ## Scalar form: the convolution view -/

/-- Read out the impulse-response coefficient `h_{k', j}` from a
    channel matrix.  The paper's indexing convention is

      h_{k', j} = (matrix at row `k'`, column `k' - j`)

    where `j in {0, ..., k'}` accesses the channel taps with
    delay `j`.  Returning `Option Complex` means that out-of-range
    delays (`j > k'`) yield `none` rather than wrapping or
    crashing. -/
def LinearIsi.tap?
    {n_s : Nat} (ch : LinearIsi n_s) (k' j : Fin n_s) : Option Complex :=
  if h : j.val <= k'.val then
    let col := k'.val - j.val
    have hcol : col < n_s :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) k'.isLt
    some (ch.channel k' ⟨col, hcol⟩)
  else
    none

/-- A channel matrix is *causal* if all entries strictly above the
    diagonal vanish.  The paper assumes causality throughout
    Section II without naming it. -/
def LinearIsi.causal {n_s : Nat} (ch : LinearIsi n_s) : Prop :=
  forall (i j : Fin n_s), i.val < j.val -> ch.channel i j = 0

/-- A channel matrix has *delay-tap bandwidth at most `b`* if all
    entries below the `b`-th sub-diagonal vanish: `h[i, j] = 0`
    whenever `i - j > b`.  Combined with causality this makes the
    channel matrix `b`-band lower triangular, the structure used by
    the RFView channel (`b = 6`) and the dicode channel (`b = 1`). -/
def LinearIsi.bandwidth
    {n_s : Nat} (ch : LinearIsi n_s) (b : Nat) : Prop :=
  forall (i j : Fin n_s), j.val + b < i.val -> ch.channel i j = 0

end Section02
end OrbgrandAi
