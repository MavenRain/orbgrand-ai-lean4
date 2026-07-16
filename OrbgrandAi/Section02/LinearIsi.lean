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

/-- *In-range delay yields the matrix entry.*  When `j.val <= k'.val`,
    the impulse-response tap reads off the channel matrix entry at
    row `k'` and column `k' - j`, packaged through `some`.  Direct
    `dif_pos` form of the `if`-guard inside `tap?`. -/
theorem LinearIsi.tap?_of_le
    {n_s : Nat} (ch : LinearIsi n_s) (k' j : Fin n_s)
    (h : j.val <= k'.val) :
    ch.tap? k' j
      = some (ch.channel k'
          ⟨k'.val - j.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k'.isLt⟩) :=
  dif_pos h

/-- *Out-of-range delay yields none.*  When `j.val > k'.val`, the
    impulse-response tap is `none`.  Direct `dif_neg` form of the
    `if`-guard inside `tap?`. -/
theorem LinearIsi.tap?_of_not_le
    {n_s : Nat} (ch : LinearIsi n_s) (k' j : Fin n_s)
    (h : ¬ j.val <= k'.val) :
    ch.tap? k' j = none :=
  dif_neg h

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

/-! ## Structural properties of the receiver -/

/-- *Identity-channel receive law.*  When the channel matrix is the
    identity, the receiver model degenerates to `Y = X + N`. -/
theorem LinearIsi.receive_one
    {n_s : Nat} (X N : SymbolVector n_s) (noiseCov : CovMatrix n_s) :
    LinearIsi.receive { channel := 1, noiseCov := noiseCov } X N
      = fun k => X k + N k :=
  funext fun k => congrArg (· + N k) (congrFun (Matrix.one_mulVec X) k)

/-- *The zero channel is causal.*  Every entry is zero, so the
    causality clause holds vacuously. -/
theorem LinearIsi.zero_causal
    {n_s : Nat} (noiseCov : CovMatrix n_s) :
    ({ channel := 0, noiseCov := noiseCov } : LinearIsi n_s).causal :=
  fun _ _ _ => rfl

/-- *The identity channel is causal.*  Off-diagonal entries of the
    identity matrix are zero, and a strict `Fin`-index inequality
    `i.val < j.val` forces `i ≠ j`. -/
theorem LinearIsi.one_causal
    {n_s : Nat} (noiseCov : CovMatrix n_s) :
    ({ channel := 1, noiseCov := noiseCov } : LinearIsi n_s).causal :=
  fun _ _ h_lt =>
    Matrix.one_apply_ne (fun heq => Nat.ne_of_lt h_lt (congrArg Fin.val heq))

/-- *The zero channel has any bandwidth.*  Every entry is zero, so
    the bandwidth-at-most-`b` clause holds vacuously. -/
theorem LinearIsi.zero_bandwidth
    {n_s : Nat} (noiseCov : CovMatrix n_s) (b : Nat) :
    ({ channel := 0, noiseCov := noiseCov } : LinearIsi n_s).bandwidth b :=
  fun _ _ _ => rfl

/-- *The identity channel has any bandwidth.*  Off-diagonal entries
    vanish; the bandwidth condition `j.val + b < i.val` forces
    `j.val < i.val` (via `Nat.le_add_right`), which implies `i ≠ j`. -/
theorem LinearIsi.one_bandwidth
    {n_s : Nat} (noiseCov : CovMatrix n_s) (b : Nat) :
    ({ channel := 1, noiseCov := noiseCov } : LinearIsi n_s).bandwidth b :=
  fun i j hij =>
    let j_lt_i : j.val < i.val :=
      Nat.lt_of_le_of_lt (Nat.le_add_right j.val b) hij
    Matrix.one_apply_ne (fun heq => j_lt_i.ne' (congrArg Fin.val heq))

/-- *Bandwidth monotonicity.*  If a channel has bandwidth at most
    `b`, it also has bandwidth at most any `b' >= b`.  Larger
    bandwidth bounds describe a weaker predicate, so this is the
    expected order. -/
theorem LinearIsi.bandwidth_le
    {n_s : Nat} {ch : LinearIsi n_s} {b b' : Nat} (hb : b <= b')
    (h : ch.bandwidth b) :
    ch.bandwidth b' :=
  fun i j hij =>
    h i j (Nat.lt_of_le_of_lt (Nat.add_le_add_left hb j.val) hij)

/-- *Bandwidth widens by one.*  A channel with bandwidth at most
    `b` also has bandwidth at most `b + 1`.  Direct corollary of
    `bandwidth_le` with the witness `Nat.le_succ b : b <= b + 1`. -/
theorem LinearIsi.bandwidth_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 1) :=
  LinearIsi.bandwidth_le (Nat.le_succ b) h

/-- *Bandwidth zero is the strongest bandwidth bound.*  A channel
    with bandwidth at most `0` (diagonal-only support) also has
    bandwidth at most any `b`.  Direct corollary of `bandwidth_le`
    with the witness `Nat.zero_le b`. -/
theorem LinearIsi.bandwidth_of_zero
    {n_s : Nat} {ch : LinearIsi n_s} (b : Nat)
    (h : ch.bandwidth 0) :
    ch.bandwidth b :=
  LinearIsi.bandwidth_le (Nat.zero_le b) h

/-- *Bandwidth widens by two.*  Two-step corollary of
    `bandwidth_succ`: lift from `b` to `b + 1` to `b + 2`. -/
theorem LinearIsi.bandwidth_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 2) :=
  LinearIsi.bandwidth_succ (LinearIsi.bandwidth_succ h)

/-- *Bandwidth widens by any additive offset.*  A channel with
    bandwidth at most `b` also has bandwidth at most `b + k` for any
    `k`.  Direct corollary of `bandwidth_le` with the witness
    `Nat.le_add_right b k`. -/
theorem LinearIsi.bandwidth_add
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (k : Nat)
    (h : ch.bandwidth b) :
    ch.bandwidth (b + k) :=
  LinearIsi.bandwidth_le (Nat.le_add_right b k) h

/-- *Bandwidth widens by any left-additive offset.*  Dual of
    `bandwidth_add`: a channel with bandwidth at most `b` also has
    bandwidth at most `k + b` for any `k`.  Direct corollary of
    `bandwidth_le` with the witness `Nat.le_add_left b k`. -/
theorem LinearIsi.bandwidth_add_left
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (k : Nat)
    (h : ch.bandwidth b) :
    ch.bandwidth (k + b) :=
  LinearIsi.bandwidth_le (Nat.le_add_left b k) h

/-- *Bandwidth widens by three.*  Three-step corollary chaining
    `bandwidth_succ_succ` and `bandwidth_succ`: lift from `b` to
    `b + 2` and then to `b + 3`. -/
theorem LinearIsi.bandwidth_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 3) :=
  LinearIsi.bandwidth_succ (LinearIsi.bandwidth_succ_succ h)

/-- *Bandwidth widens by four.*  Four-step corollary chaining
    `bandwidth_succ_succ_succ` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 4) :=
  LinearIsi.bandwidth_succ (LinearIsi.bandwidth_succ_succ_succ h)

/-- *Bandwidth widens by five.*  Five-step corollary chaining
    `bandwidth_succ_succ_succ_succ` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 5) :=
  LinearIsi.bandwidth_succ (LinearIsi.bandwidth_succ_succ_succ_succ h)

/-- *Bandwidth widens by six.*  Six-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 6) :=
  LinearIsi.bandwidth_succ (LinearIsi.bandwidth_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by seven.*  Seven-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 7) :=
  LinearIsi.bandwidth_succ (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by eight.*  Eight-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 8) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by nine.*  Nine-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ_succ` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 9) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by ten.*  Ten-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ` and
    `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 10) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by eleven.*  Eleven-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ` and
    `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 11) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by twelve.*  Twelve-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ`
    and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 12) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by thirteen.*  Thirteen-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ`
    and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 13) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by fourteen.*  Fourteen-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ`
    and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 14) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by fifteen.*  Fifteen-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ`
    and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 15) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by sixteen.*  Sixteen-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ`
    and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 16) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by seventeen.*  Seventeen-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ`
    and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 17) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by eighteen.*  Eighteen-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ`
    and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 18) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by nineteen.*  Nineteen-step corollary chaining
    `bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ`
    and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 19) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by twenty.*  Twenty-step corollary chaining
    `bandwidth_succ_(x19)` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 20) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by twenty-one.*  Twenty-one-step corollary chaining
    `bandwidth_succ_(x20)` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 21) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by twenty-two.*  Twenty-two-step corollary chaining
    `bandwidth_succ_(x21)` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 22) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by twenty-three.*  Twenty-three-step corollary chaining
    `bandwidth_succ_(x22)` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 23) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by twenty-four.*  Twenty-four-step corollary chaining
    `bandwidth_succ_(x23)` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 24) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by twenty-five.*  Twenty-five-step corollary chaining
    `bandwidth_succ_(x24)` and `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 25) :=
  LinearIsi.bandwidth_succ
    (LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h)

/-- *Bandwidth widens by an offset and one more.*  A channel with
    bandwidth at most `b` also has bandwidth at most `b + k + 1`.
    Composes `bandwidth_add` with `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_add_succ
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (k : Nat)
    (h : ch.bandwidth b) :
    ch.bandwidth (b + k + 1) :=
  LinearIsi.bandwidth_succ (LinearIsi.bandwidth_add k h)

/-- *Bandwidth widens by two chained additive offsets.*  A channel
    with bandwidth at most `b` also has bandwidth at most `b + k + m`
    for any `k` and `m`. -/
theorem LinearIsi.bandwidth_add_add
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (k m : Nat)
    (h : ch.bandwidth b) :
    ch.bandwidth (b + k + m) :=
  LinearIsi.bandwidth_add m (LinearIsi.bandwidth_add k h)

/-- *Bandwidth widens by one and then by an offset.*  Composes
    `bandwidth_succ` with `bandwidth_add`. -/
theorem LinearIsi.bandwidth_succ_add
    {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (k : Nat)
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 1 + k) :=
  LinearIsi.bandwidth_add k (LinearIsi.bandwidth_succ h)

/-- *Bandwidth-zero channels have any successor bandwidth.*  A
    channel with bandwidth at most `0` (diagonal-only support) also
    has bandwidth at most `b + 1` for any `b`.  Composes
    `bandwidth_of_zero` with `bandwidth_succ`. -/
theorem LinearIsi.bandwidth_of_zero_succ
    {n_s : Nat} {ch : LinearIsi n_s} (b : Nat)
    (h : ch.bandwidth 0) :
    ch.bandwidth (b + 1) :=
  LinearIsi.bandwidth_succ (LinearIsi.bandwidth_of_zero b h)

/-- *Zero-channel receive ignores the signal.*  With `channel := 0`,
    the channel-vector product `(0 : Matrix).mulVec X` vanishes, so
    `receive X N = N` regardless of `X`. -/
theorem LinearIsi.zero_channel_receive
    {n_s : Nat} (noiseCov : CovMatrix n_s)
    (X N : SymbolVector n_s) :
    ({ channel := 0, noiseCov := noiseCov } : LinearIsi n_s).receive X N = N :=
  funext fun k =>
    let h_zero : (0 : Matrix (Fin n_s) (Fin n_s) Complex).mulVec X k = 0 :=
      congrFun (Matrix.zero_mulVec X) k
    let step1 :
        (0 : Matrix (Fin n_s) (Fin n_s) Complex).mulVec X k + N k = 0 + N k :=
      congrArg (· + N k) h_zero
    step1.trans (zero_add (N k))

/-- *Noise-free receive law.*  When the noise vector is zero, the
    receiver model degenerates to the channel-vector product `h * X`. -/
theorem LinearIsi.receive_zero_noise
    {n_s : Nat} (ch : LinearIsi n_s) (X : SymbolVector n_s) :
    ch.receive X 0 = fun k => ch.channel.mulVec X k :=
  funext fun k => add_zero _

/-- *Signal-free receive law.*  When the signal vector is zero, the
    receiver model degenerates to the noise vector `N`.  Combines
    `Matrix.mulVec_zero` (zero in, zero out) with `zero_add` on the
    surviving noise term. -/
theorem LinearIsi.receive_zero_signal
    {n_s : Nat} (ch : LinearIsi n_s) (N : SymbolVector n_s) :
    ch.receive 0 N = N :=
  funext fun k =>
    let step1 : ch.channel.mulVec 0 k + N k = 0 + N k :=
      congrArg (· + N k) (congrFun ch.channel.mulVec_zero k)
    step1.trans (zero_add (N k))

/-- *Additivity of the receiver in the noise.*  Sending `N1 + N2`
    through the channel is the same as sending `N1` and adding `N2`
    afterwards.  Pointwise add and `add_assoc` finish the proof. -/
theorem LinearIsi.receive_noise_add
    {n_s : Nat} (ch : LinearIsi n_s)
    (X N1 N2 : SymbolVector n_s) :
    ch.receive X (N1 + N2) = ch.receive X N1 + N2 :=
  funext fun k => (add_assoc _ _ _).symm

/-- *Full linearity of the receiver.*  The receive function is
    additive in both arguments simultaneously:

      `receive (X1 + X2) (N1 + N2) = receive X1 N1 + receive X2 N2`.

    Proof: pointwise expansion uses `Matrix.mulVec_add` on the
    channel product and `add_add_add_comm` to re-pair the four terms
    into `(mulVec X1 + N1) + (mulVec X2 + N2)`. -/
theorem LinearIsi.receive_add
    {n_s : Nat} (ch : LinearIsi n_s)
    (X1 X2 N1 N2 : SymbolVector n_s) :
    ch.receive (X1 + X2) (N1 + N2) = ch.receive X1 N1 + ch.receive X2 N2 :=
  funext fun k =>
    let step1 : ch.channel.mulVec (X1 + X2) k
                = ch.channel.mulVec X1 k + ch.channel.mulVec X2 k :=
      congrFun (ch.channel.mulVec_add X1 X2) k
    let step2 : ch.channel.mulVec (X1 + X2) k + (N1 + N2) k
                = (ch.channel.mulVec X1 k + ch.channel.mulVec X2 k)
                  + (N1 k + N2 k) :=
      congrArg (· + (N1 + N2) k) step1
    step2.trans (add_add_add_comm _ _ _ _)

/-- *Causality depends only on the channel matrix.*  Two `LinearIsi`
    bundles with equal channel matrices have the same causality
    status, regardless of how their noise covariances differ.  Both
    directions follow by pointwise rewriting through `h`. -/
theorem LinearIsi.causal_iff_of_eq_channels
    {n_s : Nat} {ch1 ch2 : LinearIsi n_s}
    (h : ch1.channel = ch2.channel) :
    ch1.causal <-> ch2.causal :=
  ⟨fun h1 i j hij =>
    let s : ch1.channel i j = ch2.channel i j :=
      congrFun (congrFun h i) j
    s.symm.trans (h1 i j hij),
   fun h2 i j hij =>
    let s : ch1.channel i j = ch2.channel i j :=
      congrFun (congrFun h i) j
    s.trans (h2 i j hij)⟩

/-- *Bandwidth depends only on the channel matrix.*  Dual of
    `causal_iff_of_eq_channels`: two `LinearIsi` bundles with equal
    channel matrices have the same bandwidth status for any `b`. -/
theorem LinearIsi.bandwidth_iff_of_eq_channels
    {n_s : Nat} {ch1 ch2 : LinearIsi n_s}
    (h : ch1.channel = ch2.channel) (b : Nat) :
    ch1.bandwidth b <-> ch2.bandwidth b :=
  ⟨fun h1 i j hij =>
    let s : ch1.channel i j = ch2.channel i j :=
      congrFun (congrFun h i) j
    s.symm.trans (h1 i j hij),
   fun h2 i j hij =>
    let s : ch1.channel i j = ch2.channel i j :=
      congrFun (congrFun h i) j
    s.trans (h2 i j hij)⟩

/-- *Receiver depends only on the channel matrix.*  Two `LinearIsi`
    bundles with equal channel matrices produce equal receiver
    outputs for every `(X, N)`, regardless of how their noise
    covariances differ.  Captures the fact that `receive` does not
    read `noiseCov`. -/
theorem LinearIsi.receive_of_eq_channels
    {n_s : Nat} (ch1 ch2 : LinearIsi n_s)
    (h : ch1.channel = ch2.channel) (X N : SymbolVector n_s) :
    ch1.receive X N = ch2.receive X N :=
  funext fun k =>
    let mulVec_eq : ch1.channel.mulVec X k = ch2.channel.mulVec X k :=
      congrFun (congrArg (fun M => Matrix.mulVec M X) h) k
    congrArg (· + N k) mulVec_eq

/-- *Receiver is noise-injective at a fixed signal.*  Two noise
    realisations produce equal receiver output iff they are equal.
    Pointwise `add_left_cancel` lifts to a `funext` equality. -/
theorem LinearIsi.receive_eq_iff_noise_eq
    {n_s : Nat} (ch : LinearIsi n_s) (X N1 N2 : SymbolVector n_s) :
    ch.receive X N1 = ch.receive X N2 <-> N1 = N2 :=
  ⟨fun h => funext fun k =>
    let hk : ch.channel.mulVec X k + N1 k
           = ch.channel.mulVec X k + N2 k :=
      congrFun h k
    add_left_cancel hk,
   fun h => congrArg (ch.receive X) h⟩

/-- *Symmetric form of `receive_eq_iff_noise_eq`.*  The biconditional
    can be read in either direction; this variant lets callers
    rewrite `N1 = N2` into a `receive`-equality without an extra
    `Iff.symm`.  Direct `Iff.comm` permutation. -/
theorem LinearIsi.receive_eq_iff_noise_eq_symm
    {n_s : Nat} (ch : LinearIsi n_s) (X N1 N2 : SymbolVector n_s) :
    N1 = N2 <-> ch.receive X N1 = ch.receive X N2 :=
  Iff.comm.mp (LinearIsi.receive_eq_iff_noise_eq ch X N1 N2)

/-- *Receiver agreement at fixed noise iff channel images agree.*
    Two signals produce equal receiver output (with a common noise
    realisation) iff their channel-vector products are equal.
    Dual of `receive_eq_iff_noise_eq`, using pointwise
    `add_right_cancel`. -/
theorem LinearIsi.receive_eq_iff_mulVec_eq
    {n_s : Nat} (ch : LinearIsi n_s) (X1 X2 N : SymbolVector n_s) :
    ch.receive X1 N = ch.receive X2 N
      <-> ch.channel.mulVec X1 = ch.channel.mulVec X2 :=
  ⟨fun h => funext fun k =>
    let hk : ch.channel.mulVec X1 k + N k
           = ch.channel.mulVec X2 k + N k :=
      congrFun h k
    add_right_cancel hk,
   fun h => funext fun k =>
    congrArg (· + N k) (congrFun h k)⟩

/-- *Symmetric form of `receive_eq_iff_mulVec_eq`.*  Lets callers
    rewrite a `mulVec`-equality into a `receive`-equality without an
    extra `Iff.symm`.  Dual to `receive_eq_iff_noise_eq_symm`. -/
theorem LinearIsi.receive_eq_iff_mulVec_eq_symm
    {n_s : Nat} (ch : LinearIsi n_s) (X1 X2 N : SymbolVector n_s) :
    ch.channel.mulVec X1 = ch.channel.mulVec X2
      <-> ch.receive X1 N = ch.receive X2 N :=
  Iff.comm.mp (LinearIsi.receive_eq_iff_mulVec_eq ch X1 X2 N)

/-- *Receiver at both-zero inputs is zero.*  Direct instantiation of
    `receive_zero_signal` at `N = 0`: `ch.receive 0 0 = 0`. -/
theorem LinearIsi.receive_zero_signal_zero_noise
    {n_s : Nat} (ch : LinearIsi n_s) :
    ch.receive 0 0 = 0 :=
  LinearIsi.receive_zero_signal ch 0

/-- *Zero-output characterisation at zero signal.*  With `X = 0`, the
    receiver output equals `N` (by `receive_zero_signal`), so the
    output vanishes iff the noise vanishes.  Dual of
    `receive_zero_noise_eq_zero_iff`. -/
theorem LinearIsi.receive_zero_signal_eq_zero_iff
    {n_s : Nat} (ch : LinearIsi n_s) (N : SymbolVector n_s) :
    ch.receive 0 N = 0 <-> N = 0 :=
  let h_eq : ch.receive 0 N = N :=
    LinearIsi.receive_zero_signal ch N
  ⟨fun h => h_eq.symm.trans h, fun h => h_eq.trans h⟩

/-- *Zero-output characterisation at zero noise.*  With `N = 0`, the
    receiver output is exactly the channel-vector product `h * X`, so
    the output vanishes iff that product vanishes.  Lifts
    `receive_zero_noise` to an `Iff`. -/
theorem LinearIsi.receive_zero_noise_eq_zero_iff
    {n_s : Nat} (ch : LinearIsi n_s) (X : SymbolVector n_s) :
    ch.receive X 0 = 0 <-> ch.channel.mulVec X = 0 :=
  let h_eq : ch.receive X 0 = ch.channel.mulVec X :=
    LinearIsi.receive_zero_noise ch X
  ⟨fun h => h_eq.symm.trans h, fun h => h_eq.trans h⟩

/-- *Additivity of `receive` in the signal at zero noise.*  Specialises
    `receive_add` to `N1 = N2 = 0`, using `add_zero 0 : 0 + 0 = 0` to
    rewrite the noise argument.  Captures pure channel-superposition:
    `h * (X1 + X2) = h * X1 + h * X2`. -/
theorem LinearIsi.receive_signal_add_zero_noise
    {n_s : Nat} (ch : LinearIsi n_s) (X1 X2 : SymbolVector n_s) :
    ch.receive (X1 + X2) 0 = ch.receive X1 0 + ch.receive X2 0 :=
  let step : ch.receive (X1 + X2) (0 + 0)
            = ch.receive X1 0 + ch.receive X2 0 :=
    LinearIsi.receive_add ch X1 X2 0 0
  let h : ch.receive (X1 + X2) (0 + 0) = ch.receive (X1 + X2) 0 :=
    congrArg (ch.receive (X1 + X2)) (add_zero 0)
  h.symm.trans step

/-- *Identity-channel zero-signal receive is the noise.*  With
    `channel := 1` and `X = 0`, the receiver returns `N`.  Dual of
    `receive_one_zero_noise`: composes `receive_one` with `zero_add`. -/
theorem LinearIsi.receive_one_zero_signal
    {n_s : Nat} (N : SymbolVector n_s) (noiseCov : CovMatrix n_s) :
    ({ channel := 1, noiseCov := noiseCov } : LinearIsi n_s).receive 0 N
      = N :=
  funext fun k =>
    let h1 : ({ channel := (1 : Matrix (Fin n_s) (Fin n_s) Complex),
                noiseCov := noiseCov } : LinearIsi n_s).receive
                  (0 : SymbolVector n_s) N k
           = (0 : SymbolVector n_s) k + N k :=
      congrFun
        (LinearIsi.receive_one (0 : SymbolVector n_s) N noiseCov) k
    h1.trans (zero_add (N k))

/-- *Identity-channel zero-signal zero-noise receive is zero.*  With
    `channel := 1`, `X = 0`, and `N = 0`, the receiver returns `0`.
    Direct instantiation of `receive_one_zero_signal` at `N = 0`. -/
theorem LinearIsi.receive_one_zero_signal_zero_noise
    {n_s : Nat} (noiseCov : CovMatrix n_s) :
    ({ channel := 1, noiseCov := noiseCov } : LinearIsi n_s).receive 0 0
      = 0 :=
  LinearIsi.receive_one_zero_signal 0 noiseCov

/-- *Zero-channel zero-signal zero-noise receive is zero.*  With
    `channel := 0`, `X = 0`, and `N = 0`, the receiver returns `0`.
    Direct instantiation of `zero_channel_receive` at `N = 0`. -/
theorem LinearIsi.receive_zero_channel_zero_signal_zero_noise
    {n_s : Nat} (noiseCov : CovMatrix n_s) :
    ({ channel := 0, noiseCov := noiseCov } : LinearIsi n_s).receive 0 0
      = 0 :=
  LinearIsi.zero_channel_receive noiseCov 0 0

/-- *Generic zero-signal zero-noise receive is zero.*  For any
    channel, with `X = 0` and `N = 0`, the receiver returns `0`.
    Chains `receive_zero_noise ch 0` with `Matrix.mulVec_zero`. -/
theorem LinearIsi.receive_zero_noise_zero_signal
    {n_s : Nat} (ch : LinearIsi n_s) :
    ch.receive 0 0 = 0 :=
  let step : ch.receive 0 0 = fun k => ch.channel.mulVec 0 k :=
    LinearIsi.receive_zero_noise ch 0
  step.trans (funext fun k => congrFun ch.channel.mulVec_zero k)

/-- *Identity-channel zero-noise receive is the signal.*  With
    `channel := 1` and `N = 0`, the receiver is the identity on `X`.
    Composes `receive_one` (channel = identity reduces to `X + N`)
    with `add_zero` (zero noise drops out). -/
theorem LinearIsi.receive_one_zero_noise
    {n_s : Nat} (X : SymbolVector n_s) (noiseCov : CovMatrix n_s) :
    ({ channel := 1, noiseCov := noiseCov } : LinearIsi n_s).receive X 0
      = X :=
  funext fun k =>
    let h1 : ({ channel := (1 : Matrix (Fin n_s) (Fin n_s) Complex),
                noiseCov := noiseCov } : LinearIsi n_s).receive X
                  (0 : SymbolVector n_s) k
           = X k + (0 : SymbolVector n_s) k :=
      congrFun
        (LinearIsi.receive_one X (0 : SymbolVector n_s) noiseCov) k
    h1.trans (add_zero (X k))

/-- *Additivity of `receive` in the noise at zero signal.*  Dual of
    `receive_signal_add_zero_noise`: specialises `receive_add` to
    `X1 = X2 = 0`, using `add_zero 0 : 0 + 0 = 0` to rewrite the
    signal argument.  Captures pure noise-superposition through the
    channel. -/
theorem LinearIsi.receive_noise_add_zero_signal
    {n_s : Nat} (ch : LinearIsi n_s) (N1 N2 : SymbolVector n_s) :
    ch.receive 0 (N1 + N2) = ch.receive 0 N1 + ch.receive 0 N2 :=
  let step : ch.receive (0 + 0) (N1 + N2)
            = ch.receive 0 N1 + ch.receive 0 N2 :=
    LinearIsi.receive_add ch 0 0 N1 N2
  let h : ch.receive (0 + 0) (N1 + N2)
        = ch.receive 0 (N1 + N2) :=
    congrArg (fun X => ch.receive X (N1 + N2)) (add_zero 0)
  h.symm.trans step

/-- *Doubling of `receive` in the noise at zero signal.*  Instantiates
    `receive_noise_add_zero_signal` at `N1 = N2 = N`, giving
    `receive 0 (N + N) = receive 0 N + receive 0 N`.  The pure
    noise-superposition law specialised to a repeated noise term,
    mirroring how `receive_one_zero_signal_zero_noise` is a direct
    instantiation of `receive_one_zero_signal`. -/
theorem LinearIsi.receive_noise_add_self_zero_signal
    {n_s : Nat} (ch : LinearIsi n_s) (N : SymbolVector n_s) :
    ch.receive 0 (N + N) = ch.receive 0 N + ch.receive 0 N :=
  LinearIsi.receive_noise_add_zero_signal ch N N

/-- *Doubling of `receive` in the signal at zero noise.*  Instantiates
    `receive_signal_add_zero_noise` at `X1 = X2 = X`, giving
    `receive (X + X) 0 = receive X 0 + receive X 0`.  The pure
    channel-superposition law specialised to a repeated signal term,
    the signal-side dual of `receive_noise_add_self_zero_signal`. -/
theorem LinearIsi.receive_signal_add_self_zero_noise
    {n_s : Nat} (ch : LinearIsi n_s) (X : SymbolVector n_s) :
    ch.receive (X + X) 0 = ch.receive X 0 + ch.receive X 0 :=
  LinearIsi.receive_signal_add_zero_noise ch X X

/-- *Simultaneous doubling of `receive` in both arguments.*  Instantiates
    `receive_add` at `X1 = X2 = X` and `N1 = N2 = N`, giving
    `receive (X + X) (N + N) = receive X N + receive X N`.  The full
    receiver-linearity law specialised to a repeated signal-noise pair,
    the joint generalisation of `receive_signal_add_self_zero_noise` and
    `receive_noise_add_self_zero_signal`. -/
theorem LinearIsi.receive_add_self
    {n_s : Nat} (ch : LinearIsi n_s) (X N : SymbolVector n_s) :
    ch.receive (X + X) (N + N) = ch.receive X N + ch.receive X N :=
  LinearIsi.receive_add ch X X N N

/-- *Doubling of `receive` in the signal with a split noise.*  Instantiates
    `receive_add` at `X1 = X2 = X` while keeping the two noise summands
    distinct, giving
    `receive (X + X) (N1 + N2) = receive X N1 + receive X N2`.  A hybrid of
    `receive_add_self` and `receive_add`, doubling only the signal argument
    while the noise remains a general sum. -/
theorem LinearIsi.receive_signal_self_noise_add
    {n_s : Nat} (ch : LinearIsi n_s) (X N1 N2 : SymbolVector n_s) :
    ch.receive (X + X) (N1 + N2) = ch.receive X N1 + ch.receive X N2 :=
  LinearIsi.receive_add ch X X N1 N2

/-- *Doubling of `receive` in the noise with a split signal.*  Instantiates
    `receive_add` at `N1 = N2 = N` while keeping the two signal summands
    distinct, giving
    `receive (X1 + X2) (N + N) = receive X1 N + receive X2 N`.  The exact
    dual of `receive_signal_self_noise_add`, doubling only the noise argument
    while the signal remains a general sum. -/
theorem LinearIsi.receive_signal_add_noise_self
    {n_s : Nat} (ch : LinearIsi n_s) (X1 X2 N : SymbolVector n_s) :
    ch.receive (X1 + X2) (N + N) = ch.receive X1 N + ch.receive X2 N :=
  LinearIsi.receive_add ch X1 X2 N N

/-- *Swapped-signal doubling of `receive` in the noise.*  Instantiates
    `receive_add` at `N1 = N2 = N` with the two signal summands supplied in
    swapped order, giving
    `receive (X2 + X1) (N + N) = receive X2 N + receive X1 N`.  The
    summand-commuted companion of `receive_signal_add_noise_self`, doubling
    only the noise argument while the signal remains a general sum. -/
theorem LinearIsi.receive_signal_swap_noise_self
    {n_s : Nat} (ch : LinearIsi n_s) (X1 X2 N : SymbolVector n_s) :
    ch.receive (X2 + X1) (N + N) = ch.receive X2 N + ch.receive X1 N :=
  LinearIsi.receive_add ch X2 X1 N N

end Section02
end OrbgrandAi
