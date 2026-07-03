import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import KanTactics

/-!
# Section II.  Basic types

Newtype wrappers and a single project-wide error sum used across all
channel-model files of Section II.  Encoding domain-meaningful
quantities as their own types (rather than passing raw `Nat`/`Real`
around) keeps the channel-matrix interface honest: a `BlockSize`
cannot be silently confused with a `CodewordLength`, and a
`CorrelationCoefficient` cannot be silently confused with an
arbitrary real.

The newtypes mirror the symbol conventions of the paper:

* `SymbolIndex`   -- `k' in Z^+`, an index along the symbol time scale.
* `SequenceLength`-- `n_s in N`, the length of a transmitted block.
* `BlockSize`     -- `b in N_{>0}`, the neighbourhood size of
                      ORBGRAND-AI; must be strictly positive.
* `CodewordLength`-- `n in N_{>0}`, the bit-length of a codeword.
* `BitsPerSymbol` -- `m_s in N_{>0}` with `n_s = n / m_s`.
* `ConstellationSize` -- `|chi| = 2^{m_s}`.
* `NoisePower`    -- `sigma_N^2`, a non-negative real.
* `SignalPower`   -- `sigma_X^2`, a non-negative real.
* `CorrelationCoefficient` -- `rho in [0, 1]`.
* `Ar2Coefficient`-- `phi_1`, `phi_2` of the AR(2) approximation.
* `SamplingFreq`  -- `f_s in R_{>0}` (Hz).
* `CarrierFreq`   -- `f_c in R_{>0}` (Hz).

The error enum `ChannelError` enumerates every way a channel-model
constructor can fail.  Constructors that can fail return
`Except ChannelError T` rather than crashing.  This is the project
analogue of the Rust convention that every fallible constructor
returns `Result<T, Error>`.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section02

/-! ## Indexing newtypes -/

/-- Symbol time index `k' in N`. -/
structure SymbolIndex where
  /-- Underlying natural-number index. -/
  toNat : Nat
deriving DecidableEq, Repr

/-- Length of a transmitted block of symbols, `n_s in N`. -/
structure SequenceLength where
  /-- Underlying natural-number length. -/
  toNat : Nat
deriving DecidableEq, Repr

/-- ORBGRAND-AI block / neighbourhood size, `b in N_{>0}`.
    The smart constructor `BlockSize.mk?` enforces positivity. -/
structure BlockSize where
  /-- Underlying natural-number block size. -/
  toNat : Nat
  /-- A block size is strictly positive. -/
  pos : 0 < toNat

/-- Bit-length `n in N_{>0}` of a codeword. -/
structure CodewordLength where
  /-- Underlying natural-number codeword length. -/
  toNat : Nat
  /-- A codeword has at least one bit. -/
  pos : 0 < toNat

/-- Bits per modulation symbol, `m_s in N_{>0}`.  For BPSK this is
    `1`, for 16-QAM it is `4`, etc. -/
structure BitsPerSymbol where
  /-- Underlying natural-number bit-count. -/
  toNat : Nat
  /-- A modulation symbol carries at least one bit. -/
  pos : 0 < toNat

/-- Constellation size `|chi| = 2^{m_s}`.  Always a power of two. -/
structure ConstellationSize where
  /-- Underlying cardinality. -/
  toNat : Nat
  /-- The constellation has at least one point. -/
  pos : 0 < toNat

/-! ## Physical-quantity newtypes -/

/-- Noise variance `sigma_N^2 >= 0`. -/
structure NoisePower where
  /-- Underlying real value. -/
  val : Real
  /-- Variance is non-negative. -/
  nonneg : 0 <= val

/-- Signal variance `sigma_X^2 >= 0`. -/
structure SignalPower where
  /-- Underlying real value. -/
  val : Real
  /-- Variance is non-negative. -/
  nonneg : 0 <= val

/-- Gauss-Markov correlation coefficient `rho in [0, 1]`. -/
structure CorrelationCoefficient where
  /-- Underlying real value. -/
  val : Real
  /-- The correlation is non-negative. -/
  nonneg : 0 <= val
  /-- The correlation is at most one. -/
  le_one : val <= 1

/-- An AR(2) coefficient `phi_1` or `phi_2`.  The Yule-Walker
    stability constraints are stated separately in
    `Section03.GaussMarkov` rather than baked into this wrapper,
    so that the unconstrained least-squares fit in
    `Section06.Ar2Approximation` can still produce a value of this
    type even if the resulting AR(2) is not stationary. -/
structure Ar2Coefficient where
  /-- Underlying real value. -/
  val : Real

/-- Sampling frequency `f_s` (Hz), strictly positive. -/
structure SamplingFreq where
  /-- Underlying real value in Hz. -/
  val : Real
  /-- A sampling frequency is strictly positive. -/
  pos : 0 < val

/-- Carrier frequency `f_c` (Hz), strictly positive. -/
structure CarrierFreq where
  /-- Underlying real value in Hz. -/
  val : Real
  /-- A carrier frequency is strictly positive. -/
  pos : 0 < val

/-! ## Section-wide error sum -/

/-- All ways a Section II channel-model constructor can fail.

    Variants are deliberately concrete (carrying the offending value
    where it makes the diagnostic readable) rather than abstract,
    so that downstream code can match on them exhaustively. -/
inductive ChannelError where
  /-- Attempt to construct a `BlockSize`, `CodewordLength`, etc. from
      a zero value. -/
  | nonPositive (field : String)
  /-- Correlation coefficient outside `[0, 1]`. -/
  | correlationOutOfRange (got : Real)
  /-- Negative variance supplied where non-negativity is required. -/
  | negativeVariance (got : Real)
  /-- Channel matrix dimension does not match the sequence length. -/
  | dimensionMismatch (expected got : Nat)
  /-- Delay-tap path count was zero where at least one path is required. -/
  | noPaths
  /-- Sampling frequency was non-positive. -/
  | nonPositiveSamplingFreq (got : Real)

/-! ## Smart constructors -/

namespace BlockSize

/-- Build a `BlockSize` from a natural number.  Returns
    `Except ChannelError BlockSize` because the constructor refuses
    `0`. -/
def mk? (n : Nat) : Except ChannelError BlockSize :=
  if h : 0 < n then
    Except.ok { toNat := n, pos := h }
  else
    Except.error (ChannelError.nonPositive "BlockSize")

/-- *Positive input gives `ok`.*  Direct `dif_pos` characterization
    of `BlockSize.mk?` on a positive input. -/
theorem mk?_of_pos (n : Nat) (h : 0 < n) :
    BlockSize.mk? n = Except.ok ⟨n, h⟩ :=
  dif_pos h

/-- *Non-positive input gives `error`.*  Direct `dif_neg` form: when
    the positivity precondition fails, `BlockSize.mk?` emits a
    `nonPositive` channel error. -/
theorem mk?_of_not_pos (n : Nat) (h : ¬ 0 < n) :
    BlockSize.mk? n = Except.error (ChannelError.nonPositive "BlockSize") :=
  dif_neg h

/-- *Round-trip identity through the `.toNat` accessor.*  Parallel
    of `NoisePower.mk?_val_eq` for `BlockSize` (whose carrier field
    is `toNat`). -/
theorem mk?_toNat_eq (n : Nat) (h : 0 < n) :
    (BlockSize.mk? n).map (·.toNat) = Except.ok n :=
  (mk?_of_pos n h).symm ▸ rfl

/-- *One is a valid block size.*  Boundary corollary of
    `mk?_of_pos` at `n = 1`: the smallest strictly-positive
    neighbourhood (a single candidate flip) sits at the lower
    endpoint of `N_{>0}` and round-trips through `mk?`. -/
theorem mk?_one :
    BlockSize.mk? 1 = Except.ok ⟨1, Nat.one_pos⟩ :=
  mk?_of_pos 1 Nat.one_pos

/-- *Two is a valid block size.*  Next-concrete-value corollary of
    `mk?_of_pos` at `n = 2`: the smallest nontrivial neighbourhood
    (two candidate flips) round-trips through `mk?`, with positivity
    witnessed by `Nat.succ_pos 1` rather than `Nat.one_pos`. -/
theorem mk?_two :
    BlockSize.mk? 2 = Except.ok ⟨2, Nat.succ_pos 1⟩ :=
  mk?_of_pos 2 (Nat.succ_pos 1)

/-- *Three is a valid block size.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 3`: the smallest odd nontrivial
    neighbourhood round-trips through `mk?`, with positivity
    witnessed by `Nat.succ_pos 2`. -/
theorem mk?_three :
    BlockSize.mk? 3 = Except.ok ⟨3, Nat.succ_pos 2⟩ :=
  mk?_of_pos 3 (Nat.succ_pos 2)

/-- *Four is a valid block size.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 4`: the smallest even nontrivial
    neighbourhood beyond `2` round-trips through `mk?`, with
    positivity witnessed by `Nat.succ_pos 3`. -/
theorem mk?_four :
    BlockSize.mk? 4 = Except.ok ⟨4, Nat.succ_pos 3⟩ :=
  mk?_of_pos 4 (Nat.succ_pos 3)

/-- *Five is a valid block size.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 5`: the next odd nontrivial neighbourhood
    beyond `3` round-trips through `mk?`, with positivity witnessed
    by `Nat.succ_pos 4`. -/
theorem mk?_five :
    BlockSize.mk? 5 = Except.ok ⟨5, Nat.succ_pos 4⟩ :=
  mk?_of_pos 5 (Nat.succ_pos 4)

/-- *Six is a valid block size.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 6`: the next even nontrivial neighbourhood
    beyond `4` round-trips through `mk?`, with positivity witnessed
    by `Nat.succ_pos 5`. -/
theorem mk?_six :
    BlockSize.mk? 6 = Except.ok ⟨6, Nat.succ_pos 5⟩ :=
  mk?_of_pos 6 (Nat.succ_pos 5)

/-- *Seven is a valid block size.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 7`: the next odd nontrivial neighbourhood
    beyond `5` round-trips through `mk?`, with positivity witnessed
    by `Nat.succ_pos 6`. -/
theorem mk?_seven :
    BlockSize.mk? 7 = Except.ok ⟨7, Nat.succ_pos 6⟩ :=
  mk?_of_pos 7 (Nat.succ_pos 6)

/-- *Eight is a valid block size.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 8`: the next even nontrivial neighbourhood
    beyond `6` round-trips through `mk?`, with positivity witnessed
    by `Nat.succ_pos 7`. -/
theorem mk?_eight :
    BlockSize.mk? 8 = Except.ok ⟨8, Nat.succ_pos 7⟩ :=
  mk?_of_pos 8 (Nat.succ_pos 7)

/-- *Nine is a valid block size.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 9`: the next odd nontrivial neighbourhood
    beyond `7` round-trips through `mk?`, with positivity witnessed
    by `Nat.succ_pos 8`. -/
theorem mk?_nine :
    BlockSize.mk? 9 = Except.ok ⟨9, Nat.succ_pos 8⟩ :=
  mk?_of_pos 9 (Nat.succ_pos 8)

end BlockSize

namespace CodewordLength

/-- Build a `CodewordLength` from a natural number, refusing `0`. -/
def mk? (n : Nat) : Except ChannelError CodewordLength :=
  if h : 0 < n then
    Except.ok { toNat := n, pos := h }
  else
    Except.error (ChannelError.nonPositive "CodewordLength")

/-- *Positive input gives `ok`.*  Parallel of `BlockSize.mk?_of_pos`. -/
theorem mk?_of_pos (n : Nat) (h : 0 < n) :
    CodewordLength.mk? n = Except.ok ⟨n, h⟩ :=
  dif_pos h

/-- *Non-positive input gives `error`.*  Parallel of
    `BlockSize.mk?_of_not_pos`. -/
theorem mk?_of_not_pos (n : Nat) (h : ¬ 0 < n) :
    CodewordLength.mk? n
      = Except.error (ChannelError.nonPositive "CodewordLength") :=
  dif_neg h

/-- *Round-trip identity through the `.toNat` accessor.* -/
theorem mk?_toNat_eq (n : Nat) (h : 0 < n) :
    (CodewordLength.mk? n).map (·.toNat) = Except.ok n :=
  (mk?_of_pos n h).symm ▸ rfl

/-- *Two is a valid codeword length.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 2`: the smallest nontrivial codeword
    length (two coded bits) round-trips through `mk?`, with
    positivity witnessed by `Nat.succ_pos 1`.  Parallel of
    `BlockSize.mk?_two`. -/
theorem mk?_two :
    CodewordLength.mk? 2 = Except.ok ⟨2, Nat.succ_pos 1⟩ :=
  mk?_of_pos 2 (Nat.succ_pos 1)

/-- *Three is a valid codeword length.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 3`: the smallest odd nontrivial codeword
    length round-trips through `mk?`, with positivity witnessed by
    `Nat.succ_pos 2`.  Parallel of `BlockSize.mk?_three`. -/
theorem mk?_three :
    CodewordLength.mk? 3 = Except.ok ⟨3, Nat.succ_pos 2⟩ :=
  mk?_of_pos 3 (Nat.succ_pos 2)

/-- *Four is a valid codeword length.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 4`: the smallest even nontrivial codeword
    length beyond `2` round-trips through `mk?`, with positivity
    witnessed by `Nat.succ_pos 3`.  Parallel of `BlockSize.mk?_four`. -/
theorem mk?_four :
    CodewordLength.mk? 4 = Except.ok ⟨4, Nat.succ_pos 3⟩ :=
  mk?_of_pos 4 (Nat.succ_pos 3)

/-- *Five is a valid codeword length.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 5`: the next odd nontrivial codeword
    length beyond `3` round-trips through `mk?`, with positivity
    witnessed by `Nat.succ_pos 4`.  Parallel of `BlockSize.mk?_five`. -/
theorem mk?_five :
    CodewordLength.mk? 5 = Except.ok ⟨5, Nat.succ_pos 4⟩ :=
  mk?_of_pos 5 (Nat.succ_pos 4)

/-- *Six is a valid codeword length.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 6`: the next even nontrivial codeword
    length beyond `4` round-trips through `mk?`, with positivity
    witnessed by `Nat.succ_pos 5`.  Parallel of `BlockSize.mk?_six`. -/
theorem mk?_six :
    CodewordLength.mk? 6 = Except.ok ⟨6, Nat.succ_pos 5⟩ :=
  mk?_of_pos 6 (Nat.succ_pos 5)

/-- *Seven is a valid codeword length.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 7`: the next odd nontrivial codeword
    length beyond `5` round-trips through `mk?`, with positivity
    witnessed by `Nat.succ_pos 6`.  Parallel of `BlockSize.mk?_seven`. -/
theorem mk?_seven :
    CodewordLength.mk? 7 = Except.ok ⟨7, Nat.succ_pos 6⟩ :=
  mk?_of_pos 7 (Nat.succ_pos 6)

/-- *Eight is a valid codeword length.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 8`: the next even nontrivial codeword
    length beyond `6` round-trips through `mk?`, with positivity
    witnessed by `Nat.succ_pos 7`.  Parallel of `BlockSize.mk?_eight`. -/
theorem mk?_eight :
    CodewordLength.mk? 8 = Except.ok ⟨8, Nat.succ_pos 7⟩ :=
  mk?_of_pos 8 (Nat.succ_pos 7)

/-- *Nine is a valid codeword length.*  Next-concrete-value corollary
    of `mk?_of_pos` at `n = 9`: the next odd nontrivial codeword
    length beyond `7` round-trips through `mk?`, with positivity
    witnessed by `Nat.succ_pos 8`.  Parallel of `BlockSize.mk?_nine`. -/
theorem mk?_nine :
    CodewordLength.mk? 9 = Except.ok ⟨9, Nat.succ_pos 8⟩ :=
  mk?_of_pos 9 (Nat.succ_pos 8)

end CodewordLength

namespace BitsPerSymbol

/-- Build a `BitsPerSymbol` from a natural number, refusing `0`. -/
def mk? (n : Nat) : Except ChannelError BitsPerSymbol :=
  if h : 0 < n then
    Except.ok { toNat := n, pos := h }
  else
    Except.error (ChannelError.nonPositive "BitsPerSymbol")

/-- *Positive input gives `ok`.*  Parallel of `BlockSize.mk?_of_pos`. -/
theorem mk?_of_pos (n : Nat) (h : 0 < n) :
    BitsPerSymbol.mk? n = Except.ok ⟨n, h⟩ :=
  dif_pos h

/-- *Non-positive input gives `error`.*  Parallel of
    `BlockSize.mk?_of_not_pos`. -/
theorem mk?_of_not_pos (n : Nat) (h : ¬ 0 < n) :
    BitsPerSymbol.mk? n
      = Except.error (ChannelError.nonPositive "BitsPerSymbol") :=
  dif_neg h

/-- *Round-trip identity through the `.toNat` accessor.* -/
theorem mk?_toNat_eq (n : Nat) (h : 0 < n) :
    (BitsPerSymbol.mk? n).map (·.toNat) = Except.ok n :=
  (mk?_of_pos n h).symm ▸ rfl

end BitsPerSymbol

namespace NoisePower

/-- Build a `NoisePower` from a real, refusing negative values.

    Marked `noncomputable` because `Real`'s ordering instance is
    classical: the `if h : 0 <= v then ...` discriminant lives in
    `Prop` rather than `Bool`. -/
noncomputable def mk? (v : Real) : Except ChannelError NoisePower :=
  if h : 0 <= v then
    Except.ok { val := v, nonneg := h }
  else
    Except.error (ChannelError.negativeVariance v)

/-- *Non-negative input gives `ok`.*  Direct `dif_pos` characterization
    of `NoisePower.mk?` on a non-negative real. -/
theorem mk?_of_nonneg (v : Real) (h : 0 <= v) :
    NoisePower.mk? v = Except.ok ⟨v, h⟩ :=
  dif_pos h

/-- *Negative input gives `error`.*  Direct `dif_neg` form: when the
    non-negativity precondition fails, `NoisePower.mk?` emits a
    `negativeVariance` channel error carrying the offending value. -/
theorem mk?_of_neg (v : Real) (h : ¬ 0 <= v) :
    NoisePower.mk? v = Except.error (ChannelError.negativeVariance v) :=
  dif_neg h

/-- *Round-trip identity through the `.val` accessor.*  Building a
    `NoisePower` from a non-negative `v` and then extracting its
    `.val` field recovers `v`.  `Except.map (·.val)` lifts through
    the `Except.ok` constructor; the underlying `dif_pos` rewriting
    is delegated to `mk?_of_nonneg`. -/
theorem mk?_val_eq (v : Real) (h : 0 <= v) :
    (NoisePower.mk? v).map (·.val) = Except.ok v :=
  (mk?_of_nonneg v h).symm ▸ rfl

/-- *Zero is a valid noise power.*  Boundary corollary of
    `mk?_of_nonneg` at `v = 0`: a noiseless channel sits at the
    lower endpoint of the `[0, ∞)` range and round-trips through
    `mk?`. -/
theorem mk?_zero :
    NoisePower.mk? 0 = Except.ok ⟨0, le_refl 0⟩ :=
  mk?_of_nonneg 0 (le_refl 0)

end NoisePower

namespace SignalPower

/-- Build a `SignalPower` from a real, refusing negative values.
    `noncomputable` for the same reason as `NoisePower.mk?`. -/
noncomputable def mk? (v : Real) : Except ChannelError SignalPower :=
  if h : 0 <= v then
    Except.ok { val := v, nonneg := h }
  else
    Except.error (ChannelError.negativeVariance v)

/-- *Non-negative input gives `ok`.*  Parallel of
    `NoisePower.mk?_of_nonneg`. -/
theorem mk?_of_nonneg (v : Real) (h : 0 <= v) :
    SignalPower.mk? v = Except.ok ⟨v, h⟩ :=
  dif_pos h

/-- *Negative input gives `error`.*  Parallel of
    `NoisePower.mk?_of_neg`. -/
theorem mk?_of_neg (v : Real) (h : ¬ 0 <= v) :
    SignalPower.mk? v = Except.error (ChannelError.negativeVariance v) :=
  dif_neg h

/-- *Round-trip identity through the `.val` accessor.*  Parallel of
    `NoisePower.mk?_val_eq`. -/
theorem mk?_val_eq (v : Real) (h : 0 <= v) :
    (SignalPower.mk? v).map (·.val) = Except.ok v :=
  (mk?_of_nonneg v h).symm ▸ rfl

/-- *Zero is a valid signal power.*  Boundary corollary of
    `mk?_of_nonneg` at `v = 0`: a silent transmitter sits at the
    lower endpoint of the `[0, ∞)` range and round-trips through
    `mk?`.  Parallel of `NoisePower.mk?_zero`. -/
theorem mk?_zero :
    SignalPower.mk? 0 = Except.ok ⟨0, le_refl 0⟩ :=
  mk?_of_nonneg 0 (le_refl 0)

end SignalPower

namespace CorrelationCoefficient

/-- Build a `CorrelationCoefficient` from a real, enforcing
    `0 <= v <= 1`.  `noncomputable` for the same reason as
    `NoisePower.mk?`. -/
noncomputable def mk? (v : Real) : Except ChannelError CorrelationCoefficient :=
  if h0 : 0 <= v then
    if h1 : v <= 1 then
      Except.ok { val := v, nonneg := h0, le_one := h1 }
    else
      Except.error (ChannelError.correlationOutOfRange v)
  else
    Except.error (ChannelError.correlationOutOfRange v)

/-- *Both preconditions met: input in `[0, 1]` gives `ok`.*  Composes
    the outer `dif_pos h0` (non-negative) with the inner `dif_pos h1`
    (≤ 1). -/
theorem mk?_of_mem (v : Real) (h0 : 0 <= v) (h1 : v <= 1) :
    CorrelationCoefficient.mk? v
      = Except.ok ⟨v, h0, h1⟩ :=
  (dif_pos h0).trans (dif_pos h1)

/-- *Negative input gives `error`.*  Outer `dif_neg` short-circuits
    the entire chain. -/
theorem mk?_of_neg (v : Real) (h0 : ¬ 0 <= v) :
    CorrelationCoefficient.mk? v
      = Except.error (ChannelError.correlationOutOfRange v) :=
  dif_neg h0

/-- *Input above one gives `error`.*  Non-negative but `> 1`: outer
    `dif_pos h0` reduces to the inner `if`, which `dif_neg h1` then
    routes to the error branch. -/
theorem mk?_of_gt_one (v : Real) (h0 : 0 <= v) (h1 : ¬ v <= 1) :
    CorrelationCoefficient.mk? v
      = Except.error (ChannelError.correlationOutOfRange v) :=
  (dif_pos h0).trans (dif_neg h1)

/-- *Round-trip identity through the `.val` accessor.*  Both
    preconditions (non-negative and ≤ 1) must hold; with both met
    `mk?_of_mem` produces the `Except.ok` whose mapped `.val` is `v`. -/
theorem mk?_val_eq (v : Real) (h0 : 0 <= v) (h1 : v <= 1) :
    (CorrelationCoefficient.mk? v).map (·.val) = Except.ok v :=
  (mk?_of_mem v h0 h1).symm ▸ rfl

/-- *Zero is a valid correlation coefficient.*  Boundary corollary
    of `mk?_of_mem` at `v = 0`: an uncorrelated channel (`rho = 0`)
    sits at the lower endpoint of `[0, 1]` and round-trips through
    `mk?`. -/
theorem mk?_zero :
    CorrelationCoefficient.mk? 0
      = Except.ok ⟨0, le_refl 0, zero_le_one⟩ :=
  mk?_of_mem 0 (le_refl 0) zero_le_one

/-- *One is a valid correlation coefficient.*  Boundary corollary
    of `mk?_of_mem` at `v = 1`: a fully correlated channel (`rho =
    1`) sits at the upper endpoint of `[0, 1]` and round-trips
    through `mk?`. -/
theorem mk?_one :
    CorrelationCoefficient.mk? 1
      = Except.ok ⟨1, zero_le_one, le_refl 1⟩ :=
  mk?_of_mem 1 zero_le_one (le_refl 1)

end CorrelationCoefficient

namespace SamplingFreq

/-- Build a `SamplingFreq` from a real, refusing non-positive values.
    `noncomputable` for the same reason as `NoisePower.mk?`. -/
noncomputable def mk? (v : Real) : Except ChannelError SamplingFreq :=
  if h : 0 < v then
    Except.ok { val := v, pos := h }
  else
    Except.error (ChannelError.nonPositiveSamplingFreq v)

/-- *Strictly positive input gives `ok`.*  Direct `dif_pos`
    characterization. -/
theorem mk?_of_pos (v : Real) (h : 0 < v) :
    SamplingFreq.mk? v = Except.ok ⟨v, h⟩ :=
  dif_pos h

/-- *Non-positive input gives `error`.*  Direct `dif_neg` form: the
    `nonPositiveSamplingFreq` channel error carries the offending
    value. -/
theorem mk?_of_not_pos (v : Real) (h : ¬ 0 < v) :
    SamplingFreq.mk? v
      = Except.error (ChannelError.nonPositiveSamplingFreq v) :=
  dif_neg h

/-- *Round-trip identity through the `.val` accessor.*  Parallel of
    `NoisePower.mk?_val_eq` for `SamplingFreq` (which uses the
    strict-positivity precondition). -/
theorem mk?_val_eq (v : Real) (h : 0 < v) :
    (SamplingFreq.mk? v).map (·.val) = Except.ok v :=
  (mk?_of_pos v h).symm ▸ rfl

/-- *One hertz is a valid sampling frequency.*  Boundary corollary
    of `mk?_of_pos` at `v = 1`: a representative strictly-positive
    rate witnessing that `mk?` accepts the open `(0, ∞)` range.
    Strict positivity rules out a `mk?_zero` analogue. -/
theorem mk?_one :
    SamplingFreq.mk? 1 = Except.ok ⟨1, Real.zero_lt_one⟩ :=
  mk?_of_pos 1 Real.zero_lt_one

/-- *Two hertz is a valid sampling frequency.*  Next-concrete-value
    corollary of `mk?_of_pos` at `v = 2`: a second representative
    strictly-positive rate witnessing that `mk?` accepts the open
    `(0, ∞)` range, with positivity supplied by `zero_lt_two`.
    Parallel of `BlockSize.mk?_two` and `CodewordLength.mk?_two`
    lifted to the real-valued setting. -/
theorem mk?_two :
    SamplingFreq.mk? 2 = Except.ok ⟨2, zero_lt_two⟩ :=
  mk?_of_pos 2 zero_lt_two

/-- *Three hertz is a valid sampling frequency.*  Next-concrete-value
    corollary of `mk?_of_pos` at `v = 3`: a third representative
    strictly-positive rate witnessing that `mk?` accepts the open
    `(0, ∞)` range, with positivity supplied by `zero_lt_three`.
    Parallel of `BlockSize.mk?_three` and `CodewordLength.mk?_three`
    lifted to the real-valued setting. -/
theorem mk?_three :
    SamplingFreq.mk? 3 = Except.ok ⟨3, zero_lt_three⟩ :=
  mk?_of_pos 3 zero_lt_three

/-- *Four hertz is a valid sampling frequency.*  Next-concrete-value
    corollary of `mk?_of_pos` at `v = 4`, with positivity supplied by
    `zero_lt_four`.  Parallel of `BlockSize.mk?_four` and
    `CodewordLength.mk?_four` lifted to the real-valued setting. -/
theorem mk?_four :
    SamplingFreq.mk? 4 = Except.ok ⟨4, zero_lt_four⟩ :=
  mk?_of_pos 4 zero_lt_four

/-- *Five hertz is a valid sampling frequency.*  Next-concrete-value
    corollary of `mk?_of_pos` at `v = 5`, with positivity supplied by
    `Nat.ofNat_pos` (Mathlib does not ship a `zero_lt_five`).
    Parallel of `BlockSize.mk?_five` and `CodewordLength.mk?_five`
    lifted to the real-valued setting. -/
theorem mk?_five :
    SamplingFreq.mk? 5 = Except.ok ⟨5, Nat.ofNat_pos⟩ :=
  mk?_of_pos 5 Nat.ofNat_pos

/-- *Six hertz is a valid sampling frequency.*  Next-concrete-value
    corollary of `mk?_of_pos` at `v = 6`, with positivity supplied by
    `Nat.ofNat_pos`.  Parallel of `BlockSize.mk?_six` and
    `CodewordLength.mk?_six` lifted to the real-valued setting. -/
theorem mk?_six :
    SamplingFreq.mk? 6 = Except.ok ⟨6, Nat.ofNat_pos⟩ :=
  mk?_of_pos 6 Nat.ofNat_pos

/-- *Seven hertz is a valid sampling frequency.*  Next-concrete-value
    corollary of `mk?_of_pos` at `v = 7`, with positivity supplied by
    `Nat.ofNat_pos`.  Parallel of `BlockSize.mk?_seven` and
    `CodewordLength.mk?_seven` lifted to the real-valued setting. -/
theorem mk?_seven :
    SamplingFreq.mk? 7 = Except.ok ⟨7, Nat.ofNat_pos⟩ :=
  mk?_of_pos 7 Nat.ofNat_pos

/-- *Eight hertz is a valid sampling frequency.*  Next-concrete-value
    corollary of `mk?_of_pos` at `v = 8`, with positivity supplied by
    `Nat.ofNat_pos`.  Parallel of `BlockSize.mk?_eight` and
    `CodewordLength.mk?_eight` lifted to the real-valued setting. -/
theorem mk?_eight :
    SamplingFreq.mk? 8 = Except.ok ⟨8, Nat.ofNat_pos⟩ :=
  mk?_of_pos 8 Nat.ofNat_pos

/-- *Nine hertz is a valid sampling frequency.*  Next-concrete-value
    corollary of `mk?_of_pos` at `v = 9`, with positivity supplied by
    `Nat.ofNat_pos`.  Parallel of `BlockSize.mk?_nine` and
    `CodewordLength.mk?_nine` lifted to the real-valued setting. -/
theorem mk?_nine :
    SamplingFreq.mk? 9 = Except.ok ⟨9, Nat.ofNat_pos⟩ :=
  mk?_of_pos 9 Nat.ofNat_pos

end SamplingFreq

end Section02
end OrbgrandAi
