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

end BlockSize

namespace CodewordLength

/-- Build a `CodewordLength` from a natural number, refusing `0`. -/
def mk? (n : Nat) : Except ChannelError CodewordLength :=
  if h : 0 < n then
    Except.ok { toNat := n, pos := h }
  else
    Except.error (ChannelError.nonPositive "CodewordLength")

end CodewordLength

namespace BitsPerSymbol

/-- Build a `BitsPerSymbol` from a natural number, refusing `0`. -/
def mk? (n : Nat) : Except ChannelError BitsPerSymbol :=
  if h : 0 < n then
    Except.ok { toNat := n, pos := h }
  else
    Except.error (ChannelError.nonPositive "BitsPerSymbol")

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

end SamplingFreq

end Section02
end OrbgrandAi
