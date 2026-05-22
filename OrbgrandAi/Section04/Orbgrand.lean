import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section04.Grand
import KanTactics

/-!
# Section IV.B.  ORBGRAND

Formalizes the Ordered Reliability Bits GRAND scheme from
Section IV.B of the paper.

## Setup

ORBGRAND takes as input

* a soft demapper output, encoded as a per-bit *reliability* sequence
  `r : Fin n -> Real` (typically `r i = | log( p(b_i = 0) / p(b_i = 1) ) |`),
* a *rank* permutation `pi : Fin n -> Fin n` that sorts the bits in
  increasing order of reliability (so `pi 0` is the least reliable
  bit, `pi (n - 1)` the most),
* a linear approximation of the reliability curve as a function of
  rank.

The soft demapper's output is used to *order* the noise guesses, not
to filter them.  Each candidate noise pattern `e : Fin n -> Bool`
has a *logistic weight*

  w(e) = sum over i with e i = true of (rank of bit i) + 1

(with `+1` to start counting from `1` as per the paper's
landslide convention).  ORBGRAND enumerates patterns in increasing
`w(e)` and feeds them to GRAND's syndrome check.

## Landslide algorithm

The landslide algorithm enumerates all binary vectors of a given
logistic weight `w` in lexicographic order on the rank-sorted basis.
It runs in `O(n)` memory and `O(1)` amortised time per pattern.

## Linear reliability approximation

The soft information is collapsed into a single slope `beta in R`
and intercept `alpha in R`: a pattern of weight `w` is assigned the
log-likelihood penalty `alpha + beta * w`.  At low SNR the paper
shows this linear approximation matches the empirical reliability
curve well.

This file:

* Defines the reliability sequence and its sort permutation.
* Defines the logistic weight `logisticWeight pi e`.
* States the landslide enumeration as an abstract iterator
  `landslide n w : List (Fin n -> Bool)`.
* States the ordering-soundness theorem (logistic weight matches
  the sorted-bit ordering) as a placeholder.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section04

open OrbgrandAi.Section02

/-! ## Reliability sequence -/

/-- A bit-reliability sequence: `reliability i` is the soft-demapper
    log-likelihood-ratio magnitude for bit `i`.  Larger is more
    reliable. -/
abbrev BitReliability (n : Nat) := Fin n -> Real

/-! ## Rank permutation -/

/-- A permutation of `Fin n` sorting bits by increasing reliability.
    Encoded as a permutation function paired with the proof of
    monotonicity.  In practice this is computed by a sort over the
    `reliability` sequence. -/
structure ReliabilityRank (n : Nat) where
  /-- The permutation: `perm i` is the bit at rank `i`. -/
  perm : Fin n -> Fin n
  /-- The permutation is a bijection. -/
  bijective : Function.Bijective perm
  /-- The permutation sorts in increasing reliability. -/
  monotone :
    forall (rel : BitReliability n) (i j : Fin n),
      i.val <= j.val -> rel (perm i) <= rel (perm j)

/-! ## Logistic weight -/

/-- The logistic weight of a noise pattern `e` under rank `pi`:
    sum of `(rank + 1)` over bits where `e` is `true`. -/
def logisticWeight
    {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) : Nat :=
  Finset.univ.sum fun i =>
    let bit_at_rank_i := pi.perm i
    if e bit_at_rank_i then i.val + 1 else 0

/-! ## Landslide enumeration (abstract) -/

/-- Extend a length-`n` pattern by setting the bit at position `n`
    (the new highest position in `Fin (n + 1)`) to the value `b`.
    Built directly from `Fin.lastCases`. -/
def landslideExtend
    {n : Nat} (b : Bool) (e : Fin n -> Bool) : Fin (n + 1) -> Bool :=
  Fin.lastCases b e

/-- *Concrete landslide enumeration.*  `landslide n w` is the list of
    all `Fin n -> Bool` patterns whose identity-rank logistic weight
    is exactly `w`.  In the actual ORBGRAND pipeline the caller
    composes with a `ReliabilityRank` to get the rank-ordered
    enumeration.

    Structural recursion on `n`:
    * `landslide 0 0` returns the empty pattern (which has weight 0).
    * `landslide 0 (w + 1)` is empty (no positive weight on length 0).
    * `landslide (n + 1) w` extends the length-`n` enumerations:
        - With bit at position `n` set to `false`: keeps weight `w`.
        - With bit at position `n` set to `true`: shifts weight by
          `n + 1` (so we need patterns of weight `w - (n + 1)`),
          conditional on `n + 1 <= w`.

    The two extensions are concatenated `withTop ++ withoutTop`, so
    "more bits set" patterns are visited first within each bucket. -/
def landslide : (n w : Nat) -> List (Fin n -> Bool)
  | 0,     0     => [Fin.elim0]
  | 0,     _ + 1 => []
  | n + 1, w     =>
      let withoutTop : List (Fin (n + 1) -> Bool) :=
        (landslide n w).map (landslideExtend false)
      if n + 1 <= w then
        let withTop : List (Fin (n + 1) -> Bool) :=
          (landslide n (w - (n + 1))).map (landslideExtend true)
        withTop ++ withoutTop
      else
        withoutTop

/-- `landslide 0 0` contains exactly the empty pattern. -/
theorem landslide_zero_zero :
    landslide 0 0 = [Fin.elim0] := rfl

/-- `landslide 0 (w + 1)` is empty: there are no length-0 patterns
    of positive weight. -/
theorem landslide_zero_succ (w : Nat) :
    landslide 0 (w + 1) = [] := rfl

/-- The empty pattern has logistic weight `0` under any reliability
    rank (vacuous sum). -/
theorem logisticWeight_elim0 {pi : ReliabilityRank 0} :
    logisticWeight pi Fin.elim0 = 0 :=
  Finset.sum_empty

/-- `landslideExtend b e` evaluated at the new top position
    `Fin.last n` returns the inserted bit `b`. -/
theorem landslideExtend_last {n : Nat} (b : Bool) (e : Fin n -> Bool) :
    landslideExtend b e (Fin.last n) = b :=
  Fin.lastCases_last

/-- `landslideExtend b e` evaluated at a `castSucc`-image position
    returns the original pattern's value. -/
theorem landslideExtend_castSucc
    {n : Nat} (b : Bool) (e : Fin n -> Bool) (i : Fin n) :
    landslideExtend b e i.castSucc = e i :=
  Fin.lastCases_castSucc i

/-- `landslide 1 0` contains the single all-false pattern. -/
theorem landslide_one_zero :
    landslide 1 0 = [landslideExtend false Fin.elim0] := rfl

/-- `landslide 1 1` contains the single pattern with bit 0 set. -/
theorem landslide_one_one :
    landslide 1 1 = [landslideExtend true Fin.elim0] := rfl

/-- `landslide n w` has length 0 (is empty) when `w` is high enough
    that no pattern of length `n` can achieve it.  Specifically when
    `n = 0` and `w > 0`. -/
theorem landslide_zero_succ_length (w : Nat) :
    (landslide 0 (w + 1)).length = 0 := rfl

/-- `landslide 0 0` has length 1 -- the unique empty pattern. -/
theorem landslide_zero_zero_length :
    (landslide 0 0).length = 1 := rfl

/-- The total ORBGRAND enumeration: concatenation of landslide
    enumerations for weights `0, 1, 2, ...`. -/
def orbgrandEnumeration (n : Nat) : Nat -> List (Fin n -> Bool) :=
  fun w => landslide n w

/-! ## Bucket membership predicate -/

/-- *Predicate-based landslide bucket.*  Pattern `e` lives in bucket
    `w` (under reliability rank `pi`) iff its logistic weight is `w`.

    The opaque list-based `landslide n w` is one (yet-to-be-implemented)
    enumeration whose elements should satisfy `landslideBucket pi w` for
    the rank `pi` of the moment.  The predicate form decouples the
    ordering soundness proof from any particular enumeration. -/
def landslideBucket
    {n : Nat} (pi : ReliabilityRank n) (w : Nat)
    (e : Fin n -> Bool) : Prop :=
  logisticWeight pi e = w

/-- Every pattern is in its own logistic-weight bucket. -/
theorem landslideBucket_self
    {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    landslideBucket pi (logisticWeight pi e) e :=
  rfl

/-! ## Ordering soundness -/

/-- *Logistic-weight ordering is consistent with the bucket ordering.*

    If patterns `e1, e2` satisfy `logisticWeight pi e1 < logisticWeight pi e2`,
    then `e1` lives in a strictly earlier bucket than `e2`.  Formally:
    there exist bucket indices `i < j` such that
    `landslideBucket pi i e1` and `landslideBucket pi j e2`.

    Proof: take `i = logisticWeight pi e1`, `j = logisticWeight pi e2`;
    the hypothesis gives `i < j` directly and bucket membership is
    `rfl` for both witnesses. -/
theorem orbgrand_ordering_sound
    {n : Nat} (pi : ReliabilityRank n) (e1 e2 : Fin n -> Bool)
    (h : logisticWeight pi e1 < logisticWeight pi e2) :
    exists (i j : Nat),
      i < j /\
      landslideBucket pi i e1 /\
      landslideBucket pi j e2 :=
  ⟨logisticWeight pi e1, logisticWeight pi e2, h, rfl, rfl⟩

end Section04
end OrbgrandAi
