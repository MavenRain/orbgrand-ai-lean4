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

/-- The landslide enumeration `landslide n w` returns the list of
    all `Fin n -> Bool` patterns whose logistic weight (in the
    identity ordering) is exactly `w`.  In the actual ORBGRAND
    pipeline the caller composes with a `ReliabilityRank` to get
    the rank-ordered enumeration.

    The list is returned in lexicographic order on the sorted basis,
    which matches the landslide-algorithm spec from the paper
    (refs [14], [39]).

    *Placeholder shape.*  The full landslide construction is
    deferred; for now we expose the signature. -/
opaque landslide (n w : Nat) : List (Fin n -> Bool)

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
