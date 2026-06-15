import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
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

/-- *All-false pattern has zero logistic weight.*  Each summand has
    the form `if (fun _ => false) (pi.perm i) then i.val + 1 else 0`,
    which reduces to `0` by `rfl` on the inner `if false`.  Finishing
    via `Finset.sum_eq_zero`. -/
theorem logisticWeight_const_false {n : Nat} (pi : ReliabilityRank n) :
    logisticWeight pi (fun _ : Fin n => false) = 0 :=
  Finset.sum_eq_zero fun _ _ => rfl

/-- *All-true pattern has rank-sum logistic weight.*  Every summand is
    `if true then i.val + 1 else 0 = i.val + 1`, so the total
    collapses to `Σ i, i.val + 1` over `Finset.univ`.  The reliability
    rank does not affect the sum since the permutation `pi.perm` is a
    bijection over the same universe. -/
theorem logisticWeight_const_true {n : Nat} (pi : ReliabilityRank n) :
    logisticWeight pi (fun _ : Fin n => true)
      = Finset.univ.sum (fun i : Fin n => i.val + 1) :=
  Finset.sum_congr rfl fun _ _ => rfl

/-- *Upper bound on `logisticWeight`.*  The all-true pattern maximises
    the logistic weight: each summand is bounded by `i.val + 1`
    (since the alternative is `0`); `Finset.sum_le_sum` lifts the
    pointwise bound to the universal sum.  Mirrors `bitWeight_le_sum`
    but with the rank permutation applied. -/
theorem logisticWeight_le_const_true
    {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    logisticWeight pi e
      <= logisticWeight pi (fun _ : Fin n => true) :=
  Finset.sum_le_sum fun i _ =>
    Bool.casesOn (motive :=
        fun b => (if b then i.val + 1 else 0) <= i.val + 1)
      (e (pi.perm i))
      (Nat.zero_le _)
      (Nat.le_refl _)

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

/-- `landslide 2 0` contains a single pattern: both bits unset
    (extending all-false twice).  Direct rfl from the structural
    recursion: `withoutTop = (landslide 1 0).map (extend false)` and
    the `withTop` branch is skipped since `n + 1 > w`. -/
theorem landslide_two_zero :
    landslide 2 0
      = [landslideExtend false (landslideExtend false Fin.elim0)] := rfl

/-- `landslide 1 1` has length 1.  Direct `rfl` from `landslide_one_one`. -/
theorem landslide_one_one_length :
    (landslide 1 1).length = 1 := rfl

/-- `landslide 2 1` contains a single pattern: bit 0 set, bit 1 unset
    (extended with `false` from the length-1 weight-1 enumeration). -/
theorem landslide_two_one :
    landslide 2 1
      = [landslideExtend false (landslideExtend true Fin.elim0)] := rfl

/-- `landslide 2 2` contains a single pattern: bit 0 unset, bit 1 set
    (extended with `true` from the length-1 weight-0 enumeration). -/
theorem landslide_two_two :
    landslide 2 2
      = [landslideExtend true (landslideExtend false Fin.elim0)] := rfl

/-- `landslide n w` has length 0 (is empty) when `w` is high enough
    that no pattern of length `n` can achieve it.  Specifically when
    `n = 0` and `w > 0`. -/
theorem landslide_zero_succ_length (w : Nat) :
    (landslide 0 (w + 1)).length = 0 := rfl

/-- `landslide 0 0` has length 1 -- the unique empty pattern. -/
theorem landslide_zero_zero_length :
    (landslide 0 0).length = 1 := rfl

/-! ## Identity-rank logistic weight (`bitWeight`) -/

/-- The identity-rank logistic weight: sum of `(i + 1)` over positions
    `i` where `e i = true`.  This is what `landslide` enumerates by:
    `landslide n w` is the (yet-to-be-proven) list of all length-`n`
    patterns with `bitWeight = w`. -/
def bitWeight {n : Nat} (e : Fin n -> Bool) : Nat :=
  Finset.univ.sum fun i =>
    if e i then i.val + 1 else 0

/-- The empty pattern has bit-weight zero (vacuous sum). -/
theorem bitWeight_elim0 :
    bitWeight (Fin.elim0 : Fin 0 -> Bool) = 0 :=
  Finset.sum_empty

/-- *All-true at length 1 has bit-weight 1.*  Concrete base case at
    `n = 1`: the single summand reduces to `(0 : Fin 1).val + 1 = 1`
    via `Fin.sum_univ_one`. -/
theorem bitWeight_one_true :
    bitWeight (fun _ : Fin 1 => true) = 1 :=
  Fin.sum_univ_one _

/-- *All-true at length 2 has bit-weight 3.*  Concrete value at
    `n = 2`: summands at `i = 0, 1` reduce to `0 + 1 = 1` and
    `1 + 1 = 2`, totalling `3`, via `Fin.sum_univ_two`. -/
theorem bitWeight_two_true :
    bitWeight (fun _ : Fin 2 => true) = 3 :=
  Fin.sum_univ_two _

/-- *All-true at length 3 has bit-weight 6.*  Concrete value at
    `n = 3`: the triangular sum `1 + 2 + 3`, via
    `Fin.sum_univ_three`. -/
theorem bitWeight_three_true :
    bitWeight (fun _ : Fin 3 => true) = 6 :=
  Fin.sum_univ_three _


/-- *Logistic weight = bit-weight of the rank-permuted pattern.*  The
    two sums are definitionally equal: `logisticWeight pi e`'s
    `let bit_at_rank_i := pi.perm i; if e bit_at_rank_i then ...` and
    `bitWeight (e ∘ pi.perm)`'s `if e (pi.perm i) then ...` reduce
    to the same `Finset.univ.sum` body.  This connection allows
    transferring bit-weight theorems across the rank permutation. -/
theorem logisticWeight_eq_bitWeight_comp
    {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    logisticWeight pi e = bitWeight (e ∘ pi.perm) := rfl


/-- Extending by `false` preserves the bit-weight: the new top bit
    contributes 0, and the original positions are reproduced under
    `castSucc`.  Composes `Fin.sum_univ_castSucc` with
    `landslideExtend_last`/`landslideExtend_castSucc`. -/
theorem bitWeight_extend_false {n : Nat} (e : Fin n -> Bool) :
    bitWeight (landslideExtend false e) = bitWeight e :=
  let f : Fin (n + 1) -> Nat :=
    fun i => if (landslideExtend false e) i then i.val + 1 else 0
  let step1 : (Finset.univ : Finset (Fin (n + 1))).sum f
            = (Finset.univ : Finset (Fin n)).sum (fun i => f i.castSucc)
              + f (Fin.last n) :=
    Fin.sum_univ_castSucc f
  let step_last : f (Fin.last n) = 0 :=
    congrArg (fun b => if b then (Fin.last n).val + 1 else (0 : Nat))
      (landslideExtend_last false e)
  let step_castSucc :
      (Finset.univ : Finset (Fin n)).sum (fun i => f i.castSucc)
    = bitWeight e :=
    Finset.sum_congr rfl fun i _ =>
      congrArg (fun b => if b then i.castSucc.val + 1 else (0 : Nat))
        (landslideExtend_castSucc false e i)
  step1.trans
    ((congrArg₂ (· + ·) step_castSucc step_last).trans (add_zero _))

/-- Any pattern of length 0 has bit-weight zero (vacuous sum). -/
theorem bitWeight_fin_zero (e : Fin 0 -> Bool) : bitWeight e = 0 :=
  let h_uniq : e = Fin.elim0 :=
    funext fun (i : Fin 0) => (i.elim0 : e i = Fin.elim0 i)
  h_uniq.symm ▸ bitWeight_elim0

/-- *`landslide` correctness, base case (n = 0).*  Membership in
    `landslide 0 w` is equivalent to the pattern having bit-weight
    `w`.  Splits on `w`:
    * `w = 0`: any `e : Fin 0 → Bool` is `Fin.elim0` (uniquely
      determined), so membership in `[Fin.elim0]` follows.
    * `w > 0`: both sides are false (empty list, and `bitWeight = 0`
      can't equal a positive number). -/
theorem landslide_zero_iff (e : Fin 0 -> Bool) (w : Nat) :
    e ∈ landslide 0 w <-> bitWeight e = w :=
  let h_bw : bitWeight e = 0 := bitWeight_fin_zero e
  let h_uniq : e = Fin.elim0 :=
    funext fun (i : Fin 0) => (i.elim0 : e i = Fin.elim0 i)
  match w with
  | 0     =>
      ⟨fun _ => h_bw,
       fun _ => List.mem_singleton.mpr h_uniq⟩
  | w + 1 =>
      ⟨fun h_mem => (List.not_mem_nil h_mem).elim,
       fun h_eq =>
        (Nat.succ_ne_zero w (h_bw.symm.trans h_eq).symm).elim⟩

/-- *Pattern decomposition.*  Any length-`(n + 1)` pattern equals its
    own `landslideExtend` of (top bit, castSucc-restriction).  Proof
    by `funext` + `Fin.lastCases`: at `Fin.last n` it's by
    `landslideExtend_last`; at `castSucc j` it's by
    `landslideExtend_castSucc`. -/
theorem landslideExtend_split {n : Nat} (e : Fin (n + 1) -> Bool) :
    landslideExtend (e (Fin.last n)) (e ∘ Fin.castSucc) = e :=
  funext fun i =>
    Fin.lastCases
      (motive := fun j =>
        landslideExtend (e (Fin.last n)) (e ∘ Fin.castSucc) j = e j)
      (landslideExtend_last (e (Fin.last n)) (e ∘ Fin.castSucc))
      (fun j =>
        landslideExtend_castSucc (e (Fin.last n)) (e ∘ Fin.castSucc) j)
      i

/-- *`landslideExtend` is injective for any fixed top bit.*  Two
    length-`n` patterns extending to the same length-`(n + 1)` pattern
    must have been equal.  Proof: `funext` + `landslideExtend_castSucc`
    on each position. -/
theorem landslideExtend_inj {n : Nat} (b : Bool) :
    Function.Injective (landslideExtend (n := n) b) :=
  fun e1 e2 h =>
    funext fun i =>
      let h_at : landslideExtend b e1 i.castSucc = landslideExtend b e2 i.castSucc :=
        congrFun h i.castSucc
      (landslideExtend_castSucc b e1 i).symm.trans
        (h_at.trans (landslideExtend_castSucc b e2 i))

/-- *`landslideExtend` is injective in the top-bit argument.*  Two
    extensions of the same restriction with different top bits must
    have agreed on the top bit.  Evaluation at `Fin.last n` reads off
    the top bit (via `landslideExtend_last`). -/
theorem landslideExtend_inj_top {n : Nat} (e : Fin n -> Bool) {b1 b2 : Bool}
    (h : landslideExtend b1 e = landslideExtend b2 e) :
    b1 = b2 :=
  (landslideExtend_last b1 e).symm.trans
    ((congrFun h (Fin.last n)).trans (landslideExtend_last b2 e))

/-- *Full bidirectional injectivity of `landslideExtend`.*  Two
    extensions are equal iff both the top bit and the restriction
    agree.  Forward direction reads off the top bit at `Fin.last n`
    and the restriction at `castSucc` positions; backward direction
    is `congrArg₂`. -/
theorem landslideExtend_eq_iff {n : Nat} {b1 b2 : Bool}
    {e1 e2 : Fin n -> Bool} :
    landslideExtend b1 e1 = landslideExtend b2 e2
      <-> b1 = b2 /\ e1 = e2 :=
  ⟨fun h =>
    let h_top : b1 = b2 :=
      (landslideExtend_last b1 e1).symm.trans
        ((congrFun h (Fin.last n)).trans (landslideExtend_last b2 e2))
    let h_rest : e1 = e2 :=
      funext fun i =>
        (landslideExtend_castSucc b1 e1 i).symm.trans
          ((congrFun h i.castSucc).trans (landslideExtend_castSucc b2 e2 i))
    ⟨h_top, h_rest⟩,
   fun ⟨h_top, h_rest⟩ => congrArg₂ landslideExtend h_top h_rest⟩

/-- *`landslideExtend` as a bijection.*  Viewed as a function
    `Bool × (Fin n → Bool) → (Fin (n + 1) → Bool)`, `landslideExtend`
    is bijective.  Injectivity follows from `landslideExtend_eq_iff`
    + `Prod.ext`; surjectivity follows from `landslideExtend_split`. -/
theorem landslideExtend_bijective {n : Nat} :
    Function.Bijective (fun (p : Bool × (Fin n -> Bool)) =>
      landslideExtend p.1 p.2) :=
  ⟨fun ⟨b1, e1⟩ ⟨b2, e2⟩ h =>
    let ⟨h_b, h_e⟩ := landslideExtend_eq_iff.mp h
    Prod.ext h_b h_e,
   fun e =>
    ⟨(e (Fin.last n), e ∘ Fin.castSucc), landslideExtend_split e⟩⟩

/-- *Inverse of `landslideExtend`.*  Splits a length-`(n+1)` pattern
    into its top bit and its restriction.  This is the explicit
    inverse to `landslideExtend` (proven via the roundtrip theorems
    below). -/
def landslideExtend_inv {n : Nat} (e : Fin (n + 1) -> Bool) :
    Bool × (Fin n -> Bool) :=
  (e (Fin.last n), e ∘ Fin.castSucc)

/-- *Roundtrip 1.*  `landslideExtend_inv (landslideExtend b e) = (b, e)`.
    The inverse recovers the (top bit, restriction) pair. -/
theorem landslideExtend_inv_landslideExtend
    {n : Nat} (b : Bool) (e : Fin n -> Bool) :
    landslideExtend_inv (landslideExtend b e) = (b, e) :=
  Prod.ext
    (landslideExtend_last b e)
    (funext fun i => landslideExtend_castSucc b e i)

/-- *Roundtrip 2.*  `landslideExtend (inv).1 (inv).2 = e`.  Building
    the extension from the split recovers the original pattern.
    Direct restatement of `landslideExtend_split`. -/
theorem landslideExtend_landslideExtend_inv
    {n : Nat} (e : Fin (n + 1) -> Bool) :
    landslideExtend (landslideExtend_inv e).1 (landslideExtend_inv e).2 = e :=
  landslideExtend_split e

/-- *Existential decomposition.*  Every length-`(n + 1)` pattern is
    `landslideExtend b e'` for some `b, e'`.  Existential form of the
    `landslideExtend_split` surjectivity. -/
theorem landslideExtend_exists {n : Nat} (e : Fin (n + 1) -> Bool) :
    ∃ b : Bool, ∃ e' : Fin n -> Bool, e = landslideExtend b e' :=
  ⟨e (Fin.last n), e ∘ Fin.castSucc, (landslideExtend_split e).symm⟩


/-- Extending by `true` adds `(n + 1)` to the bit-weight: the new top
    bit at position `n` contributes `n + 1`, and the original
    positions reproduce `bitWeight e` under `castSucc`. -/
theorem bitWeight_extend_true {n : Nat} (e : Fin n -> Bool) :
    bitWeight (landslideExtend true e) = bitWeight e + (n + 1) :=
  let f : Fin (n + 1) -> Nat :=
    fun i => if (landslideExtend true e) i then i.val + 1 else 0
  let step1 : (Finset.univ : Finset (Fin (n + 1))).sum f
            = (Finset.univ : Finset (Fin n)).sum (fun i => f i.castSucc)
              + f (Fin.last n) :=
    Fin.sum_univ_castSucc f
  let step_last_ite : f (Fin.last n) = (Fin.last n).val + 1 :=
    congrArg (fun b => if b then (Fin.last n).val + 1 else (0 : Nat))
      (landslideExtend_last true e)
  let step_last_val : (Fin.last n).val + 1 = n + 1 :=
    congrArg (· + 1) (Fin.val_last n)
  let step_last : f (Fin.last n) = n + 1 := step_last_ite.trans step_last_val
  let step_castSucc :
      (Finset.univ : Finset (Fin n)).sum (fun i => f i.castSucc)
    = bitWeight e :=
    Finset.sum_congr rfl fun i _ =>
      congrArg (fun b => if b then i.castSucc.val + 1 else (0 : Nat))
        (landslideExtend_castSucc true e i)
  step1.trans (congrArg₂ (· + ·) step_castSucc step_last)

/-- *Unified extension weight rule.*  Combines `bitWeight_extend_false`
    and `bitWeight_extend_true` into a single conditional formula:
    extending by bit `b` adds `(if b then n + 1 else 0)` to the
    bit-weight.  Useful when the top bit is bound to a generic
    `b : Bool` rather than a literal. -/
theorem bitWeight_landslideExtend {n : Nat} (b : Bool) (e : Fin n -> Bool) :
    bitWeight (landslideExtend b e)
      = bitWeight e + (if b then n + 1 else 0) :=
  Bool.casesOn (motive := fun b' =>
      bitWeight (landslideExtend b' e)
        = bitWeight e + (if b' then n + 1 else 0))
    b
    ((bitWeight_extend_false e).trans (add_zero _).symm)
    (bitWeight_extend_true e)

/-- *Extension never decreases bit-weight.*  Extending by either bit
    `b` produces a pattern of at least the original bit-weight.
    Composes `bitWeight_landslideExtend` with `Nat.le_add_right`. -/
theorem bitWeight_le_landslideExtend {n : Nat} (b : Bool) (e : Fin n -> Bool) :
    bitWeight e ≤ bitWeight (landslideExtend b e) :=
  (Nat.le_add_right (bitWeight e) (if b then n + 1 else 0)).trans
    (le_of_eq (bitWeight_landslideExtend b e).symm)

/-- *Extension by `true` strictly increases bit-weight.*  Adding a
    `true` bit at the top contributes `n + 1 > 0`, so the new weight
    is strictly larger. -/
theorem bitWeight_lt_landslideExtend_true {n : Nat} (e : Fin n -> Bool) :
    bitWeight e < bitWeight (landslideExtend true e) :=
  (Nat.lt_add_of_pos_right (Nat.succ_pos n)).trans_eq
    (bitWeight_extend_true e).symm

/-- *Weight decomposition under top bit false.*  When the top bit is
    `false`, the pattern's bit-weight equals its restriction's. -/
theorem bitWeight_split_false {n : Nat} (e : Fin (n + 1) -> Bool)
    (h : e (Fin.last n) = false) :
    bitWeight e = bitWeight (e ∘ Fin.castSucc) :=
  let h_split : landslideExtend (e (Fin.last n)) (e ∘ Fin.castSucc) = e :=
    landslideExtend_split e
  let h_split' : landslideExtend false (e ∘ Fin.castSucc) = e :=
    h ▸ h_split
  (congrArg bitWeight h_split'.symm).trans
    (bitWeight_extend_false (e ∘ Fin.castSucc))

/-- *Weight decomposition under top bit true.*  When the top bit is
    `true`, the pattern's bit-weight equals its restriction's plus
    `n + 1` (the top bit's logistic-weight contribution). -/
theorem bitWeight_split_true {n : Nat} (e : Fin (n + 1) -> Bool)
    (h : e (Fin.last n) = true) :
    bitWeight e = bitWeight (e ∘ Fin.castSucc) + (n + 1) :=
  let h_split : landslideExtend (e (Fin.last n)) (e ∘ Fin.castSucc) = e :=
    landslideExtend_split e
  let h_split' : landslideExtend true (e ∘ Fin.castSucc) = e :=
    h ▸ h_split
  (congrArg bitWeight h_split'.symm).trans
    (bitWeight_extend_true (e ∘ Fin.castSucc))

/-- *Restriction never increases bit-weight.*  `bitWeight (e ∘ castSucc)`
    is always at most `bitWeight e`.  Dual of `bitWeight_le_landslideExtend`:
    just as extending can only grow the weight, restricting can only
    shrink it. -/
theorem bitWeight_castSucc_le {n : Nat} (e : Fin (n + 1) -> Bool) :
    bitWeight (e ∘ Fin.castSucc) ≤ bitWeight e :=
  match h : e (Fin.last n) with
  | false => le_of_eq (bitWeight_split_false e h).symm
  | true =>
      let h_eq : bitWeight e = bitWeight (e ∘ Fin.castSucc) + (n + 1) :=
        bitWeight_split_true e h
      (Nat.le_add_right _ _).trans (le_of_eq h_eq.symm)

/-- *Restriction strictly decreases when top bit is true.*  When
    `e (Fin.last n) = true`, the restriction's bit-weight is strictly
    less than `bitWeight e` (by `n + 1 > 0`). -/
theorem bitWeight_castSucc_lt_of_last_true
    {n : Nat} (e : Fin (n + 1) -> Bool) (h : e (Fin.last n) = true) :
    bitWeight (e ∘ Fin.castSucc) < bitWeight e :=
  let h_eq : bitWeight e = bitWeight (e ∘ Fin.castSucc) + (n + 1) :=
    bitWeight_split_true e h
  (Nat.lt_add_of_pos_right (Nat.succ_pos n)).trans_eq h_eq.symm

/-- *Membership in a `landslideExtend`-mapped list.*  Pattern `e` is in
    `list.map (landslideExtend b)` iff its top bit equals `b` and its
    restriction is in `list`.  Combines `List.mem_map` with
    `landslideExtend_last`/`landslideExtend_castSucc`/`landslideExtend_split`. -/
theorem mem_map_extend_iff {n : Nat} (list : List (Fin n -> Bool))
    (b : Bool) (e : Fin (n + 1) -> Bool) :
    e ∈ list.map (landslideExtend b) <->
      e (Fin.last n) = b /\ (e ∘ Fin.castSucc) ∈ list :=
  ⟨fun h_mem =>
    let ⟨x, hx_in, hx_eq⟩ := List.mem_map.mp h_mem
    let h_last : b = e (Fin.last n) :=
      (landslideExtend_last b x).symm.trans (congrFun hx_eq (Fin.last n))
    let h_x : x = e ∘ Fin.castSucc :=
      funext fun i =>
        (landslideExtend_castSucc b x i).symm.trans (congrFun hx_eq i.castSucc)
    ⟨h_last.symm, h_x ▸ hx_in⟩,
   fun ⟨h_last, h_x_in⟩ =>
    let h_extend : landslideExtend b (e ∘ Fin.castSucc) = e :=
      h_last ▸ landslideExtend_split e
    List.mem_map.mpr ⟨e ∘ Fin.castSucc, h_x_in, h_extend⟩⟩

/-- *`landslide` correctness.*  Membership in `landslide n w` is
    equivalent to having bit-weight `w`.  Structural recursion on `n`:
    * `n = 0` is `landslide_zero_iff`.
    * `n + 1` case-splits on `n + 1 ≤ w` and on `e (Fin.last n)`,
      using `mem_map_extend_iff` to extract the restriction, the
      `bitWeight_split_*` lemmas to relate weights, and the IH on the
      restriction `e ∘ Fin.castSucc`. -/
theorem landslide_correct : forall (n w : Nat) (e : Fin n -> Bool),
    e ∈ landslide n w <-> bitWeight e = w
  | 0,     w, e => landslide_zero_iff e w
  | n + 1, w, e =>
    let e' : Fin n -> Bool := e ∘ Fin.castSucc
    let ih_w := landslide_correct n w e'
    let ih_w_sub := landslide_correct n (w - (n + 1)) e'
    ⟨fun h_mem =>
       if h_le : n + 1 ≤ w then
         let h_mem' :
             e ∈ (landslide n (w - (n + 1))).map (landslideExtend true)
                 ++ (landslide n w).map (landslideExtend false) :=
           Eq.mp (congrArg (e ∈ ·) (if_pos h_le)) h_mem
         (List.mem_append.mp h_mem').elim
           (fun h_top =>
             let ⟨h_b, h_x_in⟩ :=
               (mem_map_extend_iff _ true e).mp h_top
             let h_bw' : bitWeight e' = w - (n + 1) := ih_w_sub.mp h_x_in
             let h_bw_e : bitWeight e = bitWeight e' + (n + 1) :=
               bitWeight_split_true e h_b
             let h_eq : bitWeight e' + (n + 1) = w :=
               (congrArg (· + (n + 1)) h_bw').trans (Nat.sub_add_cancel h_le)
             h_bw_e.trans h_eq)
           (fun h_bot =>
             let ⟨h_b, h_x_in⟩ :=
               (mem_map_extend_iff _ false e).mp h_bot
             let h_bw' : bitWeight e' = w := ih_w.mp h_x_in
             let h_bw_e : bitWeight e = bitWeight e' :=
               bitWeight_split_false e h_b
             h_bw_e.trans h_bw')
       else
         let h_mem' : e ∈ (landslide n w).map (landslideExtend false) :=
           Eq.mp (congrArg (e ∈ ·) (if_neg h_le)) h_mem
         let ⟨h_b, h_x_in⟩ :=
           (mem_map_extend_iff _ false e).mp h_mem'
         let h_bw' : bitWeight e' = w := ih_w.mp h_x_in
         let h_bw_e : bitWeight e = bitWeight e' :=
           bitWeight_split_false e h_b
         h_bw_e.trans h_bw',
     fun h_bw =>
       match h_b : e (Fin.last n) with
       | true =>
         let h_bw_e : bitWeight e = bitWeight e' + (n + 1) :=
           bitWeight_split_true e h_b
         let h_sum : bitWeight e' + (n + 1) = w := h_bw_e.symm.trans h_bw
         let h_le : n + 1 ≤ w :=
           h_sum ▸ Nat.le_add_left (n + 1) (bitWeight e')
         let h_sub : bitWeight e' = w - (n + 1) :=
           (Nat.add_sub_cancel (bitWeight e') (n + 1)).symm.trans
             (congrArg (· - (n + 1)) h_sum)
         let h_e'_in : e' ∈ landslide n (w - (n + 1)) := ih_w_sub.mpr h_sub
         let h_top :
             e ∈ (landslide n (w - (n + 1))).map (landslideExtend true) :=
           (mem_map_extend_iff _ true e).mpr ⟨h_b, h_e'_in⟩
         let h_app :
             e ∈ (landslide n (w - (n + 1))).map (landslideExtend true)
                 ++ (landslide n w).map (landslideExtend false) :=
           List.mem_append.mpr (Or.inl h_top)
         Eq.mpr (congrArg (e ∈ ·) (if_pos h_le)) h_app
       | false =>
         let h_bw_e : bitWeight e = bitWeight e' :=
           bitWeight_split_false e h_b
         let h_bw' : bitWeight e' = w := h_bw_e.symm.trans h_bw
         let h_e'_in : e' ∈ landslide n w := ih_w.mpr h_bw'
         let h_bot : e ∈ (landslide n w).map (landslideExtend false) :=
           (mem_map_extend_iff _ false e).mpr ⟨h_b, h_e'_in⟩
         if h_le : n + 1 ≤ w then
           let h_app :
               e ∈ (landslide n (w - (n + 1))).map (landslideExtend true)
                   ++ (landslide n w).map (landslideExtend false) :=
             List.mem_append.mpr (Or.inr h_bot)
           Eq.mpr (congrArg (e ∈ ·) (if_pos h_le)) h_app
         else
           Eq.mpr (congrArg (e ∈ ·) (if_neg h_le)) h_bot⟩

/-- *Self-membership.*  Every pattern is in its own bit-weight bucket. -/
theorem landslide_self_mem {n : Nat} (e : Fin n -> Bool) :
    e ∈ landslide n (bitWeight e) :=
  (landslide_correct n (bitWeight e) e).mpr rfl

/-- *Bucket weights are unique.*  A pattern cannot live in two
    different landslide buckets.  Composes both directions of
    `landslide_correct`. -/
theorem landslide_unique_bucket
    {n w1 w2 : Nat} {e : Fin n -> Bool}
    (h1 : e ∈ landslide n w1) (h2 : e ∈ landslide n w2) :
    w1 = w2 :=
  ((landslide_correct n w1 e).mp h1).symm.trans
    ((landslide_correct n w2 e).mp h2)

/-- The total ORBGRAND enumeration: concatenation of landslide
    enumerations for weights `0, 1, 2, ...`. -/
def orbgrandEnumeration (n : Nat) : Nat -> List (Fin n -> Bool) :=
  fun w => landslide n w

/-- *ORBGRAND enumeration correctness.*  `orbgrandEnumeration n w` is
    the list of all length-`n` patterns of bit-weight `w`.  Wrapper
    around `landslide_correct`. -/
theorem orbgrandEnumeration_correct
    (n w : Nat) (e : Fin n -> Bool) :
    e ∈ orbgrandEnumeration n w <-> bitWeight e = w :=
  landslide_correct n w e

/-- *Bit-weight zero characterisation.*  A pattern has bit-weight zero
    iff all of its bits are `false`.  Structural recursion on `n`:
    * `n = 0`: vacuous (no positions to check).
    * `n + 1`: case-split on `e (Fin.last n)`.  The `true` case yields
      `bitWeight e ≥ n + 1 > 0`, contradicting weight `0`.  The
      `false` case recurses on the restriction. -/
theorem bitWeight_zero_iff_all_false :
    forall {n : Nat} (e : Fin n -> Bool),
      bitWeight e = 0 <-> forall i, e i = false
  | 0,     e =>
      ⟨fun _ i => i.elim0,
       fun _ => bitWeight_fin_zero e⟩
  | n + 1, e =>
      ⟨fun h_bw =>
         match h_b : e (Fin.last n) with
         | true =>
             let h_split : bitWeight e = bitWeight (e ∘ Fin.castSucc) + (n + 1) :=
               bitWeight_split_true e h_b
             let h_sum : bitWeight (e ∘ Fin.castSucc) + (n + 1) = 0 :=
               h_split.symm.trans h_bw
             let h_le : n + 1 ≤ 0 :=
               h_sum ▸ Nat.le_add_left (n + 1) (bitWeight (e ∘ Fin.castSucc))
             (Nat.not_succ_le_zero n h_le).elim
         | false =>
             let h_split : bitWeight e = bitWeight (e ∘ Fin.castSucc) :=
               bitWeight_split_false e h_b
             let h_bw' : bitWeight (e ∘ Fin.castSucc) = 0 :=
               h_split.symm.trans h_bw
             let ih_fwd : forall j : Fin n, (e ∘ Fin.castSucc) j = false :=
               (bitWeight_zero_iff_all_false (e ∘ Fin.castSucc)).mp h_bw'
             fun i =>
               Fin.lastCases (motive := fun j => e j = false)
                 h_b
                 (fun j => ih_fwd j)
                 i,
       fun h_all =>
         Finset.sum_eq_zero fun i _ =>
           congrArg (fun b => if b then i.val + 1 else (0 : Nat)) (h_all i)⟩

/-- *Restriction strict-decrease characterisation.*  The restriction
    `e ∘ Fin.castSucc` strictly decreases the bit-weight iff the top
    bit was true.  Lifts the forward-only
    `bitWeight_castSucc_lt_of_last_true` to an iff: the backward
    direction case-splits on `e (Fin.last n)` and uses
    `bitWeight_split_false` to derive contradiction when the top
    bit is false. -/
theorem bitWeight_castSucc_lt_iff_last_true
    {n : Nat} (e : Fin (n + 1) -> Bool) :
    bitWeight (e ∘ Fin.castSucc) < bitWeight e
      <-> e (Fin.last n) = true :=
  ⟨fun h_lt =>
    match h_b : e (Fin.last n) with
    | true  => rfl
    | false =>
        let h_eq : bitWeight e = bitWeight (e ∘ Fin.castSucc) :=
          bitWeight_split_false e h_b
        (Nat.lt_irrefl (bitWeight (e ∘ Fin.castSucc))
          (h_eq ▸ h_lt)).elim,
   fun h_true => bitWeight_castSucc_lt_of_last_true e h_true⟩

/-- *Constant-false pattern has bit-weight zero.*  Direct corollary of
    `bitWeight_zero_iff_all_false`. -/
theorem bitWeight_const_false {n : Nat} :
    bitWeight (fun _ : Fin n => false) = 0 :=
  (bitWeight_zero_iff_all_false _).mpr (fun _ => rfl)

/-- *All-true logistic weight = all-true bit-weight.*  Composing the
    constant-true function with the rank permutation gives back the
    same constant-true function (defeq via `∘` and beta), so the
    `logisticWeight_eq_bitWeight_comp` bridge collapses both sides
    to the same `bitWeight (fun _ => true)`.  Captures the
    permutation-invariance of the maximum logistic weight. -/
theorem logisticWeight_const_true_eq_bitWeight_const_true
    {n : Nat} (pi : ReliabilityRank n) :
    logisticWeight pi (fun _ : Fin n => true)
      = bitWeight (fun _ : Fin n => true) :=
  logisticWeight_eq_bitWeight_comp pi (fun _ : Fin n => true)

/-- *Logistic-weight equality is bit-weight equality under permutation.*
    Two patterns have equal logistic weight (under the same rank `pi`)
    iff their `pi.perm`-permuted compositions have equal bit-weight.
    Direct biconditional via two applications of the
    `logisticWeight_eq_bitWeight_comp` bridge. -/
theorem logisticWeight_eq_iff
    {n : Nat} (pi : ReliabilityRank n) (e1 e2 : Fin n -> Bool) :
    logisticWeight pi e1 = logisticWeight pi e2
      <-> bitWeight (e1 ∘ pi.perm) = bitWeight (e2 ∘ pi.perm) :=
  let f1 : logisticWeight pi e1 = bitWeight (e1 ∘ pi.perm) :=
    logisticWeight_eq_bitWeight_comp pi e1
  let f2 : logisticWeight pi e2 = bitWeight (e2 ∘ pi.perm) :=
    logisticWeight_eq_bitWeight_comp pi e2
  ⟨fun h => f1.symm.trans (h.trans f2),
   fun h => f1.trans (h.trans f2.symm)⟩

/-- *Logistic-weight strict order is bit-weight strict order under
    permutation.*  Strict-inequality companion of `logisticWeight_le_iff`.
    Each direction chains `Eq.trans_lt` with `LT.lt.trans_eq`. -/
theorem logisticWeight_lt_iff
    {n : Nat} (pi : ReliabilityRank n) (e1 e2 : Fin n -> Bool) :
    logisticWeight pi e1 < logisticWeight pi e2
      <-> bitWeight (e1 ∘ pi.perm) < bitWeight (e2 ∘ pi.perm) :=
  let f1 : logisticWeight pi e1 = bitWeight (e1 ∘ pi.perm) :=
    logisticWeight_eq_bitWeight_comp pi e1
  let f2 : logisticWeight pi e2 = bitWeight (e2 ∘ pi.perm) :=
    logisticWeight_eq_bitWeight_comp pi e2
  ⟨fun h => (f1.symm.trans_lt h).trans_eq f2,
   fun h => (f1.trans_lt h).trans_eq f2.symm⟩

/-- *Logistic-weight order is bit-weight order under permutation.*
    Inequality version of `logisticWeight_eq_iff`: ordering of
    logistic weights matches ordering of their `pi.perm`-permuted
    bit-weight compositions.  Each direction chains `Eq.trans_le`
    with `LE.le.trans_eq` through the bridge. -/
theorem logisticWeight_le_iff
    {n : Nat} (pi : ReliabilityRank n) (e1 e2 : Fin n -> Bool) :
    logisticWeight pi e1 <= logisticWeight pi e2
      <-> bitWeight (e1 ∘ pi.perm) <= bitWeight (e2 ∘ pi.perm) :=
  let f1 : logisticWeight pi e1 = bitWeight (e1 ∘ pi.perm) :=
    logisticWeight_eq_bitWeight_comp pi e1
  let f2 : logisticWeight pi e2 = bitWeight (e2 ∘ pi.perm) :=
    logisticWeight_eq_bitWeight_comp pi e2
  ⟨fun h => (f1.symm.trans_le h).trans_eq f2,
   fun h => (f1.trans_le h).trans_eq f2.symm⟩

/-- *Zero logistic weight characterisation.*  Bridges
    `bitWeight_zero_iff_all_false` over the rank permutation:
    `logisticWeight pi e = 0` iff every bit `e (pi.perm i)` is
    `false`.  Composes `logisticWeight_eq_bitWeight_comp` with the
    bit-weight iff. -/
theorem logisticWeight_zero_iff_all_false_at_perm
    {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    logisticWeight pi e = 0 <-> forall i, e (pi.perm i) = false :=
  let bridge : logisticWeight pi e = bitWeight (e ∘ pi.perm) :=
    logisticWeight_eq_bitWeight_comp pi e
  let h_bw : bitWeight (e ∘ pi.perm) = 0
           <-> forall i, (e ∘ pi.perm) i = false :=
    bitWeight_zero_iff_all_false (e ∘ pi.perm)
  ⟨fun h => h_bw.mp (bridge.symm.trans h),
   fun h => bridge.trans (h_bw.mpr h)⟩

/-- *Constant-false pattern is in landslide bucket 0.*  Combines
    `landslide_correct` (mpr) with `bitWeight_const_false`. -/
theorem const_false_mem_landslide_zero {n : Nat} :
    (fun _ : Fin n => false) ∈ landslide n 0 :=
  (landslide_correct n 0 _).mpr bitWeight_const_false

/-- *Upper bound on `bitWeight`.*  Each summand is bounded by
    `i.val + 1` (since the alternative is `0`); `Finset.sum_le_sum`
    gives the bound over the entire universe. -/
theorem bitWeight_le_sum {n : Nat} (e : Fin n -> Bool) :
    bitWeight e ≤ Finset.univ.sum (fun i : Fin n => i.val + 1) :=
  Finset.sum_le_sum fun i _ =>
    Bool.casesOn (motive := fun b => (if b then i.val + 1 else 0) ≤ i.val + 1)
      (e i)
      (Nat.zero_le (i.val + 1))
      (Nat.le_refl (i.val + 1))

/-- *Constant-true pattern realises the maximum bit-weight.*  Each
    summand `(if (fun _ => true) i then i.val + 1 else 0)` reduces by
    β + `cond true` to `i.val + 1`, so the entire sum collapses to
    `Finset.univ.sum (fun i => i.val + 1)`. -/
theorem bitWeight_const_true {n : Nat} :
    bitWeight (fun _ : Fin n => true)
      = Finset.univ.sum (fun i : Fin n => i.val + 1) := rfl

/-- *`bitWeight (fun _ => true)` is the maximum bit-weight.*  Composes
    `bitWeight_le_sum` with `bitWeight_const_true`. -/
theorem bitWeight_le_const_true {n : Nat} (e : Fin n -> Bool) :
    bitWeight e ≤ bitWeight (fun _ : Fin n => true) :=
  (bitWeight_le_sum e).trans (le_of_eq bitWeight_const_true.symm)

/-- *Strict inequality when a bit is false.*  If any position has
    `e i = false`, then `bitWeight e < bitWeight (fun _ => true)`.
    Proof: `Finset.sum_lt_sum` with the pointwise non-strict bound
    (from `bitWeight_le_sum`'s argument) plus the strict-at-witness
    bound `0 < i.val + 1` at the false position. -/
theorem bitWeight_lt_const_true_of_exists_false {n : Nat} (e : Fin n -> Bool)
    (h : ∃ i, e i = false) :
    bitWeight e < bitWeight (fun _ : Fin n => true) :=
  let ⟨i, h_e_i⟩ := h
  Finset.sum_lt_sum
    (fun j _ =>
      Bool.casesOn (motive := fun b => (if b then j.val + 1 else 0) ≤ j.val + 1)
        (e j)
        (Nat.zero_le (j.val + 1))
        (Nat.le_refl (j.val + 1)))
    ⟨i, Finset.mem_univ i,
     h_e_i ▸ (Nat.succ_pos i.val :
       (0 : Nat) < i.val + 1)⟩

/-- *Max-weight characterisation.*  `bitWeight e = bitWeight (fun _ => true)`
    iff every bit of `e` is `true`.  Dual of `bitWeight_zero_iff_all_false`.
    Forward direction: case-split on `e i` for each i; the `false`
    branch contradicts via `bitWeight_lt_const_true_of_exists_false`.
    Backward direction: `funext` collapses `e` to `fun _ => true`. -/
theorem bitWeight_eq_const_true_iff {n : Nat} (e : Fin n -> Bool) :
    bitWeight e = bitWeight (fun _ : Fin n => true) <-> forall i, e i = true :=
  ⟨fun h_eq i =>
    match h : e i with
    | true => rfl
    | false =>
        let h_ex : ∃ j, e j = false := ⟨i, h⟩
        let h_lt : bitWeight e < bitWeight (fun _ : Fin n => true) :=
          bitWeight_lt_const_true_of_exists_false e h_ex
        (Nat.lt_irrefl _ (h_eq ▸ h_lt)).elim,
   fun h_all => congrArg bitWeight (funext h_all)⟩

/-- *Zero-weight = pattern equality (with all-false).*  `bitWeight e = 0`
    iff `e = (fun _ => false)`.  Wraps `bitWeight_zero_iff_all_false`
    with `funext`. -/
theorem bitWeight_zero_iff_eq_const_false {n : Nat} (e : Fin n -> Bool) :
    bitWeight e = 0 <-> e = (fun _ : Fin n => false) :=
  ⟨fun h => funext ((bitWeight_zero_iff_all_false e).mp h),
   fun h => h ▸ bitWeight_const_false⟩

/-- *Max-weight = pattern equality (with all-true).*  `bitWeight e =
    bitWeight (fun _ => true)` iff `e = (fun _ => true)`.  Wraps
    `bitWeight_eq_const_true_iff` with `funext`. -/
theorem bitWeight_eq_max_iff_eq_const_true {n : Nat} (e : Fin n -> Bool) :
    bitWeight e = bitWeight (fun _ : Fin n => true)
      <-> e = (fun _ : Fin n => true) :=
  ⟨fun h => funext ((bitWeight_eq_const_true_iff e).mp h),
   fun h => congrArg bitWeight h⟩

/-- *Bucket empty above the max weight.*  When `w` strictly exceeds
    `bitWeight (fun _ => true)` (the max), `landslide n w` is empty.
    Proof: by `landslide_correct`, any element would have bit-weight
    `w`, but `bitWeight_le_const_true` gives `bitWeight e < w`,
    contradicting equality. -/
theorem landslide_eq_nil_of_too_large {n w : Nat}
    (h : bitWeight (fun _ : Fin n => true) < w) :
    landslide n w = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun e h_mem =>
    let h_eq : bitWeight e = w := (landslide_correct n w e).mp h_mem
    let h_le : bitWeight e ≤ bitWeight (fun _ : Fin n => true) :=
      bitWeight_le_const_true e
    let h_lt : bitWeight e < w := Nat.lt_of_le_of_lt h_le h
    Nat.lt_irrefl w (h_eq ▸ h_lt)

/-- *At length 1, the bucket for weight 2 is empty.*  Specialisation
    of `landslide_eq_nil_of_too_large`: since the maximum bit-weight
    at `n = 1` is `1` (from `bitWeight_one_true`), any weight `≥ 2`
    is unrealisable. -/
theorem landslide_one_two_eq_nil :
    landslide 1 2 = [] :=
  landslide_eq_nil_of_too_large
    (bitWeight_one_true.trans_lt (Nat.lt_succ_self 1))

/-- *At length 2, the bucket for weight 4 is empty.*  The maximum
    bit-weight at `n = 2` is `3` (from `bitWeight_two_true`), so
    weight `4` is unrealisable.  Same composition pattern as
    `landslide_one_two_eq_nil`. -/
theorem landslide_two_four_eq_nil :
    landslide 2 4 = [] :=
  landslide_eq_nil_of_too_large
    (bitWeight_two_true.trans_lt (Nat.lt_succ_self 3))

/-- *Bucket emptiness characterisation.*  `landslide n w` is empty
    iff no pattern has bit-weight `w`.  Both directions are direct
    applications of `landslide_correct`. -/
theorem landslide_eq_nil_iff {n w : Nat} :
    landslide n w = [] <-> forall (e : Fin n -> Bool), bitWeight e ≠ w :=
  ⟨fun h_nil e h_eq =>
    let h_mem : e ∈ landslide n w := (landslide_correct n w e).mpr h_eq
    List.not_mem_nil (h_nil ▸ h_mem),
   fun h_no =>
    List.eq_nil_iff_forall_not_mem.mpr fun e h_mem =>
      h_no e ((landslide_correct n w e).mp h_mem)⟩

/-- *Singleton-bucket uniqueness.*  When `landslide n w = [e]`, the
    pattern `e` is the unique pattern of bit-weight `w`.  Any other
    pattern `e'` with the same weight must equal `e`. -/
theorem landslide_singleton_unique {n w : Nat} {e : Fin n -> Bool}
    (h : landslide n w = [e]) (e' : Fin n -> Bool) (h_eq : bitWeight e' = w) :
    e' = e :=
  let h_mem : e' ∈ landslide n w := (landslide_correct n w e').mpr h_eq
  let h_mem' : e' ∈ [e] := h ▸ h_mem
  List.mem_singleton.mp h_mem'

/-- *Negation of `landslide_correct`.*  Non-membership in
    `landslide n w` characterises the bit-weight being different. -/
theorem landslide_not_mem_iff {n w : Nat} (e : Fin n -> Bool) :
    e ∉ landslide n w <-> bitWeight e ≠ w :=
  not_congr (landslide_correct n w e)

/-- *Extending all-false by false yields all-false.*  `Fin.lastCases`
    on each position: the new top is `false` (by `landslideExtend_last`),
    and original positions reproduce `false` (by `landslideExtend_castSucc`). -/
theorem landslideExtend_false_const_false {n : Nat} :
    landslideExtend false (fun _ : Fin n => false)
      = (fun _ : Fin (n + 1) => false) :=
  funext fun i =>
    Fin.lastCases
      (motive := fun j =>
        landslideExtend false (fun _ : Fin n => false) j = false)
      (landslideExtend_last false _)
      (fun j => landslideExtend_castSucc false _ j)
      i

/-- *Extending all-true by true yields all-true.*  Dual of
    `landslideExtend_false_const_false`. -/
theorem landslideExtend_true_const_true {n : Nat} :
    landslideExtend true (fun _ : Fin n => true)
      = (fun _ : Fin (n + 1) => true) :=
  funext fun i =>
    Fin.lastCases
      (motive := fun j =>
        landslideExtend true (fun _ : Fin n => true) j = true)
      (landslideExtend_last true _)
      (fun j => landslideExtend_castSucc true _ j)
      i

/-- *`landslide n` at the max weight is the singleton of the all-true
    pattern.*  Dual of `landslide_zero_singleton`.

    Structural recursion on `n`:
    * `n = 0`: `bitWeight (fun _ : Fin 0 => true) = 0`, so the bucket
      is `landslide 0 0 = [Fin.elim0]`; identify with the all-true
      pattern via `funext` over the empty domain.
    * `n + 1`: factor `max_(n+1) = bitWeight (fun _ => true) + (n + 1)`
      via `landslideExtend_true_const_true` + `bitWeight_extend_true`.
      The if-pos branch fires (`n + 1 ≤ max_(n+1)`); `withTop` becomes
      `[fun _ : Fin (n+1) => true]` by IH + extend-true; `withoutTop`
      is empty because `landslide n max_(n+1) = []` (max_(n+1) > max_n
      via `landslide_eq_nil_of_too_large`).  Combine with
      `List.append_nil`. -/
theorem landslide_max_singleton : forall {n : Nat},
    landslide n (bitWeight (fun _ : Fin n => true))
      = [fun _ : Fin n => true]
  | 0 =>
      let h_bw : bitWeight (fun _ : Fin 0 => true) = 0 :=
        bitWeight_fin_zero _
      let h_landslide : landslide 0 (bitWeight (fun _ : Fin 0 => true))
                      = [Fin.elim0] :=
        congrArg (landslide 0) h_bw
      let h_const_eq : (Fin.elim0 : Fin 0 -> Bool)
                     = (fun _ : Fin 0 => true) :=
        funext fun i : Fin 0 => i.elim0
      h_landslide.trans (congrArg (fun e => [e]) h_const_eq)
  | n + 1 =>
      let ih : landslide n (bitWeight (fun _ : Fin n => true))
             = [fun _ : Fin n => true] := landslide_max_singleton
      let M_n := bitWeight (fun _ : Fin n => true)
      let h_max_eq : bitWeight (fun _ : Fin (n + 1) => true)
                   = M_n + (n + 1) :=
        (congrArg bitWeight landslideExtend_true_const_true.symm).trans
          (bitWeight_extend_true _)
      let h_le : n + 1 ≤ M_n + (n + 1) := Nat.le_add_left (n + 1) M_n
      let h_sub : M_n + (n + 1) - (n + 1) = M_n :=
        Nat.add_sub_cancel M_n (n + 1)
      let h_lt : M_n < M_n + (n + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos n)
      let h_empty : landslide n (M_n + (n + 1)) = [] :=
        landslide_eq_nil_of_too_large h_lt
      let h_unfold : landslide (n + 1) (M_n + (n + 1))
                   = (landslide n ((M_n + (n + 1)) - (n + 1))).map
                       (landslideExtend true)
                     ++ (landslide n (M_n + (n + 1))).map
                       (landslideExtend false) :=
        if_pos h_le
      let h_with_sub :
          (landslide n ((M_n + (n + 1)) - (n + 1))).map (landslideExtend true)
          = (landslide n M_n).map (landslideExtend true) :=
        congrArg (·.map (landslideExtend true)) (congrArg (landslide n) h_sub)
      let h_with_ih : (landslide n M_n).map (landslideExtend true)
                    = [landslideExtend true (fun _ : Fin n => true)] :=
        congrArg (·.map (landslideExtend true)) ih
      let h_with_extend : [landslideExtend true (fun _ : Fin n => true)]
                        = [fun _ : Fin (n + 1) => true] :=
        congrArg (fun e => [e]) landslideExtend_true_const_true
      let h_without : (landslide n (M_n + (n + 1))).map (landslideExtend false)
                    = [] :=
        congrArg (·.map (landslideExtend false)) h_empty
      let h_combine_with :
          (landslide n ((M_n + (n + 1)) - (n + 1))).map (landslideExtend true)
          = [fun _ : Fin (n + 1) => true] :=
        h_with_sub.trans (h_with_ih.trans h_with_extend)
      let h_rhs :
          (landslide n ((M_n + (n + 1)) - (n + 1))).map (landslideExtend true)
          ++ (landslide n (M_n + (n + 1))).map (landslideExtend false)
          = [fun _ : Fin (n + 1) => true] :=
        (congrArg₂ (· ++ ·) h_combine_with h_without).trans
          (List.append_nil _)
      (congrArg (landslide (n + 1)) h_max_eq).trans (h_unfold.trans h_rhs)

/-- *`landslide n` at the max weight has length 1.*  Direct corollary
    of `landslide_max_singleton`. -/
theorem landslide_max_length {n : Nat} :
    (landslide n (bitWeight (fun _ : Fin n => true))).length = 1 :=
  congrArg List.length landslide_max_singleton

/-- *Max-weight bucket has no duplicates.*  Singleton list is `Nodup`. -/
theorem landslide_max_nodup {n : Nat} :
    (landslide n (bitWeight (fun _ : Fin n => true))).Nodup :=
  Eq.mpr (congrArg List.Nodup landslide_max_singleton) (List.nodup_singleton _)

/-- *`landslide n 0` is the singleton of the all-false pattern.*
    Structural recursion on `n`:
    * `n = 0`: `landslide 0 0 = [Fin.elim0]`; the unique
      `Fin 0 → Bool` value collapses to the all-false pattern.
    * `n + 1`: by IH, `landslide n 0 = [fun _ => false]`; mapping
      `landslideExtend false` yields `[fun _ => false]` via
      `landslideExtend_false_const_false`. -/
theorem landslide_zero_singleton : forall {n : Nat},
    landslide n 0 = [fun _ : Fin n => false]
  | 0 =>
      congrArg (fun e => [e]) (funext fun i : Fin 0 => i.elim0)
  | n + 1 =>
      let ih : landslide n 0 = [fun _ : Fin n => false] :=
        landslide_zero_singleton
      let h_neg : ¬ (n + 1 ≤ 0) := Nat.not_succ_le_zero n
      let h_unfolded_eq :
          (if n + 1 ≤ 0 then
             (landslide n (0 - (n + 1))).map (landslideExtend true)
             ++ (landslide n 0).map (landslideExtend false)
           else
             (landslide n 0).map (landslideExtend false))
          = (landslide n 0).map (landslideExtend false) :=
        if_neg h_neg
      let h_eq : landslide (n + 1) 0
               = (landslide n 0).map (landslideExtend false) :=
        h_unfolded_eq
      let h_map : (landslide n 0).map (landslideExtend false)
                = [landslideExtend false (fun _ : Fin n => false)] :=
        congrArg (·.map (landslideExtend false)) ih
      let h_singleton :
          [landslideExtend false (fun _ : Fin n => false)]
        = [fun _ : Fin (n + 1) => false] :=
        congrArg (fun e => [e]) landslideExtend_false_const_false
      h_eq.trans (h_map.trans h_singleton)

/-- *Zero-weight bucket has no duplicates.*  Singleton list is `Nodup`. -/
theorem landslide_zero_nodup {n : Nat} :
    (landslide n 0).Nodup :=
  Eq.mpr (congrArg List.Nodup landslide_zero_singleton) (List.nodup_singleton _)

/-- *`landslide n 0` has length 1.*  Structural recursion on `n`:
    * `n = 0`: trivially length 1 (the singleton `[Fin.elim0]`).
    * `n + 1`: `n + 1 > 0` forces the else branch, so
      `landslide (n + 1) 0 = (landslide n 0).map (landslideExtend false)`.
      Length unchanged by `List.length_map`, and IH gives length 1. -/
theorem landslide_zero_length : forall {n : Nat}, (landslide n 0).length = 1
  | 0 => rfl
  | n + 1 =>
      let ih : (landslide n 0).length = 1 := landslide_zero_length
      let h_neg : ¬ (n + 1 ≤ 0) := Nat.not_succ_le_zero n
      let h_unfolded_eq :
          (if n + 1 ≤ 0 then
             (landslide n (0 - (n + 1))).map (landslideExtend true)
             ++ (landslide n 0).map (landslideExtend false)
           else
             (landslide n 0).map (landslideExtend false))
          = (landslide n 0).map (landslideExtend false) :=
        if_neg h_neg
      let h_eq : landslide (n + 1) 0
               = (landslide n 0).map (landslideExtend false) :=
        h_unfolded_eq
      let h_step : (landslide (n + 1) 0).length
                 = ((landslide n 0).map (landslideExtend false)).length :=
        congrArg List.length h_eq
      let h_map_len :
          ((landslide n 0).map (landslideExtend false)).length
        = (landslide n 0).length :=
        List.length_map (landslideExtend false)
      h_step.trans (h_map_len.trans ih)

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

/-- *Constant-false pattern is in bucket 0.*  The all-zero error
    pattern has logistic weight `0` (by `logisticWeight_const_false`),
    so it sits in bucket `0`.  One-line corollary of the definition. -/
theorem landslideBucket_const_false_zero
    {n : Nat} (pi : ReliabilityRank n) :
    landslideBucket pi 0 (fun _ : Fin n => false) :=
  logisticWeight_const_false pi

/-- *Bucket uniqueness.*  Each pattern belongs to at most one bucket:
    if `e` is in buckets `w1` and `w2`, then `w1 = w2`.  Direct
    consequence of `landslideBucket pi w e` being `logisticWeight pi
    e = w` definitionally; `h1.symm.trans h2` chains the two
    equalities. -/
theorem landslideBucket_unique
    {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat} {e : Fin n -> Bool}
    (h1 : landslideBucket pi w1 e) (h2 : landslideBucket pi w2 e) :
    w1 = w2 :=
  h1.symm.trans h2

/-- *Bucket uniqueness, symmetric form.*  Mirror of
    `landslideBucket_unique` with the equality reversed. -/
theorem landslideBucket_unique_symm
    {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat} {e : Fin n -> Bool}
    (h1 : landslideBucket pi w1 e) (h2 : landslideBucket pi w2 e) :
    w2 = w1 :=
  h2.symm.trans h1

/-- *Constant-true pattern lives in its own logistic-weight bucket.*
    Mirror of `landslideBucket_const_false_zero`: the all-one error
    pattern sits in the bucket indexed by its own logistic weight.
    One-line `rfl`. -/
theorem landslideBucket_const_true
    {n : Nat} (pi : ReliabilityRank n) :
    landslideBucket pi (logisticWeight pi (fun _ : Fin n => true))
      (fun _ : Fin n => true) :=
  rfl

/-- *Bucket characterisation of the all-false pattern.*  The
    constant-false pattern lives in bucket `w` iff `w = 0`.
    Strengthens `landslideBucket_const_false_zero` to a
    biconditional. -/
theorem landslideBucket_const_false_iff
    {n : Nat} (pi : ReliabilityRank n) (w : Nat) :
    landslideBucket pi w (fun _ : Fin n => false) <-> w = 0 :=
  ⟨fun h => h.symm.trans (logisticWeight_const_false pi),
   fun h => (logisticWeight_const_false pi).trans h.symm⟩

/-- *Same bucket ⇒ equal weight.*  If `e1` and `e2` both inhabit
    bucket `w`, their logistic weights coincide.  Bridges bucket
    membership to weight equality; chains `h1.trans h2.symm`. -/
theorem landslideBucket_eq_of_same_bucket
    {n : Nat} (pi : ReliabilityRank n) {w : Nat}
    {e1 e2 : Fin n -> Bool}
    (h1 : landslideBucket pi w e1) (h2 : landslideBucket pi w e2) :
    logisticWeight pi e1 = logisticWeight pi e2 :=
  h1.trans h2.symm

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

/-- *Maximum logistic weight characterisation.*  A pattern reaches the
    `(fun _ => true)` maximum logistic weight iff every bit at every
    rank position is `true`.  Composes three existing theorems:
    `logisticWeight_const_true_eq_bitWeight_const_true` (max equals
    `bitWeight (fun _ => true)`), `logisticWeight_eq_bitWeight_comp`
    (bridge to permuted bit-weight), and `bitWeight_eq_const_true_iff`
    (bit-weight maximum characterisation). -/
theorem logisticWeight_eq_const_true_iff_all_true
    {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    logisticWeight pi e = logisticWeight pi (fun _ : Fin n => true)
      <-> forall i, e (pi.perm i) = true :=
  let max_eq : logisticWeight pi (fun _ : Fin n => true)
             = bitWeight (fun _ : Fin n => true) :=
    logisticWeight_const_true_eq_bitWeight_const_true pi
  let bridge : logisticWeight pi e = bitWeight (e ∘ pi.perm) :=
    logisticWeight_eq_bitWeight_comp pi e
  let bw_iff : bitWeight (e ∘ pi.perm)
              = bitWeight (fun _ : Fin n => true)
             <-> forall i, (e ∘ pi.perm) i = true :=
    bitWeight_eq_const_true_iff (e ∘ pi.perm)
  ⟨fun h =>
    let h2 : bitWeight (e ∘ pi.perm)
           = bitWeight (fun _ : Fin n => true) :=
      (bridge.symm.trans h).trans max_eq
    bw_iff.mp h2,
   fun h =>
    let h2 : bitWeight (e ∘ pi.perm)
           = bitWeight (fun _ : Fin n => true) :=
      bw_iff.mpr h
    (bridge.trans h2).trans max_eq.symm⟩

/-- *Function-equality form of the restrict-extend identity.*  The
    composition `landslideExtend false ∘ (·∘ Fin.castSucc)` recovers
    `e` exactly when the top bit was already `false`.  Forward uses
    `landslideExtend_last`; backward uses `Fin.lastCases` to do a
    funext on the top vs castSucc branches. -/
theorem landslideExtend_false_castSucc_eq_iff_last_false
    {n : Nat} (e : Fin (n + 1) -> Bool) :
    landslideExtend false (e ∘ Fin.castSucc) = e
      <-> e (Fin.last n) = false :=
  ⟨fun h =>
    let s_last : landslideExtend false (e ∘ Fin.castSucc) (Fin.last n)
               = false :=
      landslideExtend_last false (e ∘ Fin.castSucc)
    let s_eval : landslideExtend false (e ∘ Fin.castSucc) (Fin.last n)
               = e (Fin.last n) :=
      congrFun h (Fin.last n)
    s_eval.symm.trans s_last,
   fun h_last => funext fun i =>
     Fin.lastCases
       (motive :=
         fun i => landslideExtend false (e ∘ Fin.castSucc) i = e i)
       ((landslideExtend_last false (e ∘ Fin.castSucc)).trans h_last.symm)
       (fun j => landslideExtend_castSucc false (e ∘ Fin.castSucc) j)
       i⟩

/-- *Restriction-then-extend by `true` recovers equality when top bit
    is true.*  Symmetric to `landslideExtend_false_castSucc_eq_iff_last_false`:
    `landslideExtend true (e ∘ Fin.castSucc) = e` iff
    `e (Fin.last n) = true`. -/
theorem landslideExtend_true_castSucc_eq_iff_last_true
    {n : Nat} (e : Fin (n + 1) -> Bool) :
    landslideExtend true (e ∘ Fin.castSucc) = e
      <-> e (Fin.last n) = true :=
  ⟨fun h =>
    let s_last : landslideExtend true (e ∘ Fin.castSucc) (Fin.last n)
               = true :=
      landslideExtend_last true (e ∘ Fin.castSucc)
    let s_eval : landslideExtend true (e ∘ Fin.castSucc) (Fin.last n)
               = e (Fin.last n) :=
      congrFun h (Fin.last n)
    s_eval.symm.trans s_last,
   fun h_last => funext fun i =>
     Fin.lastCases
       (motive :=
         fun i => landslideExtend true (e ∘ Fin.castSucc) i = e i)
       ((landslideExtend_last true (e ∘ Fin.castSucc)).trans h_last.symm)
       (fun j => landslideExtend_castSucc true (e ∘ Fin.castSucc) j)
       i⟩

/-- *Restriction-then-extend by `true`.*  Symmetric to the `false`
    version: extending the restriction by `true` adds zero (if the
    original top bit was already `true`) or `n + 1` (if the top was
    `false`).  Cleaner addition form than the subtraction-based
    `_false` variant. -/
theorem landslideExtend_true_castSucc_bitWeight
    {n : Nat} (e : Fin (n + 1) -> Bool) :
    bitWeight (landslideExtend true (e ∘ Fin.castSucc))
      = bitWeight e + (if e (Fin.last n) then 0 else n + 1) :=
  match h_b : e (Fin.last n) with
  | true =>
      let h_split : bitWeight e
                  = bitWeight (e ∘ Fin.castSucc) + (n + 1) :=
        bitWeight_split_true e h_b
      let h_extend : bitWeight (landslideExtend true (e ∘ Fin.castSucc))
                   = bitWeight (e ∘ Fin.castSucc) + (n + 1) :=
        bitWeight_extend_true (e ∘ Fin.castSucc)
      h_extend.trans h_split.symm
  | false =>
      let h_split : bitWeight e = bitWeight (e ∘ Fin.castSucc) :=
        bitWeight_split_false e h_b
      let h_extend : bitWeight (landslideExtend true (e ∘ Fin.castSucc))
                   = bitWeight (e ∘ Fin.castSucc) + (n + 1) :=
        bitWeight_extend_true (e ∘ Fin.castSucc)
      let h_lift : bitWeight (e ∘ Fin.castSucc) + (n + 1)
                 = bitWeight e + (n + 1) :=
        congrArg (fun x => x + (n + 1)) h_split.symm
      h_extend.trans h_lift

/-- *Restriction-then-extend by `false` recovers bit-weight minus
    top-bit contribution.*  Combines `bitWeight_split_true` /
    `bitWeight_split_false` with `bitWeight_extend_false`: the
    restriction's bit-weight equals `bitWeight e` minus `(n + 1)`
    when the top bit was `true`, or unchanged when `false`.  The
    `if e (Fin.last n)` packages both branches into one formula. -/
theorem landslideExtend_false_castSucc_bitWeight
    {n : Nat} (e : Fin (n + 1) -> Bool) :
    bitWeight (landslideExtend false (e ∘ Fin.castSucc))
      = bitWeight e - (if e (Fin.last n) then n + 1 else 0) :=
  match h_b : e (Fin.last n) with
  | true =>
      let h_split : bitWeight e
                  = bitWeight (e ∘ Fin.castSucc) + (n + 1) :=
        bitWeight_split_true e h_b
      let h_extend : bitWeight (landslideExtend false (e ∘ Fin.castSucc))
                   = bitWeight (e ∘ Fin.castSucc) :=
        bitWeight_extend_false (e ∘ Fin.castSucc)
      let h_cancel : bitWeight (e ∘ Fin.castSucc)
                   = bitWeight (e ∘ Fin.castSucc) + (n + 1) - (n + 1) :=
        (Nat.add_sub_cancel (bitWeight (e ∘ Fin.castSucc)) (n + 1)).symm
      let h_lift : bitWeight (e ∘ Fin.castSucc) + (n + 1) - (n + 1)
                 = bitWeight e - (n + 1) :=
        congrArg (fun x => x - (n + 1)) h_split.symm
      h_extend.trans (h_cancel.trans h_lift)
  | false =>
      let h_split : bitWeight e = bitWeight (e ∘ Fin.castSucc) :=
        bitWeight_split_false e h_b
      let h_extend : bitWeight (landslideExtend false (e ∘ Fin.castSucc))
                   = bitWeight (e ∘ Fin.castSucc) :=
        bitWeight_extend_false (e ∘ Fin.castSucc)
      h_extend.trans h_split.symm

/-- *Strict logistic-weight bound when some rank position is false.*
    The strict-inequality companion of `logisticWeight_eq_const_true_iff_all_true`:
    if any bit at any rank position is `false`, the logistic weight
    strictly undershoots the maximum.  Composes
    `logisticWeight_eq_bitWeight_comp`, `bitWeight_lt_const_true_of_exists_false`,
    and `logisticWeight_const_true_eq_bitWeight_const_true`. -/
theorem logisticWeight_lt_const_true_of_exists_false_at_perm
    {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool)
    (h : ∃ i, e (pi.perm i) = false) :
    logisticWeight pi e
      < logisticWeight pi (fun _ : Fin n => true) :=
  let bridge : logisticWeight pi e = bitWeight (e ∘ pi.perm) :=
    logisticWeight_eq_bitWeight_comp pi e
  let max_bridge : logisticWeight pi (fun _ : Fin n => true)
                 = bitWeight (fun _ : Fin n => true) :=
    logisticWeight_const_true_eq_bitWeight_const_true pi
  let h_ex : ∃ j : Fin n, (e ∘ pi.perm) j = false :=
    let ⟨i, h_i⟩ := h
    ⟨i, h_i⟩
  let h_lt : bitWeight (e ∘ pi.perm)
           < bitWeight (fun _ : Fin n => true) :=
    bitWeight_lt_const_true_of_exists_false (e ∘ pi.perm) h_ex
  (bridge.trans_lt h_lt).trans_eq max_bridge.symm

/-- *Bucket membership unfolds to logistic-weight equality.*
    Direct biconditional form of the `landslideBucket` definition. -/
theorem landslideBucket_iff
    {n : Nat} (pi : ReliabilityRank n) (w : Nat) (e : Fin n -> Bool) :
    landslideBucket pi w e <-> logisticWeight pi e = w :=
  Iff.rfl

/-- *Bucket characterisation of the all-true pattern.*  Dual of
    `landslideBucket_const_false_iff`: both directions are just the
    symmetric form of the definitional equality. -/
theorem landslideBucket_const_true_iff
    {n : Nat} (pi : ReliabilityRank n) (w : Nat) :
    landslideBucket pi w (fun _ : Fin n => true)
      <-> w = logisticWeight pi (fun _ : Fin n => true) :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- *Bucket-zero characterisation under the rank permutation.*  A
    pattern is in bucket `0` iff every bit at every rank position is
    `false`.  Bridges `landslideBucket` to the underlying
    `logisticWeight = 0` predicate (definitional) and forwards to
    `logisticWeight_zero_iff_all_false_at_perm`. -/
theorem landslideBucket_zero_iff_all_false_at_perm
    {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    landslideBucket pi 0 e <-> forall i, e (pi.perm i) = false :=
  logisticWeight_zero_iff_all_false_at_perm pi e

/-- *Bucket index congruence.*  Bucket membership respects equality
    of the bucket index.  Direct rewrite via the hypothesis. -/
theorem landslideBucket_weight_congr
    {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat} (e : Fin n -> Bool)
    (h : w1 = w2) :
    landslideBucket pi w1 e <-> landslideBucket pi w2 e :=
  h ▸ Iff.rfl

/-- *Bucket membership transports across equal-weight patterns.*
    If `e1` lives in bucket `w` and `e1, e2` have the same logistic
    weight, then `e2` lives in bucket `w` too. -/
theorem landslideBucket_transport
    {n : Nat} (pi : ReliabilityRank n) {w : Nat} {e1 e2 : Fin n -> Bool}
    (h1 : landslideBucket pi w e1)
    (h_eq : logisticWeight pi e1 = logisticWeight pi e2) :
    landslideBucket pi w e2 :=
  h_eq.symm.trans h1

/-- *Boolean-algebra corollary: conjoined bucket memberships collapse
    to an index equation.*  A pattern `e` simultaneously inhabits
    buckets `w1` and `w2` iff the bucket indices coincide and one of
    the memberships holds.  Forward direction uses
    `landslideBucket_unique`; the reverse transports the membership
    along the index equality via `landslideBucket_weight_congr`. -/
theorem landslideBucket_and_iff
    {n : Nat} (pi : ReliabilityRank n) (w1 w2 : Nat) (e : Fin n -> Bool) :
    landslideBucket pi w1 e /\ landslideBucket pi w2 e
      <-> w1 = w2 /\ landslideBucket pi w1 e :=
  ⟨fun h => ⟨landslideBucket_unique pi h.1 h.2, h.1⟩,
   fun h => ⟨h.2, (landslideBucket_weight_congr pi e h.1).mp h.2⟩⟩

/-- *Constant-false sits in bucket zero via the perm characterisation.*
    Re-derivation of `landslideBucket_const_false_zero` through
    `landslideBucket_zero_iff_all_false_at_perm`. -/
theorem landslideBucket_zero_const_false_alt
    {n : Nat} (pi : ReliabilityRank n) :
    landslideBucket pi 0 (fun _ : Fin n => false) :=
  (landslideBucket_zero_iff_all_false_at_perm pi _).mpr (fun _ => rfl)

end Section04
end OrbgrandAi
