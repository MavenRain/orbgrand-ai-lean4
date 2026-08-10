import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section04.OrbgrandAi
import KanTactics

/-!
# Section VI.A.  Query-order stability under correlation perturbation

Formalizes the *robustness-of-the-query-order* observation from
Section VI.A of the paper, Fig. 11.

## Setup

The ORBGRAND-AI query order depends on the assumed correlation
`rho` via the substitution penalties

  w_i = log p(t* | Y_i) - log p(t | Y_i).

If the receiver uses an imperfect estimate `rho_est = rho_real + delta_rho`,
the penalties become

  w_i(rho_est) = w_i(rho_real) + O(delta_rho).

Even for `delta_rho` as large as `0.2`, the resulting BLER
degradation is small (paper, Fig. 11: ~0.5 dB at BLER `1e-3`).
The paper attributes this to the fact that the *exact* magnitude
of correlation is less important than the fact that neighbouring
symbols *are* correlated: the *relative* ranking of substitution
penalties is essentially preserved under small perturbations.

## What we formalize

This file states the stability claim: for sufficiently small
`|delta_rho|`, the resulting permutation of the query order is
*close to* the true query order in some metric (e.g., Kendall tau).
The BLER consequence is empirical.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section06

open OrbgrandAi.Section02

/-! ## Kendall tau distance (abstract) -/

/-- A finite list of pattern indices ordered by their assumed
    posterior under some correlation parameter.  Concrete instances
    of this list come from ORBGRAND-AI's pattern enumeration. -/
abbrev QueryOrder (numPatterns : Nat) := List (Fin numPatterns)

/-- Index of `x` within `xs`, or `xs.length` if `x` does not appear.
    Pure-Lean replacement for `List.idxOf` (which is not in scope at
    this commit of Mathlib); structurally recursive on the list. -/
def QueryOrder.positionOf {numPatterns : Nat}
    (x : Fin numPatterns) : QueryOrder numPatterns -> Nat
  | []        => 0
  | (y :: ys) =>
      if x = y then 0 else QueryOrder.positionOf x ys + 1

/-- *Position in the empty order is zero.*  Direct unfolding of the
    `[]` arm of `QueryOrder.positionOf`. -/
theorem QueryOrder.positionOf_nil {numPatterns : Nat}
    (x : Fin numPatterns) :
    QueryOrder.positionOf x ([] : QueryOrder numPatterns) = 0 := rfl

/-- Kendall tau distance between two query orders.

    Counts the number of unordered pairs `{i, j} ⊆ Fin numPatterns`
    with `i.val < j.val` such that `a` and `b` disagree on the
    relative order of `i` and `j` (one puts `i` before `j`, the
    other puts `i` after `j`).  For lists that are *permutations* of
    `Fin numPatterns` this gives the standard Kendall tau distance;
    for lists that miss some indices the positions of missing
    indices coincide (both default to `length`), so the missing
    pairs contribute zero by the same-side check.

    Concretely: iterate `i, j : Fin numPatterns`, restrict to
    `i.val < j.val`, look up positions in `a` and `b`, and add `1`
    iff `(pos_a i < pos_a j)` disagrees with `(pos_b i < pos_b j)`. -/
def kendallTau {numPatterns : Nat} (a b : QueryOrder numPatterns) : Nat :=
  Finset.univ.sum fun i : Fin numPatterns =>
    Finset.univ.sum fun j : Fin numPatterns =>
      if i.val < j.val then
        let ai := QueryOrder.positionOf i a
        let aj := QueryOrder.positionOf j a
        let bi := QueryOrder.positionOf i b
        let bj := QueryOrder.positionOf j b
        if decide (ai < aj) = decide (bi < bj) then 0 else 1
      else 0

/-- *Non-negativity.*  `kendallTau` returns a `Nat`, which is
    universally non-negative.  Trivial via `Nat.zero_le`. -/
theorem kendallTau_nonneg {numPatterns : Nat}
    (a b : QueryOrder numPatterns) :
    0 <= kendallTau a b :=
  Nat.zero_le _

/-- *Reflexivity.*  `kendallTau a a = 0`: every pair `(i, j)` with
    `i.val < j.val` finds `decide (positionOf i a < positionOf j a) =
    decide (positionOf i a < positionOf j a)` (= `rfl`), so the inner
    `if` returns `0`.  All summands are `0`, and the double sum
    vanishes by `Finset.sum_const_zero` (twice). -/
theorem kendallTau_self {numPatterns : Nat} (a : QueryOrder numPatterns) :
    kendallTau a a = 0 :=
  Finset.sum_eq_zero fun i _ =>
    Finset.sum_eq_zero fun j _ =>
      if h : i.val < j.val then
        let ai := QueryOrder.positionOf i a
        let aj := QueryOrder.positionOf j a
        let h_inner : decide (ai < aj) = decide (ai < aj) := rfl
        (if_pos h).trans (if_pos h_inner)
      else
        if_neg h

/-- *Symmetry.*  `kendallTau a b = kendallTau b a`: the only
    structural difference between the two double sums is the order of
    `decide (... < ...) = decide (... < ...)` on the inner condition,
    and `Eq` is symmetric.  Use `if_congr` on the inner ite to bridge
    the `Iff` from `Eq.symm`. -/
theorem kendallTau_symm {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    kendallTau a b = kendallTau b a :=
  Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ =>
      if h : i.val < j.val then
        let pa_i := QueryOrder.positionOf i a
        let pa_j := QueryOrder.positionOf j a
        let pb_i := QueryOrder.positionOf i b
        let pb_j := QueryOrder.positionOf j b
        let h_iff :
            (decide (pa_i < pa_j) = decide (pb_i < pb_j)) ↔
              (decide (pb_i < pb_j) = decide (pa_i < pa_j)) :=
          ⟨Eq.symm, Eq.symm⟩
        (if_pos h).trans
          ((if_congr h_iff rfl rfl).trans (if_pos h).symm)
      else
        (if_neg h).trans (if_neg h).symm

/-- *Per-pair upper bound.*  Each `(i, j)` summand of `kendallTau` is
    at most `1`: the outer if returns `0` on `¬ i.val < j.val`, and on
    the positive branch the inner if returns `0` or `1`. -/
theorem kendallTau_summand_le_one
    {numPatterns : Nat} (a b : QueryOrder numPatterns) (i j : Fin numPatterns) :
    (if i.val < j.val then
        let ai := QueryOrder.positionOf i a
        let aj := QueryOrder.positionOf j a
        let bi := QueryOrder.positionOf i b
        let bj := QueryOrder.positionOf j b
        if decide (ai < aj) = decide (bi < bj) then (0 : Nat) else 1
      else 0) ≤ 1 :=
  if h : i.val < j.val then
    let ai := QueryOrder.positionOf i a
    let aj := QueryOrder.positionOf j a
    let bi := QueryOrder.positionOf i b
    let bj := QueryOrder.positionOf j b
    if h2 : decide (ai < aj) = decide (bi < bj) then
      (if_pos h).trans_le ((if_pos h2).trans_le (Nat.zero_le 1))
    else
      (if_pos h).trans_le ((if_neg h2).trans_le (Nat.le_refl 1))
  else
    (if_neg h).trans_le (Nat.zero_le 1)

/-- *Agreement implies zero distance.*  If `a` and `b` agree on the
    relative order of every pair `i.val < j.val` (i.e., the
    `decide`-equality holds at every such pair), then
    `kendallTau a b = 0`.

    Generalizes `kendallTau_self` (which is the `b = a` case where
    agreement is trivial via `rfl`).  Same proof skeleton:
    `Finset.sum_eq_zero` twice, then per-pair dispatch on
    `i.val < j.val` with `if_pos` chaining the agreement-witness
    through the inner `if`. -/
theorem kendallTau_eq_zero_of_agreement
    {numPatterns : Nat} (a b : QueryOrder numPatterns)
    (h : forall (i j : Fin numPatterns), i.val < j.val ->
      decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
        = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)) :
    kendallTau a b = 0 :=
  Finset.sum_eq_zero fun i _ =>
    Finset.sum_eq_zero fun j _ =>
      if hij : i.val < j.val then
        (if_pos hij).trans (if_pos (h i j hij))
      else
        if_neg hij

/-- *Zero distance implies agreement.*  Converse of
    `kendallTau_eq_zero_of_agreement`: if `kendallTau a b = 0`, then
    `a` and `b` order every pair `i.val < j.val` the same way.

    Proof: strip the double sum via `Finset.sum_eq_zero_iff_of_nonneg`
    twice (Nat values are unconditionally nonneg).  At a fixed pair
    `(i, j)` with `i.val < j.val`, the outer `if_pos hij` extracts the
    inner `if` as `0`.  Case-split on the inner `decide`-equality: the
    `else` branch yields `1 = 0`, contradicting `Nat.succ_ne_zero 0`. -/
theorem kendallTau_agreement_of_eq_zero
    {numPatterns : Nat} (a b : QueryOrder numPatterns)
    (h : kendallTau a b = 0)
    (i j : Fin numPatterns) (hij : i.val < j.val) :
    decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
      = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b) :=
  let h_inner_sum_zero :
      Finset.univ.sum (fun j' : Fin numPatterns =>
        if i.val < j'.val then
          let ai := QueryOrder.positionOf i a
          let aj := QueryOrder.positionOf j' a
          let bi := QueryOrder.positionOf i b
          let bj := QueryOrder.positionOf j' b
          if decide (ai < aj) = decide (bi < bj) then (0 : Nat) else 1
        else 0) = 0 :=
    ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h)
      i (Finset.mem_univ i)
  let h_summand_zero :
      (if i.val < j.val then
        let ai := QueryOrder.positionOf i a
        let aj := QueryOrder.positionOf j a
        let bi := QueryOrder.positionOf i b
        let bj := QueryOrder.positionOf j b
        if decide (ai < aj) = decide (bi < bj) then (0 : Nat) else 1
      else 0) = 0 :=
    ((Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => Nat.zero_le _)).mp h_inner_sum_zero)
      j (Finset.mem_univ j)
  let h_inner_if_zero :
      (if decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
          = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
        then (0 : Nat) else 1) = 0 :=
    (if_pos hij).symm.trans h_summand_zero
  if h_eq : decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
            = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b) then
    h_eq
  else
    absurd ((if_neg h_eq).symm.trans h_inner_if_zero) (Nat.succ_ne_zero 0)

/-- *Zero-distance characterization (iff).*  `kendallTau a b = 0` iff
    `a` and `b` order every pair `i.val < j.val` the same way.
    Packages `kendallTau_eq_zero_of_agreement` and
    `kendallTau_agreement_of_eq_zero` into a single iff. -/
theorem kendallTau_eq_zero_iff
    {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    kendallTau a b = 0 ↔
      forall (i j : Fin numPatterns), i.val < j.val ->
        decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
          = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b) :=
  ⟨kendallTau_agreement_of_eq_zero a b,
   kendallTau_eq_zero_of_agreement a b⟩

/-- *Self-distance characterization via the iff.*  Restates
    `kendallTau_self` as the right-to-left of `kendallTau_eq_zero_iff`
    applied at `b = a`, where the agreement hypothesis is `rfl` at
    every pair.  Alternative proof route to the direct construction
    in `kendallTau_self`; useful as a sanity-check that the iff is
    consistent with the reflexivity lemma. -/
theorem kendallTau_self_eq_zero {numPatterns : Nat}
    (a : QueryOrder numPatterns) :
    kendallTau a a = 0 :=
  (kendallTau_eq_zero_iff a a).mpr (fun _ _ _ => rfl)

/-- *Empty domain.*  At `numPatterns = 0` the only `QueryOrder 0` is `[]`,
    so `kendallTau` is `0` on any pair of inputs (vacuously via
    `Fin.elim0` — there are no `i, j : Fin 0` to disagree on). -/
theorem kendallTau_empty (a b : QueryOrder 0) : kendallTau a b = 0 :=
  Finset.sum_eq_zero fun i _ => Fin.elim0 i

/-- *Singleton domain.*  At `numPatterns = 1` every `i j : Fin 1`
    has `i.val = j.val = 0`, so `i.val < j.val` is never satisfied
    and the outer `if` in each summand returns `0`.  Companion to
    `kendallTau_empty` covering the second trivial-domain case. -/
theorem kendallTau_singleton (a b : QueryOrder 1) : kendallTau a b = 0 :=
  Finset.sum_eq_zero fun i _ =>
    Finset.sum_eq_zero fun j _ =>
      if_neg fun h =>
        Nat.not_lt_zero i.val (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ j.isLt))

/-- *Per-Bool triangle inequality.*  For three Booleans `X`, `Y`, `Z`,
    the indicator of `X ≠ Z` is at most the indicators of `X ≠ Y` plus
    `Y ≠ Z`.  Eight-case Bool enumeration: in each case both LHS and
    RHS reduce to specific `Nat` literals (`0`, `1`, or `2`), and
    `Nat.le_refl` / `Nat.zero_le` closes each. -/
private theorem triangle_pointwise : forall (X Y Z : Bool),
    (if X = Z then (0 : Nat) else 1) ≤
      (if X = Y then 0 else 1) + (if Y = Z then 0 else 1)
  | true,  true,  true  => Nat.le_refl 0
  | true,  true,  false => Nat.le_refl 1
  | true,  false, true  => Nat.zero_le 2
  | true,  false, false => Nat.le_refl 1
  | false, true,  true  => Nat.le_refl 1
  | false, true,  false => Nat.zero_le 2
  | false, false, true  => Nat.le_refl 1
  | false, false, false => Nat.le_refl 0

/-- *Per-summand triangle inequality.*  Lift `triangle_pointwise` to the
    full kendallTau summand (with the outer `if i.val < j.val`
    wrapper).  In the true branch the three outer `if`s collapse via
    `if_pos h` and `triangle_pointwise` closes; in the false branch
    all three reduce to `0` via `if_neg h` and the trivial `0 ≤ 0 + 0`
    closes. -/
private theorem triangle_summand
    {numPatterns : Nat} (a b c : QueryOrder numPatterns) (i j : Fin numPatterns) :
    (if i.val < j.val then
        if decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
            = decide (QueryOrder.positionOf i c < QueryOrder.positionOf j c)
          then (0 : Nat) else 1
      else 0) ≤
      (if i.val < j.val then
          if decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
              = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
            then (0 : Nat) else 1
        else 0) +
        (if i.val < j.val then
            if decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
                = decide (QueryOrder.positionOf i c < QueryOrder.positionOf j c)
              then (0 : Nat) else 1
          else 0) :=
  if h : i.val < j.val then
    let X := decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
    let Y := decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
    let Z := decide (QueryOrder.positionOf i c < QueryOrder.positionOf j c)
    let key : (if X = Z then (0 : Nat) else 1) ≤
              (if X = Y then 0 else 1) + (if Y = Z then 0 else 1) :=
      triangle_pointwise X Y Z
    (if_pos h).symm ▸ (if_pos h).symm ▸ (if_pos h).symm ▸ key
  else
    let h_l :
        (if i.val < j.val then
            if decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
                = decide (QueryOrder.positionOf i c < QueryOrder.positionOf j c)
              then (0 : Nat) else 1
          else 0) = 0 := if_neg h
    let h_r1 :
        (if i.val < j.val then
            if decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
                = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
              then (0 : Nat) else 1
          else 0) = 0 := if_neg h
    let h_r2 :
        (if i.val < j.val then
            if decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
                = decide (QueryOrder.positionOf i c < QueryOrder.positionOf j c)
              then (0 : Nat) else 1
          else 0) = 0 := if_neg h
    Nat.le_of_eq (h_l.trans (congrArg₂ (· + ·) h_r1.symm h_r2.symm))

/-- *Triangle inequality on `kendallTau`.*  For any three query orders
    `a`, `b`, `c`,
    `kendallTau a c ≤ kendallTau a b + kendallTau b c`.

    Sum the per-pair `triangle_summand` over `Finset.univ × Finset.univ`,
    then redistribute the resulting `sum (g + h)` to `sum g + sum h`
    via `Finset.sum_add_distrib` (twice for the two nested sums). -/
theorem kendallTau_triangle
    {numPatterns : Nat} (a b c : QueryOrder numPatterns) :
    kendallTau a c ≤ kendallTau a b + kendallTau b c :=
  let h_inner_le : forall (i : Fin numPatterns),
      Finset.univ.sum (fun j : Fin numPatterns =>
        if i.val < j.val then
          if decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
              = decide (QueryOrder.positionOf i c < QueryOrder.positionOf j c)
            then (0 : Nat) else 1
        else 0) ≤
      Finset.univ.sum (fun j : Fin numPatterns =>
        (if i.val < j.val then
          if decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
              = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
            then (0 : Nat) else 1
        else 0) +
        (if i.val < j.val then
          if decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
              = decide (QueryOrder.positionOf i c < QueryOrder.positionOf j c)
            then (0 : Nat) else 1
        else 0)) :=
    fun i => Finset.sum_le_sum (fun j _ => triangle_summand a b c i j)
  let h_outer_le : kendallTau a c ≤
      Finset.univ.sum (fun i : Fin numPatterns =>
        Finset.univ.sum (fun j : Fin numPatterns =>
          (if i.val < j.val then
            if decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
                = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
              then (0 : Nat) else 1
          else 0) +
          (if i.val < j.val then
            if decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
                = decide (QueryOrder.positionOf i c < QueryOrder.positionOf j c)
              then (0 : Nat) else 1
          else 0))) :=
    Finset.sum_le_sum (fun i _ => h_inner_le i)
  let h_inner_split : forall (i : Fin numPatterns),
      Finset.univ.sum (fun j : Fin numPatterns =>
        (if i.val < j.val then
          if decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
              = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
            then (0 : Nat) else 1
        else 0) +
        (if i.val < j.val then
          if decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
              = decide (QueryOrder.positionOf i c < QueryOrder.positionOf j c)
            then (0 : Nat) else 1
        else 0)) =
      Finset.univ.sum (fun j : Fin numPatterns =>
        if i.val < j.val then
          if decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
              = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
            then (0 : Nat) else 1
        else 0) +
      Finset.univ.sum (fun j : Fin numPatterns =>
        if i.val < j.val then
          if decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
              = decide (QueryOrder.positionOf i c < QueryOrder.positionOf j c)
            then (0 : Nat) else 1
        else 0) :=
    fun _ => Finset.sum_add_distrib
  let h_outer_split :
      Finset.univ.sum (fun i : Fin numPatterns =>
        Finset.univ.sum (fun j : Fin numPatterns =>
          (if i.val < j.val then
            if decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
                = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
              then (0 : Nat) else 1
          else 0) +
          (if i.val < j.val then
            if decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)
                = decide (QueryOrder.positionOf i c < QueryOrder.positionOf j c)
              then (0 : Nat) else 1
          else 0))) =
      kendallTau a b + kendallTau b c :=
    (Finset.sum_congr rfl (fun i _ => h_inner_split i)).trans
      Finset.sum_add_distrib
  h_outer_le.trans h_outer_split.le

/-- *Upper bound by `numPatterns * numPatterns`.*  Sum of at most
    `Finset.univ.card * Finset.univ.card = numPatterns * numPatterns`
    summands each `≤ 1` by `kendallTau_summand_le_one`.

    Term-mode chain:
    * `Finset.sum_le_sum` twice to bound by the constant-1 sum.
    * `Finset.sum_const_nat` to evaluate the inner constant sum to
      `Finset.univ.card * 1 = Finset.univ.card`.
    * `Finset.card_univ.trans (Fintype.card_fin numPatterns)` to
      identify `Finset.univ.card` with `numPatterns`.
    * `Finset.sum_const_nat` again on the outer sum to get
      `Finset.univ.card * numPatterns`.
    * Substitute again via `congrArg`. -/
theorem kendallTau_le_sq
    {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    kendallTau a b ≤ numPatterns * numPatterns :=
  let h_card : (Finset.univ : Finset (Fin numPatterns)).card = numPatterns :=
    Finset.card_univ.trans (Fintype.card_fin numPatterns)
  let h_inner :
      Finset.univ.sum (fun _ : Fin numPatterns => (1 : Nat)) = numPatterns :=
    (Finset.sum_const_nat (fun _ _ => rfl)).trans
      ((Nat.mul_one _).trans h_card)
  let h_outer :
      Finset.univ.sum (fun _ : Fin numPatterns =>
        Finset.univ.sum (fun _ : Fin numPatterns => (1 : Nat)))
        = numPatterns * numPatterns :=
    (Finset.sum_const_nat (fun _ _ => h_inner)).trans
      (congrArg (· * numPatterns) h_card)
  let h_bound : kendallTau a b ≤
      Finset.univ.sum (fun _ : Fin numPatterns =>
        Finset.univ.sum (fun _ : Fin numPatterns => (1 : Nat))) :=
    Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_sum (fun j _ => kendallTau_summand_le_one a b i j))
  h_bound.trans h_outer.le

/-- *Singleton domain upper bound by one.*  At `numPatterns = 1`,
    `kendallTau a b = 0` by `kendallTau_singleton`, hence trivially
    bounded above by `1`. -/
theorem kendallTau_singleton_le_one (a b : QueryOrder 1) :
    kendallTau a b <= 1 :=
  (kendallTau_singleton a b).le.trans (Nat.zero_le 1)

/-- *Empty domain collapses kendallTau to a single value.*  Any two
    pairs of `QueryOrder 0` inputs produce the same `kendallTau`,
    namely `0`. -/
theorem kendallTau_empty_eq (a b c d : QueryOrder 0) :
    kendallTau a b = kendallTau c d :=
  (kendallTau_empty a b).trans (kendallTau_empty c d).symm

/-- *Trivial self-additive bound.*  `kendallTau a b` is bounded
    above by `kendallTau a b + kendallTau b b`, since the second
    summand is zero by `kendallTau_self`. -/
theorem kendallTau_le_self_add {numPatterns : Nat}
    (a b : QueryOrder numPatterns) :
    kendallTau a b <= kendallTau a b + kendallTau b b :=
  (kendallTau_self b).symm ▸ Nat.le_add_right _ _

/-- *Empty domain upper bound by one.*  Companion to
    `kendallTau_singleton_le_one` covering the other trivial-domain
    case. -/
theorem kendallTau_empty_le_one (a b : QueryOrder 0) :
    kendallTau a b <= 1 :=
  (kendallTau_empty a b).le.trans (Nat.zero_le 1)

/-- *Zero-distance is transitive.*  If `kendallTau a b = 0` and
    `kendallTau b c = 0`, then `kendallTau a c = 0`.  Direct
    consequence of `kendallTau_triangle` plus `Nat.le_zero.mp` on
    the resulting bound. -/
theorem kendallTau_eq_zero_trans
    {numPatterns : Nat} (a b c : QueryOrder numPatterns)
    (hab : kendallTau a b = 0) (hbc : kendallTau b c = 0) :
    kendallTau a c = 0 :=
  Nat.le_zero.mp
    ((kendallTau_triangle a b c).trans (hab.symm ▸ hbc.symm ▸ Nat.le_refl 0))

/-- *Zero distance is symmetric.*  If `kendallTau a b = 0` then
    `kendallTau b a = 0`.  Direct transport via `kendallTau_symm`:
    `kendallTau b a = kendallTau a b = 0`.  Companion to
    `kendallTau_eq_zero_trans` (transitivity of zero-distance), giving
    the symmetry leg of the "zero-distance is an equivalence relation"
    package. -/
theorem kendallTau_eq_zero_symm
    {numPatterns : Nat} (a b : QueryOrder numPatterns)
    (h : kendallTau a b = 0) :
    kendallTau b a = 0 :=
  (kendallTau_symm a b).symm.trans h

/-- *Zero distance is symmetric (iff form).*  `kendallTau a b = 0` iff
    `kendallTau b a = 0`.  Packages both directions of
    `kendallTau_eq_zero_symm`. -/
theorem kendallTau_eq_zero_iff_symm
    {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    kendallTau a b = 0 ↔ kendallTau b a = 0 :=
  ⟨kendallTau_eq_zero_symm a b, kendallTau_eq_zero_symm b a⟩

/-- *Non-zero distance is symmetric (iff form).*  `kendallTau a b ≠ 0`
    iff `kendallTau b a ≠ 0`.  Direct negation of
    `kendallTau_eq_zero_iff_symm` via `Iff.not`. -/
theorem kendallTau_ne_zero_iff_symm
    {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    kendallTau a b ≠ 0 ↔ kendallTau b a ≠ 0 :=
  (kendallTau_eq_zero_iff_symm a b).not

/-- *Zero left-distance squeeze.*  If `kendallTau a b = 0`, then for any
    third query order `c`, `kendallTau a c <= kendallTau b c`.  Direct
    consequence of `kendallTau_triangle a b c` rewritten under
    `kendallTau a b = 0`, where the `0 + kendallTau b c` summand
    collapses via `Nat.zero_add`. -/
theorem kendallTau_le_of_eq_zero_left {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) (hab : kendallTau a b = 0) :
    kendallTau a c <= kendallTau b c :=
  let h_tri : kendallTau a c <= kendallTau a b + kendallTau b c :=
    kendallTau_triangle a b c
  let h_collapse : kendallTau a b + kendallTau b c = kendallTau b c :=
    hab ▸ Nat.zero_add _
  h_tri.trans h_collapse.le

/-- *Zero right-distance squeeze.*  If `kendallTau b c = 0`, then for any
    other query order `a`, `kendallTau a c <= kendallTau a b`.
    Right-anchored companion to `kendallTau_le_of_eq_zero_left`. -/
theorem kendallTau_le_of_eq_zero_right {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) (hbc : kendallTau b c = 0) :
    kendallTau a c <= kendallTau a b :=
  let h_tri : kendallTau a c <= kendallTau a b + kendallTau b c :=
    kendallTau_triangle a b c
  let h_collapse : kendallTau a b + kendallTau b c = kendallTau a b :=
    hbc ▸ Nat.add_zero _
  h_tri.trans h_collapse.le

/-- *Zero left-distance forces equality of right-distances.*  If
    `kendallTau a b = 0`, then for any third query order `c`,
    `kendallTau a c = kendallTau b c`.  Strengthens
    `kendallTau_le_of_eq_zero_left` from `<=` to `=` via
    `Nat.le_antisymm` applied to both directions. -/
theorem kendallTau_eq_of_eq_zero_left {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) (hab : kendallTau a b = 0) :
    kendallTau a c = kendallTau b c :=
  let hba : kendallTau b a = 0 := kendallTau_eq_zero_symm a b hab
  let h_le : kendallTau a c <= kendallTau b c :=
    kendallTau_le_of_eq_zero_left a b c hab
  let h_ge : kendallTau b c <= kendallTau a c :=
    kendallTau_le_of_eq_zero_left b a c hba
  Nat.le_antisymm h_le h_ge

/-- *Zero right-distance forces equality of left-distances.*  If
    `kendallTau b c = 0`, then for any other query order `a`,
    `kendallTau a c = kendallTau a b`.  Right-anchored companion to
    `kendallTau_eq_of_eq_zero_left`. -/
theorem kendallTau_eq_of_eq_zero_right {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) (hbc : kendallTau b c = 0) :
    kendallTau a c = kendallTau a b :=
  let hcb : kendallTau c b = 0 := kendallTau_eq_zero_symm b c hbc
  let h_le : kendallTau a c <= kendallTau a b :=
    kendallTau_le_of_eq_zero_right a b c hbc
  let h_ge : kendallTau a b <= kendallTau a c :=
    kendallTau_le_of_eq_zero_right a c b hcb
  Nat.le_antisymm h_le h_ge

/-- *Zero left-distance forces equality of left-anchored distances.*  If
    `kendallTau a b = 0`, then for any third query order `c`,
    `kendallTau c a = kendallTau c b`.  Symm-anchored companion to
    `kendallTau_eq_of_eq_zero_left`: the original fixes `c` on the right
    of each side, whereas this fixes `c` on the left of each side. -/
theorem kendallTau_eq_of_eq_zero_symm {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) (hab : kendallTau a b = 0) :
    kendallTau c a = kendallTau c b :=
  (kendallTau_symm c a).trans
    ((kendallTau_eq_of_eq_zero_left a b c hab).trans
      (kendallTau_symm b c))

/-- *Zero right-distance forces equality of right-anchored distances.*  If
    `kendallTau b c = 0`, then for any other query order `a`,
    `kendallTau c a = kendallTau b a`.  Right-anchored companion to
    `kendallTau_eq_of_eq_zero_symm`. -/
theorem kendallTau_eq_of_eq_zero_symm_right {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) (hbc : kendallTau b c = 0) :
    kendallTau c a = kendallTau b a :=
  (kendallTau_symm c a).trans
    ((kendallTau_eq_of_eq_zero_right a b c hbc).trans
      (kendallTau_symm a b))

/-- *Zero left-distance propagates strict upper bounds.*  If
    `kendallTau a b = 0` and `kendallTau a c < n`, then
    `kendallTau b c < n`.  Strict-inequality companion to
    `kendallTau_le_of_eq_zero_left`. -/
theorem kendallTau_lt_of_lt_of_eq_zero_left {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hab : kendallTau a b = 0) (hac : kendallTau a c < n) :
    kendallTau b c < n :=
  (kendallTau_eq_of_eq_zero_left a b c hab) ▸ hac

/-- *Zero right-distance propagates strict upper bounds.*  If
    `kendallTau b c = 0` and `kendallTau a b < n`, then
    `kendallTau a c < n`.  Right-anchored companion to
    `kendallTau_lt_of_lt_of_eq_zero_left`. -/
theorem kendallTau_lt_of_lt_of_eq_zero_right {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hbc : kendallTau b c = 0) (hab : kendallTau a b < n) :
    kendallTau a c < n :=
  (kendallTau_eq_of_eq_zero_right a b c hbc).symm ▸ hab

/-- *Zero left-distance gives an iff for strict upper bounds.*  If
    `kendallTau a b = 0`, then for any third query order `c` and any
    bound `n`, `kendallTau a c < n` iff `kendallTau b c < n`.
    Iff-shape strengthening of `kendallTau_lt_of_lt_of_eq_zero_left`. -/
theorem kendallTau_lt_iff_lt_of_eq_zero_left {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hab : kendallTau a b = 0) :
    kendallTau a c < n ↔ kendallTau b c < n :=
  iff_of_eq (congrArg (· < n) (kendallTau_eq_of_eq_zero_left a b c hab))

/-- *Zero right-distance gives an iff for strict upper bounds.*  If
    `kendallTau b c = 0`, then for any other query order `a` and any
    bound `n`, `kendallTau a b < n` iff `kendallTau a c < n`.
    Right-anchored iff companion to `kendallTau_lt_iff_lt_of_eq_zero_left`. -/
theorem kendallTau_lt_iff_lt_of_eq_zero_right {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hbc : kendallTau b c = 0) :
    kendallTau a b < n ↔ kendallTau a c < n :=
  iff_of_eq (congrArg (· < n) (kendallTau_eq_of_eq_zero_right a b c hbc).symm)

/-- *Zero left-distance gives an iff for weak upper bounds.*  If
    `kendallTau a b = 0`, then for any third query order `c` and any
    bound `n`, `kendallTau a c <= n` iff `kendallTau b c <= n`.
    Weak-inequality companion to `kendallTau_lt_iff_lt_of_eq_zero_left`. -/
theorem kendallTau_le_iff_le_of_eq_zero_left {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hab : kendallTau a b = 0) :
    kendallTau a c <= n ↔ kendallTau b c <= n :=
  iff_of_eq (congrArg (· <= n) (kendallTau_eq_of_eq_zero_left a b c hab))

/-- *Zero right-distance gives an iff for weak upper bounds.*  If
    `kendallTau b c = 0`, then for any other query order `a` and any
    bound `n`, `kendallTau a b <= n` iff `kendallTau a c <= n`.
    Right-anchored weak-inequality companion. -/
theorem kendallTau_le_iff_le_of_eq_zero_right {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hbc : kendallTau b c = 0) :
    kendallTau a b <= n ↔ kendallTau a c <= n :=
  iff_of_eq (congrArg (· <= n) (kendallTau_eq_of_eq_zero_right a b c hbc).symm)

/-- *Zero left-distance gives an iff for strict upper bounds (symm-anchored).*
    If `kendallTau a b = 0`, then for any third query order `c` and any
    bound `n`, `kendallTau c a < n` iff `kendallTau c b < n`.  Symm-anchored
    iff companion to `kendallTau_lt_iff_lt_of_eq_zero_left`. -/
theorem kendallTau_lt_iff_lt_of_eq_zero_symm {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hab : kendallTau a b = 0) :
    kendallTau c a < n ↔ kendallTau c b < n :=
  iff_of_eq (congrArg (· < n) (kendallTau_eq_of_eq_zero_symm a b c hab))

/-- *Zero left-distance gives an iff for weak upper bounds (symm-anchored).*
    If `kendallTau a b = 0`, then for any third query order `c` and any
    bound `n`, `kendallTau c a <= n` iff `kendallTau c b <= n`.
    Weak-inequality companion to `kendallTau_lt_iff_lt_of_eq_zero_symm`. -/
theorem kendallTau_le_iff_le_of_eq_zero_symm {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hab : kendallTau a b = 0) :
    kendallTau c a <= n ↔ kendallTau c b <= n :=
  iff_of_eq (congrArg (· <= n) (kendallTau_eq_of_eq_zero_symm a b c hab))

/-- *Triangle inequality, right-symmetrized form.*  For any three query
    orders `a`, `b`, `c`,
    `kendallTau a c <= kendallTau a b + kendallTau c b`.
    Direct corollary of `kendallTau_triangle` (with middle witness `b`)
    composed with `kendallTau_symm` on the second summand to flip
    `kendallTau b c` into `kendallTau c b`.  Useful when the caller has
    a bound on `kendallTau c b` rather than `kendallTau b c`. -/
theorem kendallTau_triangle_right_symm
    {numPatterns : Nat} (a b c : QueryOrder numPatterns) :
    kendallTau a c ≤ kendallTau a b + kendallTau c b :=
  (kendallTau_symm c b) ▸ kendallTau_triangle a b c

/-- *Triangle inequality, left-symmetrized form.*  For any three query
    orders `a`, `b`, `c`,
    `kendallTau a c <= kendallTau b a + kendallTau b c`.
    Direct corollary of `kendallTau_triangle` (with middle witness `b`)
    composed with `kendallTau_symm` on the first summand to flip
    `kendallTau a b` into `kendallTau b a`.  Useful when the caller has
    a bound on `kendallTau b a` rather than `kendallTau a b`.  Companion
    to `kendallTau_triangle_right_symm`. -/
theorem kendallTau_triangle_left_symm
    {numPatterns : Nat} (a b c : QueryOrder numPatterns) :
    kendallTau a c ≤ kendallTau b a + kendallTau b c :=
  (kendallTau_symm a b) ▸ kendallTau_triangle a b c

/-- *Triangle inequality, both-symmetrized form.*  For any three query
    orders `a`, `b`, `c`,
    `kendallTau a c <= kendallTau b a + kendallTau c b`.
    Direct corollary of `kendallTau_triangle` (with middle witness `b`)
    composed with `kendallTau_symm` on BOTH summands.  Useful when the
    caller has bounds on `kendallTau b a` and `kendallTau c b` rather
    than the canonical-direction forms.  Companion to
    `kendallTau_triangle_left_symm` and `kendallTau_triangle_right_symm`. -/
theorem kendallTau_triangle_both_symm
    {numPatterns : Nat} (a b c : QueryOrder numPatterns) :
    kendallTau a c ≤ kendallTau b a + kendallTau c b :=
  (kendallTau_symm a b) ▸ (kendallTau_symm c b) ▸ kendallTau_triangle a b c


/-! ## Query-order stability claim (placeholder) -/

/-- *Stability of the ORBGRAND-AI query order under correlation
    perturbation.*

    There exists a modulus `K` such that, for all
    `|delta_rho| <= 0.2`, the Kendall-tau distance between the query
    order computed under `rho_real` and the query order computed
    under `rho_real + delta_rho` satisfies

      `kendallTau (queryOrder rho_real) (queryOrder (rho_real + delta_rho))
        <= K * |delta_rho|`.

    *Refactored shape (was: vacuous quantification over arbitrary
    `orderReal`, `orderEst`).*  The new shape parameterises the
    Lipschitz claim by an abstract
    `queryOrder : Real -> QueryOrder numPatterns` function (the
    Lipschitz constant `K` is universally quantified along with the
    `queryOrder` family).  Once a concrete `queryOrder` derived from
    ORBGRAND-AI's per-block posterior is wired up, this theorem will
    specialise into the actual stability claim from the paper.

    The closing `True` is retained as a deferred-proof marker; the
    body is now a *proper* Lipschitz claim on the de-opaqued
    `kendallTau` rather than a quantification over unrelated query
    orders. -/
theorem query_order_stability_statement
    (rho_real : CorrelationCoefficient) (numPatterns : Nat) :
    (forall (queryOrder : Real -> QueryOrder numPatterns),
      exists (K : Real), 0 < K /\
        forall (delta_rho : Real),
          abs delta_rho <= 0.2 ->
            (kendallTau (queryOrder rho_real.val)
                        (queryOrder (rho_real.val + delta_rho)) : Real)
              <= K * abs delta_rho)
      -> True := by
  kan_intro _h
  kan_constructor

/-- *Zero right-distance gives an iff for weak upper bounds (symm-right-anchored).*
    If `kendallTau b c = 0`, then for any other query order `a` and any
    bound `n`, `kendallTau c a <= n` iff `kendallTau b a <= n`.
    Right-anchored weak-inequality companion to
    `kendallTau_le_iff_le_of_eq_zero_symm`. -/
theorem kendallTau_le_iff_le_of_eq_zero_symm_right {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hbc : kendallTau b c = 0) :
    kendallTau c a <= n ↔ kendallTau b a <= n :=
  iff_of_eq (congrArg (· <= n) (kendallTau_eq_of_eq_zero_symm_right a b c hbc))

/-- *Zero right-distance gives an iff for strict upper bounds (symm-right-anchored).*
    If `kendallTau b c = 0`, then for any other query order `a` and any
    bound `n`, `kendallTau c a < n` iff `kendallTau b a < n`.
    Right-anchored strict-inequality companion to
    `kendallTau_lt_iff_lt_of_eq_zero_symm`. -/
theorem kendallTau_lt_iff_lt_of_eq_zero_symm_right {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hbc : kendallTau b c = 0) :
    kendallTau c a < n ↔ kendallTau b a < n :=
  iff_of_eq (congrArg (· < n) (kendallTau_eq_of_eq_zero_symm_right a b c hbc))

/-- *Zero right-distance gives an iff for exact values (symm-right-anchored).*
    If `kendallTau b c = 0`, then for any other query order `a` and any
    value `n`, `kendallTau c a = n` iff `kendallTau b a = n`.
    Equality companion to `kendallTau_lt_iff_lt_of_eq_zero_symm_right`. -/
theorem kendallTau_eq_iff_eq_of_eq_zero_symm_right {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hbc : kendallTau b c = 0) :
    kendallTau c a = n ↔ kendallTau b a = n :=
  iff_of_eq (congrArg (· = n) (kendallTau_eq_of_eq_zero_symm_right a b c hbc))

/-- *Zero left-distance gives an iff for exact values (symm-anchored).*
    If `kendallTau a b = 0`, then for any third query order `c` and any
    value `n`, `kendallTau c a = n` iff `kendallTau c b = n`.  Equality
    companion to `kendallTau_lt_iff_lt_of_eq_zero_symm`. -/
theorem kendallTau_eq_iff_eq_of_eq_zero_symm {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hab : kendallTau a b = 0) :
    kendallTau c a = n ↔ kendallTau c b = n :=
  iff_of_eq (congrArg (· = n) (kendallTau_eq_of_eq_zero_symm a b c hab))

/-- *Zero left-distance gives an iff for exact values (left-anchored).*
    If `kendallTau a b = 0`, then for any third query order `c` and any
    value `n`, `kendallTau a c = n` iff `kendallTau b c = n`.  Equality
    companion to `kendallTau_le_iff_le_of_eq_zero_left`. -/
theorem kendallTau_eq_iff_eq_of_eq_zero_left {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hab : kendallTau a b = 0) :
    kendallTau a c = n ↔ kendallTau b c = n :=
  iff_of_eq (congrArg (· = n) (kendallTau_eq_of_eq_zero_left a b c hab))

/-- *Zero right-distance gives an iff for exact values (right-anchored).*
    If `kendallTau b c = 0`, then for any other query order `a` and any
    value `n`, `kendallTau a b = n` iff `kendallTau a c = n`.
    Right-anchored equality companion to
    `kendallTau_eq_iff_eq_of_eq_zero_left`. -/
theorem kendallTau_eq_iff_eq_of_eq_zero_right {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hbc : kendallTau b c = 0) :
    kendallTau a b = n ↔ kendallTau a c = n :=
  iff_of_eq (congrArg (· = n) (kendallTau_eq_of_eq_zero_right a b c hbc).symm)


/-- *Zero right-distance gives an iff for exact values (symm-left-anchored).*
    If `kendallTau b c = 0`, then for any other query order `a` and any
    value `n`, `kendallTau b a = n` iff `kendallTau c a = n`.  Left-flipped
    equality companion to `kendallTau_eq_iff_eq_of_eq_zero_symm_right`. -/
theorem kendallTau_eq_iff_eq_of_eq_zero_symm_left {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hbc : kendallTau b c = 0) :
    kendallTau b a = n ↔ kendallTau c a = n :=
  iff_of_eq (congrArg (· = n) (kendallTau_eq_of_eq_zero_symm_right a b c hbc).symm)

/-- *Zero right-distance gives an iff for weak upper bounds (symm-left-anchored).*
    If `kendallTau b c = 0`, then for any other query order `a` and any
    bound `n`, `kendallTau b a <= n` iff `kendallTau c a <= n`.  Left-flipped
    weak-inequality companion to `kendallTau_le_iff_le_of_eq_zero_symm_right`. -/
theorem kendallTau_le_iff_le_of_eq_zero_symm_left {numPatterns : Nat}
    (a b c : QueryOrder numPatterns) {n : Nat}
    (hbc : kendallTau b c = 0) :
    kendallTau b a <= n ↔ kendallTau c a <= n :=
  iff_of_eq (congrArg (· <= n) (kendallTau_eq_of_eq_zero_symm_right a b c hbc).symm)

end Section06
end OrbgrandAi
