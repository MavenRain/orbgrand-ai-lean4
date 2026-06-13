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


/-! ## Query-order stability claim (placeholder) -/

/-- *Stability of the ORBGRAND-AI query order under correlation
    perturbation.*

    There exists a modulus `K` such that, for all
    `|delta_rho| <= epsilon`, the Kendall tau distance between the
    query order computed under `rho_real` and the query order
    computed under `rho_real + delta_rho` satisfies

      `kendallTau order(rho_real) order(rho_real + delta_rho) <= K * epsilon`.

    *Placeholder shape.*  The constant `K` depends polynomially on
    `n_s`, `b`, and the constellation size. -/
theorem query_order_stability_statement
    (rho_real : CorrelationCoefficient) (numPatterns : Nat) :
    (exists (K : Real), 0 < K /\
        forall (delta_rho : Real),
          abs delta_rho <= 0.2 ->
            forall (orderReal orderEst : QueryOrder numPatterns),
              (kendallTau orderReal orderEst : Real) <= K * abs delta_rho)
      -> True := by
  kan_intro _h
  kan_constructor

end Section06
end OrbgrandAi
