import Mathlib.Data.Real.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.MinMax
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section04.Grand
import OrbgrandAi.Section04.Orbgrand
import KanTactics

/-!
# Section IV.D.  ORBGRAND-AI

Formalizes Algorithm 1 of the paper.

## Block factorisation

For block length `n_s` and neighbourhood size `b` with `b | n_s`, the
received vector is partitioned into non-overlapping blocks:

  Y^{n_s}
    = (Y^b_1, Y^b_2, ..., Y^b_{n_s / b}).

For each block index `i in {1, ..., n_s / b}`, the per-block
posterior

  p_{X^b | Y^b}(t^b_i | Y^b_i) for each t^b_i in chi^b

is computed using the channel model and CSI `Psi`.  Let `t^{b,*}_i`
denote the hard-decision per-block argmax.

The *approximate independence* assumption replaces the joint
posterior with the product

  p_{X^{n_s} | Y^{n_s}}(t^{n_s} | Y^{n_s})
    ~= prod_{i = 1}^{n_s / b}
        p_{X^b | Y^b}(t^b_i | Y^b_i)
        / p_{X^b | Y^b}(t^{b,*}_i | Y^b_i).        (eq. 3)

After taking logs and dropping the constant numerator term, this
becomes a sum of *substitution penalties*

  w^mu_i = - log( p_{X^b | Y^b}(t^b_i | Y^b_i)
                 / p_{X^b | Y^b}(t^{b,*}_i | Y^b_i) ).

The ORBGRAND pattern generator (`Section04.Orbgrand`) then walks
candidate `mu`-vectors in increasing total penalty
`sum_i w^mu_i`.

## Algorithm 1

```
Inputs: Y^{n_s}, Phi (membership oracle), tau' (abandonment budget),
        Psi (channel statistics).
Output: c^{n_s,*} or FAILURE.

  d' := 0
  Compute w^mu (substitution-block likelihoods).
  while d' < tau':
    d' := d' + 1
    e^mu := next-most-likely ORBGRAND pattern for w^mu
    if e^mu has no substitution conflict:
      s^{n_s} := substitute blocks per e^mu
      c^n := demodulate s^{n_s}
      if Phi(c^n) == 1:
        return c^{n_s,*} = c^n
  return FAILURE
```

This file:

* Defines the per-block hard-decision argmax and the substitution
  penalty.
* Defines the substitution operator that turns an `e^mu` pattern
  into a substituted symbol vector.
* Defines the codebook-membership oracle as a `Bool`-valued
  function (mirroring the paper's `Phi : C^n -> {0, 1}`).
* Defines the abandonment threshold `tau' : N`.
* States Algorithm 1 as a recursive Lean function `orbgrandAi`
  consuming a (precomputed) pattern enumeration.
* States the *no-false-positive* property (any non-`FAILURE`
  return value passes the membership oracle) as a definitionally
  provable theorem.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section04

open OrbgrandAi.Section02

/-! ## Per-block hard decision and substitution penalty -/

/-- A per-block posterior table indexed by candidate `t^b in chi^b`,
    where `chi^b` is the alphabet of `b`-blocks.  We model
    `chi^b = Fin numCandidates` to keep things finite. -/
abbrev BlockPosterior (numCandidates : Nat) := Fin numCandidates -> Real

/-- The hard-decision block argmax `t^{b,*}` is the candidate index
    achieving maximal posterior in `Fin numCandidates`.  Returns
    `Option (Fin numCandidates)`; `none` exactly when
    `numCandidates = 0` (since `List.finRange 0 = []` and
    `List.argmax _ [] = none`).

    Concrete: enumerate `Fin numCandidates` via `List.finRange`, then
    `List.argmax post`.  Tie-breaking matches `List.argmax`: when
    multiple indices share the maximal posterior, the *earliest*
    one in `List.finRange numCandidates` order (i.e., the smallest
    `Fin numCandidates`) is returned.

    Marked `noncomputable` because `Real`'s order is classical. -/
noncomputable def hardDecisionBlock?
    {numCandidates : Nat} (post : BlockPosterior numCandidates) :
    Option (Fin numCandidates) :=
  (List.finRange numCandidates).argmax post

/-- *Empty candidate set yields `none`.*  At `numCandidates = 0`,
    `List.finRange 0 = []` and `List.argmax _ [] = none`. -/
theorem hardDecisionBlock?_empty
    (post : BlockPosterior 0) : hardDecisionBlock? post = none := rfl

/-- *Body unfold.*  `hardDecisionBlock? post` is exactly
    `(List.finRange numCandidates).argmax post`. -/
theorem hardDecisionBlock?_eq
    {numCandidates : Nat} (post : BlockPosterior numCandidates) :
    hardDecisionBlock? post = (List.finRange numCandidates).argmax post := rfl

/-- *Reverse definitional bridge for the hard-decision argmax.*  The
    raw `List.argmax post` over `List.finRange numCandidates` is
    exactly `hardDecisionBlock? post`.  Useful when rewriting an
    `argmax` expression into the named ORBGRAND-AI form.  Reverse
    direction of `hardDecisionBlock?_eq`. -/
theorem argmax_eq_hardDecisionBlock?
    {numCandidates : Nat} (post : BlockPosterior numCandidates) :
    (List.finRange numCandidates).argmax post = hardDecisionBlock? post :=
  (hardDecisionBlock?_eq post).symm

/-- The per-block substitution penalty

      w_i(t) = - log( p(t | Y_i) / p(t* | Y_i) )
             = log p(t* | Y_i) - log p(t | Y_i)

    where `t* = hardDecisionBlock? post`.  Returns `none` when the
    candidate set is empty. -/
noncomputable def substitutionPenalty?
    {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates) : Option Real :=
  hardDecisionBlock? post |>.map fun tStar =>
    Real.log (post tStar) - Real.log (post t)

/-- *Body unfold.*  `substitutionPenalty? post t` is the
    `hardDecisionBlock?`-keyed log-ratio penalty.  Definitional. -/
theorem substitutionPenalty?_eq
    {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates) :
    substitutionPenalty? post t
      = (hardDecisionBlock? post).map
          (fun tStar => Real.log (post tStar) - Real.log (post t)) := rfl

/-- *Empty candidate set yields `none`.*  At `numCandidates = 0`,
    `hardDecisionBlock? post = none` and `none.map _ = none`, so
    the penalty is `none`.  Definitional. -/
theorem substitutionPenalty?_empty
    (post : BlockPosterior 0) (t : Fin 0) :
    substitutionPenalty? post t = none := rfl

/-- *Raw-`argmax` unfold of the substitution penalty.*  Chains
    `substitutionPenalty?_eq` with `hardDecisionBlock?_eq` to
    express the penalty directly in terms of `List.argmax`. -/
theorem substitutionPenalty?_eq_argmax_map
    {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates) :
    substitutionPenalty? post t
      = ((List.finRange numCandidates).argmax post).map
          (fun tStar => Real.log (post tStar) - Real.log (post t)) :=
  rfl

/-- *Definedness bridge for the substitution penalty.*  The
    penalty is `some _` exactly when the hard-decision argmax is
    `some _`, because the penalty is `Option.map` over the
    hard-decision and `isSome` is preserved by `map`. -/
theorem substitutionPenalty?_isSome_iff_hardDecisionBlock?_isSome
    {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates) :
    (substitutionPenalty? post t).isSome
      = (hardDecisionBlock? post).isSome :=
  Option.isSome_map

/-- *Undefinedness bridge for the substitution penalty.*  Dual of
    the `isSome` form via `Option.isNone_map`. -/
theorem substitutionPenalty?_isNone_iff_hardDecisionBlock?_isNone
    {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates) :
    (substitutionPenalty? post t).isNone
      = (hardDecisionBlock? post).isNone :=
  Option.isNone_map

/-- *Forward direction of the definedness bridge.*  If the
    hard-decision argmax is defined, so is the substitution penalty. -/
theorem substitutionPenalty?_isSome_of_hardDecisionBlock?_isSome
    {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates)
    (h : (hardDecisionBlock? post).isSome = true) :
    (substitutionPenalty? post t).isSome = true :=
  (substitutionPenalty?_isSome_iff_hardDecisionBlock?_isSome post t).trans h

/-- *Forward direction of the undefinedness bridge.*  If the
    hard-decision argmax is undefined, so is the substitution penalty. -/
theorem substitutionPenalty?_isNone_of_hardDecisionBlock?_isNone
    {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates)
    (h : (hardDecisionBlock? post).isNone = true) :
    (substitutionPenalty? post t).isNone = true :=
  (substitutionPenalty?_isNone_iff_hardDecisionBlock?_isNone post t).trans h

/-! ## Codebook membership and abandonment -/

/-- The codebook-membership oracle `Phi : Codeword n -> Bool`. -/
abbrev CodebookMembership (n : Nat) := Codeword n -> Bool

/-- The abandonment-threshold budget `tau'`. -/
structure AbandonmentBudget where
  /-- The budget value `tau'`. -/
  toNat : Nat
deriving Repr

/-! ## Substitution operator (abstract) -/

/-- The substitution operator: takes an ORBGRAND-AI pattern
    `e^mu : Fin (n_s / b) -> Fin numCandidates` (which candidate to
    swap into block `i`) and produces the substituted symbol
    vector.  Concrete instances depend on the modulation; here we
    expose the signature as opaque. -/
opaque substitute
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (e : Fin (n_s / b) -> Fin numCandidates) :
    Codeword n_s

/-- A pattern `e^mu` has *no substitution conflict* if it does not
    propose two simultaneous swaps that target the same underlying
    symbol.  For symbol-level patterns this is a no-op; for
    bit-level patterns it filters duplicate proposals.

    *Placeholder shape.*  The concrete predicate depends on the
    modulation. -/
opaque noSubstitutionConflict
    {n_s b numCandidates : Nat}
    (e : Fin (n_s / b) -> Fin numCandidates) : Bool

/-! ## Algorithm 1 -/

/-- The inner search loop of Algorithm 1, lifted to a top-level
    declaration so that soundness can be proved by structural
    induction on the pattern list. -/
def orbgrandAiLoop
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (Phi : CodebookMembership n_s)
    (steps_remaining : Nat) :
    List (Fin (n_s / b) -> Fin numCandidates) -> Option (Codeword n_s)
  | []        => none
  | (e :: rest) =>
      match steps_remaining with
      | 0      => none
      | (m + 1) =>
          if noSubstitutionConflict e then
            let c := substitute Y e
            if Phi c then some c
            else orbgrandAiLoop Y Phi m rest
          else
            orbgrandAiLoop Y Phi m rest

/-- ORBGRAND-AI Algorithm 1.

    Iterates through the precomputed pattern enumeration
    `patterns : List (Fin (n_s / b) -> Fin numCandidates)`, applies
    the substitution operator, and returns the first substituted
    codeword that satisfies the membership oracle `Phi`.  Aborts
    after `budget` iterations.

    Returns `Option (Codeword n_s)`; `none` represents the
    "FAILURE" branch of Algorithm 1. -/
def orbgrandAi
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    Option (Codeword n_s) :=
  orbgrandAiLoop Y Phi budget.toNat patterns

/-! ## No-false-positive (soundness of the accept gate) -/

/-- The inner loop is sound: if it ever returns `some c`, then
    `Phi c = true`.  Structural recursion on the pattern list with
    case on `steps_remaining` and the two `if` discriminants.

    By taking `Y Phi c` as universally quantified arguments AFTER the
    colon rather than as bound parameters BEFORE the colon, the
    recursive call matches all six pattern slots cleanly, which
    avoids the elaborator's confusion over which binders are
    explicit. -/
theorem orbgrandAiLoop_accept_sound
    {n_s b numCandidates : Nat} :
    forall (Y : Codeword n_s) (Phi : CodebookMembership n_s)
      (c : Codeword n_s) (steps : Nat)
      (patterns : List (Fin (n_s / b) -> Fin numCandidates)),
      orbgrandAiLoop Y Phi steps patterns = some c -> Phi c = true
  | _, _,   _, 0,     [],            h => nomatch h
  | _, _,   _, _ + 1, [],            h => nomatch h
  | _, _,   _, 0,     _ :: _,        h => nomatch h
  | Y, Phi, c, m + 1, e :: rest,     h =>
      -- Definitional unfolding of `orbgrandAiLoop` gives us
      --   h : (if hnc : noSubstitutionConflict e then
      --          (if Phi (substitute Y e) then some (substitute Y e)
      --            else orbgrandAiLoop Y Phi m rest)
      --          else orbgrandAiLoop Y Phi m rest)
      --       = some c
      let hdite : (if hnc : noSubstitutionConflict e then
                    (if Phi (substitute Y e) then some (substitute Y e)
                      else orbgrandAiLoop Y Phi m rest)
                    else orbgrandAiLoop Y Phi m rest)
                  = some c := h
      if hnc : noSubstitutionConflict e then
        let hif : (if Phi (substitute Y e) then some (substitute Y e)
                    else orbgrandAiLoop Y Phi m rest)
                  = some c :=
          (dif_pos hnc).symm.trans hdite
        if hp : Phi (substitute Y e) then
          let hsome : some (substitute Y e) = some c :=
            (if_pos hp).symm.trans hif
          let heq : substitute Y e = c := Option.some.inj hsome
          heq ▸ hp
        else
          let hloop : orbgrandAiLoop Y Phi m rest = some c :=
            (if_neg hp).symm.trans hif
          orbgrandAiLoop_accept_sound Y Phi c m rest hloop
      else
        let hloop : orbgrandAiLoop Y Phi m rest = some c :=
          (dif_neg hnc).symm.trans hdite
        orbgrandAiLoop_accept_sound Y Phi c m rest hloop

/-- *Soundness of ORBGRAND-AI's accept gate.*

    If `orbgrandAi` returns `some c`, then `Phi c = true`. -/
theorem orbgrandAi_accept_sound
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (c : Codeword n_s)
    (h : orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi budget patterns = some c) :
    Phi c = true :=
  orbgrandAiLoop_accept_sound Y Phi c budget.toNat patterns h

/-! ## Cons-case decomposition -/

/-- *Cons case, conflict branch.*  When the head pattern has a
    substitution conflict, the loop discards it and recurses (one
    step is consumed from the budget). -/
theorem orbgrandAiLoop_cons_conflict
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (h : ¬ noSubstitutionConflict e) :
    orbgrandAiLoop Y Phi (m + 1) (e :: rest)
      = orbgrandAiLoop Y Phi m rest :=
  dif_neg h

/-- *Cons case, accept branch.*  When the head pattern has no
    conflict and the substituted codeword is accepted by `Phi`, the
    loop returns it immediately without consuming further steps. -/
theorem orbgrandAiLoop_cons_accept
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (hnc : noSubstitutionConflict e)
    (hp : Phi (substitute Y e)) :
    orbgrandAiLoop Y Phi (m + 1) (e :: rest)
      = some (substitute Y e) :=
  (dif_pos hnc).trans (if_pos hp)

/-- *Cons case, reject branch.*  When the head pattern has no
    conflict but the substituted codeword is rejected by `Phi`, the
    loop recurses (one step is consumed). -/
theorem orbgrandAiLoop_cons_reject
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (hnc : noSubstitutionConflict e)
    (hp : ¬ Phi (substitute Y e)) :
    orbgrandAiLoop Y Phi (m + 1) (e :: rest)
      = orbgrandAiLoop Y Phi m rest :=
  (dif_pos hnc).trans (if_neg hp)

/-! ## Boundary-case behaviour of the loop -/

/-- *Zero remaining steps on a non-empty list.*  The loop returns
    `none` immediately when its abandonment budget is exhausted,
    regardless of what patterns are still pending.  Matches the inner
    `match steps_remaining with | 0 => none` branch by `rfl`. -/
theorem orbgrandAiLoop_zero_steps_cons
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAiLoop Y Phi 0 (e :: rest) = none := rfl

/-- *Empty pattern list.*  With no patterns to try, the loop returns
    `none` regardless of the remaining step count. -/
theorem orbgrandAiLoop_nil
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) :
    forall (steps : Nat),
      orbgrandAiLoop (b := b) (numCandidates := numCandidates)
        Y Phi steps [] = none
  | 0     => rfl
  | _ + 1 => rfl

/-- *Exhausted step budget.*  With zero remaining steps, the loop
    returns `none` regardless of the pattern list. -/
theorem orbgrandAiLoop_zero_steps
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) :
    forall (patterns : List (Fin (n_s / b) -> Fin numCandidates)),
      orbgrandAiLoop Y Phi 0 patterns = none
  | []     => rfl
  | _ :: _ => rfl

/-- *Empty pattern list at the top level.*  Wrapper around
    `orbgrandAiLoop_nil` for the public `orbgrandAi` entry point. -/
theorem orbgrandAi_empty_patterns
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget [] = none :=
  orbgrandAiLoop_nil Y Phi budget.toNat

/-- *Zero budget at the top level.*  Wrapper around
    `orbgrandAiLoop_zero_steps` for the public `orbgrandAi` entry
    point. -/
theorem orbgrandAi_zero_budget
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi ⟨0⟩ patterns = none :=
  orbgrandAiLoop_zero_steps Y Phi patterns

/-- *Vacuous codebook.*  If the membership oracle rejects every
    codeword (`Phi = fun _ => false`), then the loop never accepts and
    always returns `none`.  Structural recursion on (steps, patterns)
    with a case split on `noSubstitutionConflict e` and the
    definitional reduction `(fun _ => false) c = false` on the inner
    branch. -/
theorem orbgrandAiLoop_empty_codebook
    {n_s b numCandidates : Nat} :
    forall (Y : Codeword n_s) (steps : Nat)
      (patterns : List (Fin (n_s / b) -> Fin numCandidates)),
      orbgrandAiLoop Y (fun _ => false) steps patterns = none
  | _, 0,     []        => rfl
  | _, _ + 1, []        => rfl
  | _, 0,     _ :: _    => rfl
  | Y, m + 1, e :: rest =>
      let ih : orbgrandAiLoop Y (fun _ => false) m rest = none :=
        orbgrandAiLoop_empty_codebook Y m rest
      if hnc : noSubstitutionConflict e then
        let then_branch_eq_none :
            (if (fun _ : Codeword n_s => false) (substitute Y e)
              then some (substitute Y e)
              else orbgrandAiLoop Y (fun _ => false) m rest)
            = none := ih
        (dif_pos hnc).trans then_branch_eq_none
      else
        (dif_neg hnc).trans ih

/-- *Vacuous codebook at the top level.*  Wrapper of
    `orbgrandAiLoop_empty_codebook` for the public `orbgrandAi` entry
    point. -/
theorem orbgrandAi_empty_codebook
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) budget patterns = none :=
  orbgrandAiLoop_empty_codebook Y budget.toNat patterns

/-- *Vacuous codebook on an empty pattern list.*  Degenerate corner:
    the codebook rejects everything and there are no patterns to
    try; the decoder returns `none`.  Specialises
    `orbgrandAi_empty_codebook` at the empty pattern list. -/
theorem orbgrandAi_empty_codebook_nil
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (budget : AbandonmentBudget) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) budget [] = none :=
  orbgrandAi_empty_codebook Y budget []

/-- *Vacuous codebook on a non-empty pattern list.*  Degenerate
    corner: the codebook rejects every codeword, so no candidate
    pattern can ever be accepted, and the decoder returns `none`
    regardless of budget or pattern head/tail.  Specialises
    `orbgrandAi_empty_codebook` at a `cons`. -/
theorem orbgrandAi_empty_codebook_cons
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (budget : AbandonmentBudget)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) budget (e :: rest) = none :=
  orbgrandAi_empty_codebook Y budget (e :: rest)

/-- *Vacuous codebook at zero budget.*  Degenerate corner combining
    two failure modes: the codebook rejects every codeword AND the
    abandonment budget is exhausted from the start.  Specialises
    `orbgrandAi_empty_codebook` at `AbandonmentBudget.mk 0`. -/
theorem orbgrandAi_empty_codebook_zero_budget
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 0) patterns = none :=
  orbgrandAi_empty_codebook Y (AbandonmentBudget.mk 0) patterns

/-- *Vacuous codebook at unit budget.*  Specialises
    `orbgrandAi_empty_codebook` at `AbandonmentBudget.mk 1`. -/
theorem orbgrandAi_empty_codebook_mk_one
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 1) patterns = none :=
  orbgrandAi_empty_codebook Y (AbandonmentBudget.mk 1) patterns

/-- *Vacuous codebook at budget `2`.*  Specialises
    `orbgrandAi_empty_codebook` at `AbandonmentBudget.mk 2`. -/
theorem orbgrandAi_empty_codebook_mk_two
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 2) patterns = none :=
  orbgrandAi_empty_codebook Y (AbandonmentBudget.mk 2) patterns

/-- *Vacuous codebook on the empty pattern list at zero budget.*
    Specialises `orbgrandAi_empty_codebook_zero_budget` at
    `patterns = []`. -/
theorem orbgrandAi_empty_codebook_nil_zero_budget
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 0)
      ([] : List (Fin (n_s / b) -> Fin numCandidates)) = none :=
  orbgrandAi_empty_codebook_zero_budget Y []

/-! ## Substitution provenance (soundness of the output) -/

/-- *Returned codewords come from the substitution operator.*  If the
    loop returns `some c`, then there exists a pattern `e` in the
    input list such that `c = substitute Y e`.  Together with
    `orbgrandAiLoop_accept_sound`, this establishes that any accepted
    output is both in the codebook (via `Phi`) and a candidate
    substitution of the received vector. -/
theorem orbgrandAiLoop_returns_substituted
    {n_s b numCandidates : Nat} :
    forall (Y : Codeword n_s) (Phi : CodebookMembership n_s)
      (c : Codeword n_s) (steps : Nat)
      (patterns : List (Fin (n_s / b) -> Fin numCandidates)),
      orbgrandAiLoop Y Phi steps patterns = some c ->
        exists e, e ∈ patterns /\ c = substitute Y e
  | _, _,   _, 0,     [],         h => nomatch h
  | _, _,   _, _ + 1, [],         h => nomatch h
  | _, _,   _, 0,     _ :: _,     h => nomatch h
  | Y, Phi, c, m + 1, e :: rest,  h =>
      let hdite : (if hnc : noSubstitutionConflict e then
                    (if Phi (substitute Y e) then some (substitute Y e)
                      else orbgrandAiLoop Y Phi m rest)
                    else orbgrandAiLoop Y Phi m rest)
                  = some c := h
      if hnc : noSubstitutionConflict e then
        let hif : (if Phi (substitute Y e) then some (substitute Y e)
                    else orbgrandAiLoop Y Phi m rest)
                  = some c :=
            (dif_pos hnc).symm.trans hdite
        if hp : Phi (substitute Y e) then
          let hsome : some (substitute Y e) = some c :=
              (if_pos hp).symm.trans hif
          let heq : substitute Y e = c := Option.some.inj hsome
          ⟨e, List.mem_cons_self, heq.symm⟩
        else
          let hloop : orbgrandAiLoop Y Phi m rest = some c :=
              (if_neg hp).symm.trans hif
          let ⟨e', hmem, hceq⟩ :=
              orbgrandAiLoop_returns_substituted Y Phi c m rest hloop
          ⟨e', List.mem_cons_of_mem e hmem, hceq⟩
      else
        let hloop : orbgrandAiLoop Y Phi m rest = some c :=
            (dif_neg hnc).symm.trans hdite
        let ⟨e', hmem, hceq⟩ :=
            orbgrandAiLoop_returns_substituted Y Phi c m rest hloop
        ⟨e', List.mem_cons_of_mem e hmem, hceq⟩

/-- *Returned codewords come from the substitution operator (top-level).*
    Wrapper of `orbgrandAiLoop_returns_substituted` threaded through
    `AbandonmentBudget`. -/
theorem orbgrandAi_returns_substituted
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (c : Codeword n_s)
    (h : orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi budget patterns = some c) :
    exists e, e ∈ patterns /\ c = substitute Y e :=
  orbgrandAiLoop_returns_substituted Y Phi c budget.toNat patterns h

/-- *Strong soundness.*  If the loop returns `some c`, there exists a
    witness pattern `e` that passes both the conflict check AND the
    membership oracle, and that substitutes to `c`.  Strengthens
    `orbgrandAiLoop_returns_substituted` by carrying `noSubstitutionConflict e`
    and `Phi (substitute Y e)` through the existential. -/
theorem orbgrandAiLoop_returns_strong
    {n_s b numCandidates : Nat} :
    forall (Y : Codeword n_s) (Phi : CodebookMembership n_s)
      (c : Codeword n_s) (steps : Nat)
      (patterns : List (Fin (n_s / b) -> Fin numCandidates)),
      orbgrandAiLoop Y Phi steps patterns = some c ->
        exists e, e ∈ patterns
                  /\ noSubstitutionConflict e
                  /\ Phi (substitute Y e)
                  /\ c = substitute Y e
  | _, _,   _, 0,     [],         h => nomatch h
  | _, _,   _, _ + 1, [],         h => nomatch h
  | _, _,   _, 0,     _ :: _,     h => nomatch h
  | Y, Phi, c, m + 1, e :: rest,  h =>
      let hdite : (if hnc : noSubstitutionConflict e then
                    (if Phi (substitute Y e) then some (substitute Y e)
                      else orbgrandAiLoop Y Phi m rest)
                    else orbgrandAiLoop Y Phi m rest)
                  = some c := h
      if hnc : noSubstitutionConflict e then
        let hif : (if Phi (substitute Y e) then some (substitute Y e)
                    else orbgrandAiLoop Y Phi m rest)
                  = some c :=
            (dif_pos hnc).symm.trans hdite
        if hp : Phi (substitute Y e) then
          let hsome : some (substitute Y e) = some c :=
              (if_pos hp).symm.trans hif
          let heq : substitute Y e = c := Option.some.inj hsome
          ⟨e, List.mem_cons_self, hnc, hp, heq.symm⟩
        else
          let hloop : orbgrandAiLoop Y Phi m rest = some c :=
              (if_neg hp).symm.trans hif
          let ⟨e', hmem, hnc', hp', hceq⟩ :=
              orbgrandAiLoop_returns_strong Y Phi c m rest hloop
          ⟨e', List.mem_cons_of_mem e hmem, hnc', hp', hceq⟩
      else
        let hloop : orbgrandAiLoop Y Phi m rest = some c :=
            (dif_neg hnc).symm.trans hdite
        let ⟨e', hmem, hnc', hp', hceq⟩ :=
            orbgrandAiLoop_returns_strong Y Phi c m rest hloop
        ⟨e', List.mem_cons_of_mem e hmem, hnc', hp', hceq⟩

/-- *Strong soundness at the top level.*  Wrapper of
    `orbgrandAiLoop_returns_strong`. -/
theorem orbgrandAi_returns_strong
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (c : Codeword n_s)
    (h : orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi budget patterns = some c) :
    exists e, e ∈ patterns
              /\ noSubstitutionConflict e
              /\ Phi (substitute Y e)
              /\ c = substitute Y e :=
  orbgrandAiLoop_returns_strong Y Phi c budget.toNat patterns h

/-- *Full soundness specification of `orbgrandAi`.*  If `orbgrandAi`
    returns `some c`, then `c` simultaneously
    (1) is accepted by the membership oracle `Phi`, and
    (2) is `substitute Y e` for some pattern `e` from the input list.
    The conjunction captures the no-hallucination property: every
    accepted output traces back to a specific candidate substitution
    of the received vector, and the codebook signs off on it. -/
theorem orbgrandAi_sound
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (c : Codeword n_s)
    (h : orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi budget patterns = some c) :
    Phi c = true
    /\ (exists e, e ∈ patterns /\ c = substitute Y e) :=
  ⟨orbgrandAi_accept_sound Y Phi budget patterns c h,
   orbgrandAi_returns_substituted Y Phi budget patterns c h⟩

/-- *List-extension stability.*  Appending more patterns to the end of
    the input list cannot undo an acceptance: if the original list
    accepts within `steps`, so does the extended list with the same
    `steps`.  Structural recursion on `p1`; the extra patterns sit at
    positions the loop never reaches once `p1` has accepted. -/
theorem orbgrandAiLoop_append_left
    {n_s b numCandidates : Nat} :
    forall (Y : Codeword n_s) (Phi : CodebookMembership n_s)
      (c : Codeword n_s) (steps : Nat)
      (p1 : List (Fin (n_s / b) -> Fin numCandidates)),
      orbgrandAiLoop Y Phi steps p1 = some c ->
      forall (p2 : List (Fin (n_s / b) -> Fin numCandidates)),
        orbgrandAiLoop Y Phi steps (p1 ++ p2) = some c
  | _, _,   _, 0,     [],         h, _ => nomatch h
  | _, _,   _, _ + 1, [],         h, _ => nomatch h
  | _, _,   _, 0,     _ :: _,     h, _ => nomatch h
  | Y, Phi, c, m + 1, e :: rest1, h, p2 =>
      let hdite : (if hnc : noSubstitutionConflict e then
                    (if Phi (substitute Y e) then some (substitute Y e)
                      else orbgrandAiLoop Y Phi m rest1)
                    else orbgrandAiLoop Y Phi m rest1)
                  = some c := h
      if hnc : noSubstitutionConflict e then
        let hif : (if Phi (substitute Y e) then some (substitute Y e)
                    else orbgrandAiLoop Y Phi m rest1)
                  = some c :=
            (dif_pos hnc).symm.trans hdite
        if hp : Phi (substitute Y e) then
          let hsome : some (substitute Y e) = some c :=
              (if_pos hp).symm.trans hif
          let pos_step :
              (if Phi (substitute Y e) then some (substitute Y e)
                else orbgrandAiLoop Y Phi m (rest1 ++ p2))
              = some c :=
              (if_pos hp).trans hsome
          (dif_pos hnc).trans pos_step
        else
          let hloop : orbgrandAiLoop Y Phi m rest1 = some c :=
              (if_neg hp).symm.trans hif
          let hloop_app : orbgrandAiLoop Y Phi m (rest1 ++ p2) = some c :=
              orbgrandAiLoop_append_left Y Phi c m rest1 hloop p2
          let neg_step :
              (if Phi (substitute Y e) then some (substitute Y e)
                else orbgrandAiLoop Y Phi m (rest1 ++ p2))
              = some c :=
              (if_neg hp).trans hloop_app
          (dif_pos hnc).trans neg_step
      else
        let hloop : orbgrandAiLoop Y Phi m rest1 = some c :=
            (dif_neg hnc).symm.trans hdite
        let hloop_app : orbgrandAiLoop Y Phi m (rest1 ++ p2) = some c :=
            orbgrandAiLoop_append_left Y Phi c m rest1 hloop p2
        (dif_neg hnc).trans hloop_app

/-- *List-extension stability at the top level.*  Wrapper of
    `orbgrandAiLoop_append_left`. -/
theorem orbgrandAi_append_left
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (p1 p2 : List (Fin (n_s / b) -> Fin numCandidates))
    (c : Codeword n_s)
    (h : orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi budget p1 = some c) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget (p1 ++ p2) = some c :=
  orbgrandAiLoop_append_left Y Phi c budget.toNat p1 h p2

/-- *All-fail sufficient condition.*  If every pattern in the input
    fails at least one of the two acceptance gates (conflict check or
    `Phi` acceptance), the loop returns `none`.  The dual of the
    strong-soundness theorem: where the strong soundness extracts a
    passing witness from a `some`, this rules out a `some` whenever
    every candidate is forced to be skipped.  Structural recursion on
    `(steps, patterns)`. -/
theorem orbgrandAiLoop_none_of_all_fail
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) :
    forall (steps : Nat)
      (patterns : List (Fin (n_s / b) -> Fin numCandidates)),
      (forall e, e ∈ patterns ->
        ¬ noSubstitutionConflict e ∨ ¬ Phi (substitute Y e)) ->
      orbgrandAiLoop Y Phi steps patterns = none
  | _,     [],         _     => orbgrandAiLoop_nil _ _ _
  | 0,     _ :: _,     _     => rfl
  | m + 1, e :: rest, hfail =>
      let heither : ¬ noSubstitutionConflict e ∨ ¬ Phi (substitute Y e) :=
        hfail e List.mem_cons_self
      let h_rest : forall e', e' ∈ rest ->
          ¬ noSubstitutionConflict e' ∨ ¬ Phi (substitute Y e') :=
        fun e' hmem => hfail e' (List.mem_cons_of_mem e hmem)
      let ih : orbgrandAiLoop Y Phi m rest = none :=
        orbgrandAiLoop_none_of_all_fail Y Phi m rest h_rest
      if hnc : noSubstitutionConflict e then
        let hp_not : ¬ Phi (substitute Y e) :=
          heither.resolve_left (fun hnc_neg => hnc_neg hnc)
        (orbgrandAiLoop_cons_reject Y Phi m e rest hnc hp_not).trans ih
      else
        (orbgrandAiLoop_cons_conflict Y Phi m e rest hnc).trans ih

/-- *All-fail sufficient condition at the top level.*  Wrapper of
    `orbgrandAiLoop_none_of_all_fail` for `orbgrandAi`. -/
theorem orbgrandAi_none_of_all_fail
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (hfail : forall e, e ∈ patterns ->
      ¬ noSubstitutionConflict e ∨ ¬ Phi (substitute Y e)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget patterns = none :=
  orbgrandAiLoop_none_of_all_fail Y Phi budget.toNat patterns hfail

/-- *All-fail necessary condition under sufficient budget.*  When
    `steps >= patterns.length`, the loop visits every pattern before
    returning, so if the result is `none` every pattern must fail at
    least one acceptance gate.  Structural recursion on
    `(steps, patterns)` with case split on the conflict / `Phi`
    discriminants; the accept branch produces a `some` contradicting
    the `none` hypothesis (`nomatch`). -/
theorem orbgrandAiLoop_none_imp_all_fail_of_budget
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) :
    forall (steps : Nat)
      (patterns : List (Fin (n_s / b) -> Fin numCandidates)),
      patterns.length <= steps ->
      orbgrandAiLoop Y Phi steps patterns = none ->
      forall e, e ∈ patterns ->
        ¬ noSubstitutionConflict e ∨ ¬ Phi (substitute Y e)
  | _,     [],         _,    _,     _,  hmem => (List.not_mem_nil hmem).elim
  | 0,     _ :: _,    hlen, _,     _,  _    =>
      (Nat.not_succ_le_zero _ hlen).elim
  | m + 1, e :: rest, hlen, hnone, Ng, hmem =>
      let rest_len : rest.length <= m := Nat.le_of_succ_le_succ hlen
      if hnc : noSubstitutionConflict e then
        let hif : (if Phi (substitute Y e) then some (substitute Y e)
                    else orbgrandAiLoop Y Phi m rest)
                  = none :=
            (dif_pos hnc).symm.trans hnone
        if hp : Phi (substitute Y e) then
          nomatch (if_pos hp).symm.trans hif
        else
          let h_rest_none : orbgrandAiLoop Y Phi m rest = none :=
            (if_neg hp).symm.trans hif
          match hmem with
          | List.Mem.head _    => Or.inr hp
          | List.Mem.tail _ hrm =>
              orbgrandAiLoop_none_imp_all_fail_of_budget
                Y Phi m rest rest_len h_rest_none Ng hrm
      else
        let h_rest_none : orbgrandAiLoop Y Phi m rest = none :=
          (dif_neg hnc).symm.trans hnone
        match hmem with
        | List.Mem.head _    => Or.inl hnc
        | List.Mem.tail _ hrm =>
            orbgrandAiLoop_none_imp_all_fail_of_budget
              Y Phi m rest rest_len h_rest_none Ng hrm

/-- *Loop failure characterisation under sufficient budget.*
    Combines `_none_of_all_fail` (always) with
    `_none_imp_all_fail_of_budget` (under `steps >= patterns.length`)
    to give the full iff. -/
theorem orbgrandAiLoop_none_iff_of_budget
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (steps : Nat)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (hbudget : patterns.length <= steps) :
    orbgrandAiLoop Y Phi steps patterns = none <->
      forall e, e ∈ patterns ->
        ¬ noSubstitutionConflict e ∨ ¬ Phi (substitute Y e) :=
  ⟨orbgrandAiLoop_none_imp_all_fail_of_budget Y Phi steps patterns hbudget,
   orbgrandAiLoop_none_of_all_fail Y Phi steps patterns⟩

/-- *Top-level failure characterisation under sufficient budget.* -/
theorem orbgrandAi_none_iff_of_budget
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (hbudget : patterns.length <= budget.toNat) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget patterns = none <->
      forall e, e ∈ patterns ->
        ¬ noSubstitutionConflict e ∨ ¬ Phi (substitute Y e) :=
  orbgrandAiLoop_none_iff_of_budget Y Phi budget.toNat patterns hbudget

/-- *Definitional bridge from `orbgrandAi` to `orbgrandAiLoop`.*  By
    definition, the public entry point `orbgrandAi` is just
    `orbgrandAiLoop` invoked at `budget.toNat`.  Exposes this as a
    named rewrite so downstream proofs can drop into the loop layer
    without re-wrapping through `AbandonmentBudget`.  Direct `rfl`. -/
theorem orbgrandAi_unfolds_to_loop
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget patterns
      = orbgrandAiLoop Y Phi budget.toNat patterns := rfl

/-- *Reverse definitional bridge: from `orbgrandAiLoop` back to the
    public API.*  When the step count `steps` arises as
    `budget.toNat`, the loop form rewrites to the top-level
    `orbgrandAi`.  Reverse direction of `orbgrandAi_unfolds_to_loop`. -/
theorem orbgrandAiLoop_eq_orbgrandAi
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAiLoop Y Phi budget.toNat patterns
      = orbgrandAi (b := b) (numCandidates := numCandidates)
          Y Phi budget patterns :=
  (orbgrandAi_unfolds_to_loop Y Phi budget patterns).symm

/-- *Public API at zero budget on a non-empty pattern list.*  At
    `budget = AbandonmentBudget.mk 0`, the loop has no steps and
    returns `none` for any non-empty pattern list.  Direct lift of
    `orbgrandAiLoop_zero_steps_cons` through the definitional
    unfolding of `orbgrandAi`. -/
theorem orbgrandAi_zero_steps_cons
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi (AbandonmentBudget.mk 0) (e :: rest) = none :=
  orbgrandAiLoop_zero_steps_cons Y Phi e rest

/-- *Reverse of `orbgrandAi_zero_steps_cons`.*  At zero budget on a
    non-empty pattern list, the decoder returns `none`, expressed
    with the `none` on the left. -/
theorem orbgrandAi_zero_steps_cons_symm
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates)) :
    (none : Option (Codeword n_s))
      = orbgrandAi (b := b) (numCandidates := numCandidates)
          Y Phi (AbandonmentBudget.mk 0) (e :: rest) :=
  (orbgrandAi_zero_steps_cons Y Phi e rest).symm

/-- *Empty pattern list at the public API.*  With no patterns to
    try, the top-level `orbgrandAi` decoder returns `none` for any
    `Y`, `Phi`, `budget`.  Composes `orbgrandAi_unfolds_to_loop`
    with `orbgrandAiLoop_nil` at `budget.toNat`. -/
theorem orbgrandAi_nil
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget [] = none :=
  (orbgrandAi_unfolds_to_loop Y Phi budget []).trans
    (orbgrandAiLoop_nil Y Phi budget.toNat)

/-- *Reverse of `orbgrandAi_nil`.*  Empty pattern list returns
    `none`, expressed with the `none` on the left. -/
theorem orbgrandAi_nil_symm
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget) :
    (none : Option (Codeword n_s))
      = orbgrandAi (b := b) (numCandidates := numCandidates)
          Y Phi budget [] :=
  (orbgrandAi_nil Y Phi budget).symm

/-- *Bridge between the two `_nil` lemmas.*  The public API on an
    empty pattern list and the loop on an empty pattern list both
    return `none`, hence are equal.  Composes `orbgrandAi_nil` with
    the `.symm` of `orbgrandAiLoop_nil`. -/
theorem orbgrandAi_nil_eq_orbgrandAiLoop_nil
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi budget []
      = orbgrandAiLoop (b := b) (numCandidates := numCandidates)
          Y Phi budget.toNat [] :=
  (orbgrandAi_nil Y Phi budget).trans
    (orbgrandAiLoop_nil Y Phi budget.toNat).symm

/-- *Public API at zero budget on the empty pattern list.*  The
    degenerate corner where both gates of `orbgrandAi` are
    trivially blocked: the budget is exhausted from the start AND
    there are no patterns to try.  Direct specialisation of
    `orbgrandAi_nil` at `AbandonmentBudget.mk 0`. -/
theorem orbgrandAi_zero_steps_nil
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi (AbandonmentBudget.mk 0) [] = none :=
  orbgrandAi_nil Y Phi (AbandonmentBudget.mk 0)

/-- *Public-API cons-conflict.*  Wrapper around `orbgrandAiLoop_cons_conflict`:
    with budget `⟨m + 1⟩`, a head pattern that has a substitution
    conflict is skipped, advancing to the rest with budget `⟨m⟩`. -/
theorem orbgrandAi_cons_conflict
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (h : ¬ noSubstitutionConflict e) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi ⟨m + 1⟩ (e :: rest)
      = orbgrandAi Y Phi ⟨m⟩ rest :=
  orbgrandAiLoop_cons_conflict Y Phi m e rest h

/-- *Public-API cons-reject.*  Wrapper around `orbgrandAiLoop_cons_reject`
    threaded through the `AbandonmentBudget` structure: with budget
    `⟨m + 1⟩`, a non-conflicting head whose substitution is rejected
    by `Phi` advances to the rest with budget `⟨m⟩` (one step
    consumed). -/
theorem orbgrandAi_cons_reject
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (hnc : noSubstitutionConflict e)
    (hp : ¬ Phi (substitute Y e)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi ⟨m + 1⟩ (e :: rest)
      = orbgrandAi Y Phi ⟨m⟩ rest :=
  orbgrandAiLoop_cons_reject Y Phi m e rest hnc hp

/-- *Public-API cons-accept.*  Wrapper around `orbgrandAiLoop_cons_accept`
    threaded through the `AbandonmentBudget` structure: with budget
    `⟨m + 1⟩`, a non-conflicting head pattern whose substitution is
    accepted by `Phi` returns immediately.  Defeq unfolding gives
    `orbgrandAi Y Phi ⟨m + 1⟩ (e :: rest) = orbgrandAiLoop Y Phi (m + 1) (e :: rest)`. -/
theorem orbgrandAi_cons_accept
    {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (hnc : noSubstitutionConflict e)
    (hp : Phi (substitute Y e)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi ⟨m + 1⟩ (e :: rest)
      = some (substitute Y e) :=
  orbgrandAiLoop_cons_accept Y Phi m e rest hnc hp

end Section04
end OrbgrandAi
