import Mathlib.Data.Real.Basic
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
    `Option (Fin numCandidates)`; `none` only when
    `numCandidates = 0`.

    *Placeholder shape.*  The constructive argmax implementation is
    deferred; for now we expose the signature as opaque so downstream
    consumers can refer to a hard-decision block even before the
    concrete algorithm is wired up. -/
opaque hardDecisionBlock?
    {numCandidates : Nat} (post : BlockPosterior numCandidates) :
    Option (Fin numCandidates)

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

/-! ## Boundary-case behaviour of the loop -/

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

end Section04
end OrbgrandAi
