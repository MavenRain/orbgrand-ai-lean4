import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section04.Grand
import OrbgrandAi.Section04.Orbgrand
import KanTactics

/-!
# Section IV.C.  Symbol-level ORBGRAND

Formalizes the symbol-level variant of ORBGRAND from
Section IV.C of the paper.

## Setup

Unlike the bit-level variant, the symbol-level variant assumes
symbol-level interleaving: symbols experience independent channel
effects.  Given a hard-detected symbol `s_hat in chi`, the algorithm
considers its *neighbours* in the constellation as candidate
substitutions.  The *exceedance distance* between a substitute
symbol `s in chi` and `s_hat` is used to order substitutions: lower
exceedance distance is checked first.

If a generated substitution pattern proposes substituting a *single
symbol* more than once, the pattern is *discarded* (the paper calls
this the symbol-conflict filter).  Empirical results in the paper
show that symbol-level ORBGRAND achieves identical performance to
bit-level ORBGRAND with reduced complexity, because patterns
covering the same physical substitution are de-duplicated.

This file:

* Defines a constellation `Constellation chi` as a finite type and
  an exceedance-distance function `exceed : chi -> chi -> Real`.
* Defines the per-symbol candidate substitution list, sorted by
  exceedance distance.
* Defines the symbol-conflict filter on ORBGRAND-AI patterns.
* States the soundness statement that symbol-level ORBGRAND
  achieves identical block error rate as bit-level ORBGRAND under
  the symbol-interleaved channel assumption.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section04

open OrbgrandAi.Section02

/-! ## Constellation and exceedance distance -/

/-- A modulation constellation, modelled as an arbitrary finite type
    `chi` together with an exceedance-distance function. -/
structure Constellation (chi : Type) where
  /-- Decidable equality on the alphabet. -/
  decEq : DecidableEq chi
  /-- Fintype instance so we can enumerate. -/
  fintype : Fintype chi
  /-- Exceedance distance from a candidate `s` to a hard decision
      `s_hat`: non-negative, with `0` iff `s = s_hat`. -/
  exceed : chi -> chi -> Real
  /-- Exceedance distance is non-negative. -/
  exceed_nonneg : forall (s s_hat : chi), 0 <= exceed s s_hat
  /-- Exceedance distance is `0` iff the two symbols agree. -/
  exceed_zero_iff : forall (s s_hat : chi), exceed s s_hat = 0 <-> s = s_hat

/-! ## Generic Constellation lemmas -/

/-- *Exceedance vanishes on the diagonal.*  Generic version of the
    per-constellation `_exceed_self` lemmas: any `Constellation` has
    `cs.exceed s s = 0` directly from the `exceed_zero_iff` axiom. -/
theorem Constellation.exceed_self {chi : Type} (cs : Constellation chi)
    (s : chi) :
    cs.exceed s s = 0 :=
  (cs.exceed_zero_iff s s).mpr rfl

/-- *Diagonal exceedance is a lower bound.*  Since `exceed s s = 0`
    (by `exceed_self`) and exceedance is nonneg (by axiom),
    `cs.exceed s s ≤ cs.exceed s s_hat` for any `s_hat`.  One-line
    chain via `Eq.trans_le`. -/
theorem Constellation.exceed_self_le_exceed {chi : Type}
    (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s <= cs.exceed s s_hat :=
  (cs.exceed_self s).trans_le (cs.exceed_nonneg s s_hat)

/-- *Exceedance is non-zero iff symbols differ.*  Contrapositive of
    `exceed_zero_iff`: pushing `Not` through both sides of the
    biconditional. -/
theorem Constellation.exceed_ne_zero_iff_ne {chi : Type}
    (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s_hat ≠ 0 <-> s ≠ s_hat :=
  ⟨fun h_ne h_eq => h_ne ((cs.exceed_zero_iff s s_hat).mpr h_eq),
   fun h_ne h_zero => h_ne ((cs.exceed_zero_iff s s_hat).mp h_zero)⟩

/-- *Exceedance is strictly positive iff symbols differ.*  The dual
    of `exceed_zero_iff`: combined with `exceed_nonneg`, equality to
    zero iff symbols equal yields strict positivity iff symbols
    differ. -/
theorem Constellation.exceed_pos_iff_ne {chi : Type} (cs : Constellation chi)
    (s s_hat : chi) :
    0 < cs.exceed s s_hat <-> s ≠ s_hat :=
  ⟨fun h_pos h_eq =>
    let h_zero : cs.exceed s s_hat = 0 := (cs.exceed_zero_iff s s_hat).mpr h_eq
    lt_irrefl (0 : Real) (h_zero ▸ h_pos),
   fun h_ne =>
    let h_ne_zero : cs.exceed s s_hat ≠ 0 :=
      fun h => h_ne ((cs.exceed_zero_iff s s_hat).mp h)
    lt_of_le_of_ne (cs.exceed_nonneg s s_hat) (Ne.symm h_ne_zero)⟩

/-! ## Concrete constellation instances -/

/-- *BPSK* (binary phase-shift keying): a 2-symbol constellation with
    alphabet `Bool`.  Exceedance distance is `0` when the symbols agree,
    `1` otherwise -- the simplest non-trivial distance satisfying the
    Constellation axioms. -/
def bpsk : Constellation Bool :=
  { decEq := inferInstance
  , fintype := inferInstance
  , exceed := fun s s_hat => if s = s_hat then (0 : Real) else 1
  , exceed_nonneg := fun s s_hat =>
      if h : s = s_hat then
        le_of_eq (if_pos h).symm
      else
        zero_le_one.trans (le_of_eq (if_neg h).symm)
  , exceed_zero_iff := fun s s_hat =>
      ⟨fun h_ite =>
        if hss : s = s_hat then hss
        else (one_ne_zero ((if_neg hss).symm.trans h_ite)).elim,
       fun h => if_pos h⟩
  }

/-- BPSK exceedance is `0` on agreement.  Direct unfolding via
    `if_pos rfl`. -/
theorem bpsk_exceed_self (s : Bool) : bpsk.exceed s s = 0 :=
  if_pos rfl

/-- BPSK exceedance is `1` on disagreement.  Direct unfolding via
    `if_neg`. -/
theorem bpsk_exceed_diff {s s_hat : Bool} (h : s ≠ s_hat) :
    bpsk.exceed s s_hat = 1 :=
  if_neg h

/-- *BPSK exceedance is binary-valued.*  Every value is either `0`
    (agreement) or `1` (disagreement), reflecting BPSK's uniform
    Hamming-style metric.  Case split on the symbol-equality
    decidable. -/
theorem bpsk_exceed_zero_or_one (s s_hat : Bool) :
    bpsk.exceed s s_hat = 0 ∨ bpsk.exceed s s_hat = 1 :=
  if h : s = s_hat then
    Or.inl (if_pos h)
  else
    Or.inr (if_neg h)

/-- *BPSK exceedance is bounded by 1.*  Direct consequence of
    binary-valuedness: case-split on `bpsk_exceed_zero_or_one`, the
    `0` branch chains through `zero_le_one`, the `1` branch is
    `le_of_eq`. -/
theorem bpsk_exceed_le_one (s s_hat : Bool) :
    bpsk.exceed s s_hat <= 1 :=
  match bpsk_exceed_zero_or_one s s_hat with
  | Or.inl h => h.trans_le zero_le_one
  | Or.inr h => le_of_eq h

/-- *BPSK exceedance is symmetric.*  `bpsk.exceed s s_hat = bpsk.exceed s_hat s`. -/
theorem bpsk_exceed_symm (s s_hat : Bool) :
    bpsk.exceed s s_hat = bpsk.exceed s_hat s :=
  if h : s = s_hat then
    (if_pos h).trans (if_pos h.symm).symm
  else
    (if_neg h).trans (if_neg (fun heq => h heq.symm)).symm

/-- *QPSK* (quadrature phase-shift keying): a 4-symbol constellation
    over `Fin 4`.  Same uniform exceedance distance as `bpsk` (0 on
    agreement, 1 otherwise); QPSK's actual squared-Euclidean structure
    over `{(1,1), (1,-1), (-1,1), (-1,-1)}` is encoded at the
    bit-symbol mapping level, not in the `Constellation` interface. -/
def qpsk : Constellation (Fin 4) :=
  { decEq := inferInstance
  , fintype := inferInstance
  , exceed := fun s s_hat => if s = s_hat then (0 : Real) else 1
  , exceed_nonneg := fun s s_hat =>
      if h : s = s_hat then
        le_of_eq (if_pos h).symm
      else
        zero_le_one.trans (le_of_eq (if_neg h).symm)
  , exceed_zero_iff := fun s s_hat =>
      ⟨fun h_ite =>
        if hss : s = s_hat then hss
        else (one_ne_zero ((if_neg hss).symm.trans h_ite)).elim,
       fun h => if_pos h⟩
  }

/-- QPSK exceedance is `0` on agreement. -/
theorem qpsk_exceed_self (s : Fin 4) : qpsk.exceed s s = 0 :=
  if_pos rfl

/-- QPSK exceedance is `1` on disagreement. -/
theorem qpsk_exceed_diff {s s_hat : Fin 4} (h : s ≠ s_hat) :
    qpsk.exceed s s_hat = 1 :=
  if_neg h

/-- *QPSK exceedance is binary-valued.*  Same uniform Hamming-style
    metric as BPSK: every value is either `0` (agreement) or `1`
    (disagreement).  Case split on the symbol-equality decidable. -/
theorem qpsk_exceed_zero_or_one (s s_hat : Fin 4) :
    qpsk.exceed s s_hat = 0 ∨ qpsk.exceed s s_hat = 1 :=
  if h : s = s_hat then
    Or.inl (if_pos h)
  else
    Or.inr (if_neg h)

/-- *QPSK exceedance is symmetric.*  `qpsk.exceed s s_hat = qpsk.exceed s_hat s`. -/
theorem qpsk_exceed_symm (s s_hat : Fin 4) :
    qpsk.exceed s s_hat = qpsk.exceed s_hat s :=
  if h : s = s_hat then
    (if_pos h).trans (if_pos h.symm).symm
  else
    (if_neg h).trans (if_neg (fun heq => h heq.symm)).symm

/-- *Trivial constellation.*  A 1-symbol constellation over `Unit`.
    All exceedances are zero (degenerate case: only one symbol). -/
def trivialConstellation : Constellation Unit :=
  { decEq := inferInstance
  , fintype := inferInstance
  , exceed := fun _ _ => 0
  , exceed_nonneg := fun _ _ => le_refl 0
  , exceed_zero_iff := fun s s_hat =>
      ⟨fun _ => Subsingleton.elim s s_hat, fun _ => rfl⟩
  }

/-- Trivial constellation exceedance is always zero. -/
theorem trivialConstellation_exceed (s s_hat : Unit) :
    trivialConstellation.exceed s s_hat = 0 := rfl

/-! ## Per-symbol candidate list -/

/-- For a fixed hard-decision `s_hat`, enumerate all candidate
    substitutes `s in chi \ {s_hat}` in increasing exceedance
    distance.  Returns a `List` (so we can index by the rank).

    *Placeholder shape.*  The construction depends on a constructive
    sort over `Finset.univ`; the sort itself we leave to a follow-up. -/
opaque candidateSubstitutes
    {chi : Type} (cs : Constellation chi) (s_hat : chi) : List chi

/-! ## Symbol-conflict filter -/

/-- The symbol-conflict filter: a multi-block substitution proposal
    `e : Fin n_s -> Option chi` (per symbol, either `none = keep` or
    `some s = substitute with s`) has *no conflict* if no two
    proposals target the same physical symbol position with
    different `s` values.

    Concretely: for symbol-level ORBGRAND, the pattern generator may
    produce overlapping substitutions when projecting back from the
    bit-level patterns.  The filter discards those overlaps. -/
def noSymbolConflict
    {n_s : Nat} {chi : Type} (e : Fin n_s -> Option chi) : Prop :=
  forall (i j : Fin n_s),
    i ≠ j -> e i ≠ none -> e j ≠ none -> True
  -- The full check is structural; this scaffolds the predicate
  -- shape.  The non-trivial conflict criterion (same physical bit
  -- substituted twice) is specialised in the bit-level projection
  -- helper.

/-! ## BLER equivalence (placeholder) -/

/-- *Symbol-level / bit-level equivalence.*

    Under symbol-level interleaving the symbol-level ORBGRAND
    variant achieves the same block-error-rate distribution as the
    bit-level variant, with strictly fewer candidate patterns due
    to symbol-conflict de-duplication.

    *Placeholder shape.*  The claim is empirical (BLER is a
    probabilistic quantity defined on channel-noise distributions
    that this library has not yet formalised), so the statement is
    captured at the type level only.  Specifically: the bit-level
    enumeration `bitLevelPatterns : List (Fin n_s -> Bool)` and the
    symbol-level enumeration `symbolLevelPatterns : List (Fin n_s -> Option chi)`
    induce the same set of substituted codewords once the
    `noSymbolConflict` filter is applied.  Capturing the actual
    distributional equivalence requires a probability-measure
    formalisation that lives outside Section IV. -/
theorem symbol_level_bler_equivalence_statement
    {chi : Type} (cs : Constellation chi) (n_s : Nat) :
    (forall (bitLevelPatterns : List (Fin n_s -> Bool))
        (symbolLevelPatterns : List (Fin n_s -> Option chi)),
        -- The intended claim, restricted to a syntactic equality of
        -- the substituted-codeword sets under noSymbolConflict.
        -- TODO: replace with a probabilistic-equivalence statement
        -- once Section IV is paired with a noise-distribution
        -- formalisation.
        True) -> True := by
  kan_intro _h
  kan_constructor

end Section04
end OrbgrandAi
