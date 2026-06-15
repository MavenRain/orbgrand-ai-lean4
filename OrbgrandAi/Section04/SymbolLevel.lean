import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import OrbgrandAi.Section00.Probability
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

/-- *Diagonal exceedance is non-negative.*  Special case of
    `exceed_nonneg` at `s_hat = s`; the diagonal value is exactly
    `0`, and `exceed_nonneg` certifies `0 <= cs.exceed s s`. -/
theorem Constellation.exceed_self_nonneg {chi : Type}
    (cs : Constellation chi) (s : chi) :
    0 <= cs.exceed s s :=
  cs.exceed_nonneg s s

/-- *Diagonal exceedance is unique up to symbol.*  Any two diagonal
    exceedances are equal: `cs.exceed s s = cs.exceed s_hat s_hat`.
    Both sides are `0` by `exceed_self`, so chaining `.trans` and
    `.symm` closes the goal in one line. -/
theorem Constellation.exceed_self_eq_exceed_self {chi : Type}
    (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s = cs.exceed s_hat s_hat :=
  (cs.exceed_self s).trans (cs.exceed_self s_hat).symm

/-- *Exceedance vanishes iff symbols agree.*  Generic-name re-exposure
    of the `exceed_zero_iff` structure field as a public lemma under
    the `Constellation` namespace.  Matches the naming convention of
    `exceed_ne_zero_iff_ne` and `exceed_pos_iff_ne` and lets downstream
    callers cite `cs.exceed_eq_zero_iff_eq` without reaching into the
    structure projection. -/
theorem Constellation.exceed_eq_zero_iff_eq
    {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s_hat = 0 ↔ s = s_hat :=
  cs.exceed_zero_iff s s_hat

/-- *Zero exceedance implies symbol equality.*  Forward extraction
    from the `exceed_zero_iff` axiom: converting an exceedance
    measurement back into an equality between symbols.  Useful for
    decoder soundness arguments that observe a zero distance and
    need to conclude the candidate symbol equals the hard decision. -/
theorem Constellation.eq_of_exceed_zero {chi : Type}
    (cs : Constellation chi) {s s_hat : chi}
    (h : cs.exceed s s_hat = 0) :
    s = s_hat :=
  (cs.exceed_zero_iff s s_hat).mp h

/-- *Symbol equality implies zero exceedance.*  Backward direction
    of `exceed_zero_iff`, packaged for direct use in proof chains
    that need to inject a known symbol equality into an exceedance
    expression.  Dual of `eq_of_exceed_zero`. -/
theorem Constellation.exceed_zero_of_eq {chi : Type}
    (cs : Constellation chi) {s s_hat : chi}
    (h : s = s_hat) :
    cs.exceed s s_hat = 0 :=
  (cs.exceed_zero_iff s s_hat).mpr h

/-- *Diagonal exceedance is a lower bound.*  Since `exceed s s = 0`
    (by `exceed_self`) and exceedance is nonneg (by axiom),
    `cs.exceed s s ≤ cs.exceed s s_hat` for any `s_hat`.  One-line
    chain via `Eq.trans_le`. -/
theorem Constellation.exceed_self_le_exceed {chi : Type}
    (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s <= cs.exceed s s_hat :=
  (cs.exceed_self s).trans_le (cs.exceed_nonneg s s_hat)

/-- *Diagonal at `s_hat` is also a lower bound.*  Mirror of
    `exceed_self_le_exceed`: the diagonal value at the second
    argument (`exceed s_hat s_hat = 0`) is at most any exceedance
    landing at `s_hat`.  Useful when the second argument is the
    "anchor" symbol. -/
theorem Constellation.exceed_self_le_exceed_right {chi : Type}
    (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s_hat s_hat <= cs.exceed s s_hat :=
  (cs.exceed_self s_hat).trans_le (cs.exceed_nonneg s s_hat)

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

/-- *Symbol inequality implies strictly positive exceedance.*  Forward
    direction of `exceed_pos_iff_ne`, packaged for direct injection
    when only the implication direction is needed in a chain. -/
theorem Constellation.exceed_pos_of_ne {chi : Type} (cs : Constellation chi)
    {s s_hat : chi} (h : s ≠ s_hat) :
    0 < cs.exceed s s_hat :=
  (cs.exceed_pos_iff_ne s s_hat).mpr h

/-- *Symbol inequality implies non-zero exceedance.*  Forward
    direction of `exceed_ne_zero_iff_ne`, packaged for direct injection
    when only the implication direction is needed in a chain. -/
theorem Constellation.exceed_ne_of_ne {chi : Type} (cs : Constellation chi)
    {s s_hat : chi} (h : s ≠ s_hat) :
    cs.exceed s s_hat ≠ 0 :=
  (cs.exceed_ne_zero_iff_ne s s_hat).mpr h

/-- *Two-argument congruence for `exceed`.*  If both arguments are
    equal under separate hypotheses, so are the exceedances.  Two
    sequential `▸` substitutions reduce the goal to `rfl`.  Useful
    when substituting symbols (e.g., via decoder identifications) on
    either argument of `exceed`. -/
theorem Constellation.exceed_eq_of_eq {chi : Type}
    (cs : Constellation chi) {s s' s_hat s_hat' : chi}
    (h_s : s = s') (h_hat : s_hat = s_hat') :
    cs.exceed s s_hat = cs.exceed s' s_hat' :=
  h_s ▸ h_hat ▸ rfl

/-- *Exceedance dichotomy.*  Any exceedance value is either the
    minimal `0` (when symbols agree) or strictly positive (when they
    disagree).  Term-mode `match` on `cs.decEq` decides which arm. -/
theorem Constellation.exceed_zero_or_pos
    {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s_hat = 0 \/ 0 < cs.exceed s s_hat :=
  match cs.decEq s s_hat with
  | isTrue h_eq  => Or.inl ((cs.exceed_zero_iff s s_hat).mpr h_eq)
  | isFalse h_ne => Or.inr ((cs.exceed_pos_iff_ne s s_hat).mpr h_ne)

/-- *Non-zero exceedance is positive.*  Direct consequence of the
    dichotomy: if `cs.exceed s s_hat ≠ 0`, then by elimination on
    `exceed_zero_or_pos` only the positive arm survives. -/
theorem Constellation.exceed_pos_of_ne_zero
    {chi : Type} (cs : Constellation chi)
    {s s_hat : chi} (h : cs.exceed s s_hat ≠ 0) :
    0 < cs.exceed s s_hat :=
  (cs.exceed_zero_or_pos s s_hat).elim
    (fun h_eq => absurd h_eq h)
    id

/-- *Positive iff non-zero.*  Combines `ne_of_gt` (forward, trivial)
    with `exceed_pos_of_ne_zero` (backward).  Packages the standard
    "nonneg + nonzero = positive" identity at the `cs.exceed` level. -/
theorem Constellation.exceed_pos_iff_ne_zero
    {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    0 < cs.exceed s s_hat <-> cs.exceed s s_hat ≠ 0 :=
  ⟨ne_of_gt, cs.exceed_pos_of_ne_zero⟩

/-- *Positive exceedance is non-zero.*  Forward direction of
    `exceed_pos_iff_ne_zero`, packaged for direct injection when
    only the implication direction is needed in a chain.  One-line
    application of `ne_of_gt`. -/
theorem Constellation.exceed_ne_zero_of_pos
    {chi : Type} (cs : Constellation chi)
    {s s_hat : chi} (h : 0 < cs.exceed s s_hat) :
    cs.exceed s s_hat ≠ 0 :=
  ne_of_gt h

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

/-- *BPSK diagonal at `true`.*  Concrete instance of
    `bpsk_exceed_self` at `s = true`. -/
theorem bpsk_exceed_true_true : bpsk.exceed true true = 0 :=
  bpsk_exceed_self true

/-- *BPSK diagonal at `false`.*  Concrete instance of
    `bpsk_exceed_self` at `s = false`. -/
theorem bpsk_exceed_false_false : bpsk.exceed false false = 0 :=
  bpsk_exceed_self false

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

/-- *BPSK exceedance is non-negative.*  Specialisation of the
    generic `Constellation.exceed_nonneg` structure field to the
    concrete `bpsk` instance.  Packages the lower bound at the
    instance level so downstream callers can cite
    `bpsk_exceed_nonneg` without reaching through the structure
    projection, mirroring `bpsk_exceed_le_one` at the upper end. -/
theorem bpsk_exceed_nonneg (s s_hat : Bool) :
    0 <= bpsk.exceed s s_hat :=
  bpsk.exceed_nonneg s s_hat

/-- *BPSK exceedance is symmetric.*  `bpsk.exceed s s_hat = bpsk.exceed s_hat s`. -/
theorem bpsk_exceed_symm (s s_hat : Bool) :
    bpsk.exceed s s_hat = bpsk.exceed s_hat s :=
  if h : s = s_hat then
    (if_pos h).trans (if_pos h.symm).symm
  else
    (if_neg h).trans (if_neg (fun heq => h heq.symm)).symm

/-- *BPSK exceedance is `1` exactly on disagreement.*  Combines
    `bpsk_exceed_diff` (backward) with the forward direction via
    the `exceed_zero_iff` axiom: if `s = s_hat` then `exceed = 0`,
    not `1`, contradicting `zero_ne_one`. -/
theorem bpsk_exceed_eq_one_iff (s s_hat : Bool) :
    bpsk.exceed s s_hat = 1 ↔ s ≠ s_hat :=
  ⟨fun h heq =>
      zero_ne_one
        (((bpsk.exceed_zero_iff s s_hat).mpr heq).symm.trans h),
   bpsk_exceed_diff⟩

/-- *BPSK exceedance is non-zero iff symbols differ.*  Dual of
    `bpsk_exceed_eq_one_iff` on the zero side; specialises the
    generic `Constellation.exceed_ne_zero_iff_ne` to `bpsk`. -/
theorem bpsk_exceed_ne_zero_iff_ne (s s_hat : Bool) :
    bpsk.exceed s s_hat ≠ 0 ↔ s ≠ s_hat :=
  ⟨fun h_ne h_eq => h_ne ((bpsk.exceed_zero_iff s s_hat).mpr h_eq),
   fun h_ne h_zero => h_ne ((bpsk.exceed_zero_iff s s_hat).mp h_zero)⟩

/-- *BPSK exceedance is non-zero iff it equals one.*  Binary-valued
    dichotomy from `bpsk_exceed_zero_or_one`: non-zero forces the
    value to `1`; conversely `1 ≠ 0`. -/
theorem bpsk_exceed_ne_zero_iff_eq_one (s s_hat : Bool) :
    bpsk.exceed s s_hat ≠ 0 ↔ bpsk.exceed s s_hat = 1 :=
  ⟨fun h_ne =>
      (bpsk_exceed_zero_or_one s s_hat).elim
        (fun h_zero => absurd h_zero h_ne) id,
   fun h_one h_zero => one_ne_zero (h_one.symm.trans h_zero)⟩

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

/-- *QPSK exceedance is bounded by 1.*  Same case split as
    `bpsk_exceed_le_one` on `qpsk_exceed_zero_or_one`. -/
theorem qpsk_exceed_le_one (s s_hat : Fin 4) :
    qpsk.exceed s s_hat <= 1 :=
  match qpsk_exceed_zero_or_one s s_hat with
  | Or.inl h => h.trans_le zero_le_one
  | Or.inr h => le_of_eq h

/-- *QPSK exceedance is non-negative.*  Specialisation of the
    generic `Constellation.exceed_nonneg` structure field to the
    concrete `qpsk` instance, complementing `qpsk_exceed_le_one`
    at the lower end. -/
theorem qpsk_exceed_nonneg (s s_hat : Fin 4) :
    0 <= qpsk.exceed s s_hat :=
  qpsk.exceed_nonneg s s_hat

/-- *QPSK exceedance is symmetric.*  `qpsk.exceed s s_hat = qpsk.exceed s_hat s`. -/
theorem qpsk_exceed_symm (s s_hat : Fin 4) :
    qpsk.exceed s s_hat = qpsk.exceed s_hat s :=
  if h : s = s_hat then
    (if_pos h).trans (if_pos h.symm).symm
  else
    (if_neg h).trans (if_neg (fun heq => h heq.symm)).symm

/-- *QPSK exceedance is `1` exactly on disagreement.*  Dual of
    `bpsk_exceed_eq_one_iff` for the 4-ary Hamming-style metric. -/
theorem qpsk_exceed_eq_one_iff (s s_hat : Fin 4) :
    qpsk.exceed s s_hat = 1 ↔ s ≠ s_hat :=
  ⟨fun h heq =>
      zero_ne_one
        (((qpsk.exceed_zero_iff s s_hat).mpr heq).symm.trans h),
   qpsk_exceed_diff⟩

/-- *QPSK exceedance is non-zero iff symbols differ.*  Dual of
    `qpsk_exceed_eq_one_iff` on the zero side; mirrors
    `bpsk_exceed_ne_zero_iff_ne` for the 4-ary Hamming-style metric. -/
theorem qpsk_exceed_ne_zero_iff_ne (s s_hat : Fin 4) :
    qpsk.exceed s s_hat ≠ 0 ↔ s ≠ s_hat :=
  ⟨fun h_ne h_eq => h_ne ((qpsk.exceed_zero_iff s s_hat).mpr h_eq),
   fun h_ne h_zero => h_ne ((qpsk.exceed_zero_iff s s_hat).mp h_zero)⟩

/-- *QPSK exceedance is non-zero iff it equals one.*  Binary-valued
    dichotomy from `qpsk_exceed_zero_or_one`.  Mirrors
    `bpsk_exceed_ne_zero_iff_eq_one`. -/
theorem qpsk_exceed_ne_zero_iff_eq_one (s s_hat : Fin 4) :
    qpsk.exceed s s_hat ≠ 0 ↔ qpsk.exceed s s_hat = 1 :=
  ⟨fun h_ne =>
      (qpsk_exceed_zero_or_one s s_hat).elim
        (fun h_zero => absurd h_zero h_ne) id,
   fun h_one h_zero => one_ne_zero (h_one.symm.trans h_zero)⟩

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

/-- *Trivial-constellation diagonal vanishes.*  Specialisation of
    `trivialConstellation_exceed` to the diagonal case `s = s_hat`,
    completing the `_exceed_self` family across the three concrete
    constellation instances. -/
theorem trivialConstellation_exceed_self (s : Unit) :
    trivialConstellation.exceed s s = 0 :=
  trivialConstellation_exceed s s

/-- *Trivial constellation symbols are all equal.*  `Unit` is a
    `Subsingleton`, so any two symbols of the trivial constellation
    coincide.  Complements `trivialConstellation_exceed` at the
    symbol-identity level. -/
theorem trivialConstellation_all_eq (s s_hat : Unit) :
    s = s_hat :=
  Subsingleton.elim s s_hat

/-- *Trivial constellation exceedance is bounded by `1`.*  Direct
    consequence of `trivialConstellation_exceed`: every value is
    exactly `0`, and `0 <= 1` via `zero_le_one`.  Mirrors
    `bpsk_exceed_le_one` / `qpsk_exceed_le_one` for the degenerate
    one-symbol case, completing the `_le_one` family across all
    three concrete constellation instances. -/
theorem trivialConstellation_le_one (s s_hat : Unit) :
    trivialConstellation.exceed s s_hat <= 1 :=
  (trivialConstellation_exceed s s_hat).trans_le zero_le_one

/-- *Trivial constellation exceedance is non-negative.*  Direct
    consequence of `trivialConstellation_exceed`: every value is
    exactly `0`, so `Eq.ge` gives `0 <= 0`.  Completes the `_nonneg`
    family across the three concrete constellation instances. -/
theorem trivialConstellation_nonneg (s s_hat : Unit) :
    0 <= trivialConstellation.exceed s s_hat :=
  (trivialConstellation_exceed s s_hat).ge

/-- *Trivial-constellation exceedance is constant.*  Any two
    exceedance values on the trivial constellation are equal: both
    sides reduce to `0` via `trivialConstellation_exceed`.  Mirrors
    `Constellation.exceed_self_eq_exceed_self` at the trivial
    instance level. -/
theorem trivialConstellation_exceed_eq (s1 s_hat1 s2 s_hat2 : Unit) :
    trivialConstellation.exceed s1 s_hat1
      = trivialConstellation.exceed s2 s_hat2 :=
  (trivialConstellation_exceed s1 s_hat1).trans
    (trivialConstellation_exceed s2 s_hat2).symm

/-! ## Per-symbol candidate list -/

/-- For a fixed hard-decision `s_hat`, enumerate all candidate
    substitutes `s in chi \ {s_hat}` in increasing exceedance
    distance.  Returns a `List` (so we can index by the rank).

    Concrete: erase `s_hat` from `Finset.univ` (via the
    `Constellation`'s `decEq` + `fintype` fields), convert to a list,
    then `List.mergeSort` by `cs.exceed s_hat` ascending.  Marked
    `noncomputable` because `Real`'s order is classical; the
    Bool-valued comparator routes through `Classical.propDecidable`. -/
noncomputable def candidateSubstitutes
    {chi : Type} (cs : Constellation chi) (s_hat : chi) : List chi :=
  let _ : DecidableEq chi := cs.decEq
  let _ : Fintype chi := cs.fintype
  ((Finset.univ : Finset chi).erase s_hat).toList.mergeSort
    (fun s1 s2 =>
      @decide (cs.exceed s_hat s1 ≤ cs.exceed s_hat s2)
        (Classical.propDecidable _))

/-- *Body unfold for `candidateSubstitutes`.*  The definition is just
    `(Finset.univ.erase s_hat).toList` sorted ascending by exceedance
    distance from `s_hat`. -/
theorem candidateSubstitutes_eq
    {chi : Type} (cs : Constellation chi) (s_hat : chi) :
    candidateSubstitutes cs s_hat
      = @List.mergeSort chi
          (let _ : DecidableEq chi := cs.decEq
           let _ : Fintype chi := cs.fintype
           ((Finset.univ : Finset chi).erase s_hat).toList)
          (fun s1 s2 =>
            @decide (cs.exceed s_hat s1 ≤ cs.exceed s_hat s2)
              (Classical.propDecidable _)) := rfl


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

    *Statement form, probabilistic.*  The hypothesis exposes the
    actual BLER-equation shape via `Section00.bler`:
    for every pair `(bitDecoder, symbolDecoder)` of decoders viewed
    as `Bool`-valued failure indicators on `RealSymbolVector n_s`,
    their `Section00.bler` agrees at every noise power `sigma`.
    The closing `True` is retained as a deferred-proof marker until
    a concrete pair `(bitDecoder, symbolDecoder)` derived from the
    actual ORBGRAND-AI variants is wired up.

    *Constellation context.*  The `cs : Constellation chi`
    parameter is the symbol-level alphabet under which the
    symbol-level enumeration is parameterised in the eventual
    concrete claim; it does not appear in the hypothesis here
    because the abstract decoder pair quantifies away the
    constellation choice. -/
theorem symbol_level_bler_equivalence_statement
    {chi : Type} (cs : Constellation chi) (n_s : Nat) :
    (forall (bitDecoder symbolDecoder : Section00.RealSymbolVector n_s -> Bool)
        (sigma : NoisePower),
      Section00.bler sigma bitDecoder
        = Section00.bler sigma symbolDecoder) -> True := by
  kan_intro _h
  kan_constructor

end Section04
end OrbgrandAi
