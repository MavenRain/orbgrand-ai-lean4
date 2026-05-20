import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.CharP.Two
import OrbgrandAi.Section02.Basic
import KanTactics

/-!
# Section IV.A.  GRAND

Formalizes the Guessing Random Additive Noise Decoding scheme from
Section IV.A of the paper.

## Setup

* Codeword length `n : N`.
* Information length `k : N` with `k <= n`.
* Parity-check matrix `H : Bool^{(n - k) x n}`.  We use `ZMod 2`
  instead of `Bool` for the arithmetic (`xor` becomes addition).
* Received vector `Y : ZMod 2 ^ n`.
* Noise candidate `N_g : ZMod 2 ^ n`.

## The GRAND search

For each `N_g` in a query order, compute the syndrome

  s(N_g) = H * (Y `xor` N_g)
         = H * Y `xor` H * N_g  (since `H * c = 0` for a codeword `c`).

If `s(N_g) = 0` then `c := Y `xor` N_g` is a codeword and is
returned.  The algorithm is *maximum-likelihood* if the query order
is non-increasing in `p(N = N_g | Y)` (the posterior on the noise).

This file:

* Defines the parity-check matrix wrapper `ParityCheck`.
* Defines the noise-flip operator and the syndrome `syndrome H Y N_g`.
* States the GRAND search loop as a function `grandFind` that
  consumes a (possibly infinite) sequence of noise guesses and
  returns the first one with zero syndrome.
* States ML optimality of GRAND under a sound query order as a
  placeholder theorem.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section04

open OrbgrandAi.Section02

/-! ## Binary vectors and parity-check matrices -/

/-- A binary codeword of length `n`. -/
abbrev Codeword (n : Nat) := Fin n -> ZMod 2

/-- A parity-check matrix `H` of an `[n, k]` code, encoded as a
    `(n - k) x n` matrix over `ZMod 2`. -/
structure ParityCheck (n k : Nat) where
  /-- The underlying matrix.  Rows index parity checks; columns
      index codeword bits. -/
  matrix : Matrix (Fin (n - k)) (Fin n) (ZMod 2)
  /-- `k <= n` so that the parity matrix has the right shape. -/
  kLeN : k <= n

/-! ## Syndrome -/

/-- Element-wise xor of two binary vectors (`xor` is `(+)` in
    `ZMod 2`). -/
def Codeword.xor {n : Nat} (a b : Codeword n) : Codeword n :=
  fun i => a i + b i

/-- The syndrome `H * (Y xor N_g)` for a candidate noise vector. -/
def syndrome
    {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n) :
    Fin (n - k) -> ZMod 2 :=
  H.matrix.mulVec (Codeword.xor Y N_g)

/-- A noise candidate is *accepted* by the parity check when its
    syndrome vanishes. -/
def syndromeZero
    {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n) : Prop :=
  forall (i : Fin (n - k)), syndrome H Y N_g i = 0

/-! ## The GRAND search -/

/-- The GRAND decoded output: search a finite list of candidate noise
    vectors in order and return the first one whose syndrome is
    zero.  Returns `Option (Codeword n)`; `none` means the candidate
    list was exhausted without finding a codeword (the paper's
    "FAILURE" branch).

    The `if hp : ... then ... else ...` is the *dependent* `if`, so
    the soundness proof can pull `hp : forall i, ... = 0` out of the
    `then` branch via `dif_pos`.  The Decidable instance comes from
    `Fintype.decidableForallFintype` combined with `DecidableEq (ZMod 2)`. -/
def grandFind
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    : List (Codeword n) -> Option (Codeword n)
  | []           => none
  | (Ng :: rest) =>
      let candidate := Codeword.xor Y Ng
      if _hp : forall (i : Fin (n - k)), H.matrix.mulVec candidate i = 0 then
        some candidate
      else
        grandFind H Y rest

/-! ## Soundness: the GRAND output has zero syndrome -/

/-- If `grandFind` returns `some c`, then `c` has zero syndrome (it
    is a codeword).  Structural induction on the candidate list,
    mirroring `OrbgrandAi.Section04.OrbgrandAi.orbgrandAiLoop_accept_sound`.

    By taking `H, Y` as universally quantified arguments AFTER the
    colon rather than as bound parameters BEFORE the colon, the
    recursive call matches all five pattern slots cleanly, which
    avoids the elaborator's confusion over which binders are
    explicit. -/
theorem grandFind_zero_syndrome
    {n k : Nat} :
    forall (H : ParityCheck n k) (Y : Codeword n)
      (order : List (Codeword n)) (c : Codeword n),
      grandFind H Y order = some c ->
      forall (i : Fin (n - k)), H.matrix.mulVec c i = 0
  | _, _, [],            _, h, _ => nomatch h
  | H, Y, (Ng :: rest),  c, h, i =>
      -- Definitionally:
      --   grandFind H Y (Ng :: rest)
      --     = if hp : forall i, H.mulVec (Y xor Ng) i = 0
      --       then some (Y xor Ng)
      --       else grandFind H Y rest
      let hdite : (if _hp : forall (i : Fin (n - k)),
                    H.matrix.mulVec (Codeword.xor Y Ng) i = 0 then
                    some (Codeword.xor Y Ng)
                  else grandFind H Y rest) = some c := h
      if hp : forall (j : Fin (n - k)),
          H.matrix.mulVec (Codeword.xor Y Ng) j = 0 then
        let hsome : some (Codeword.xor Y Ng) = some c :=
          (dif_pos hp).symm.trans hdite
        let heq : Codeword.xor Y Ng = c := Option.some.inj hsome
        heq ▸ hp i
      else
        let hrest : grandFind H Y rest = some c :=
          (dif_neg hp).symm.trans hdite
        grandFind_zero_syndrome H Y rest c hrest i

/-- Surface the soundness in `syndromeZero` form. -/
theorem grandFind_syndromeZero
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) (c : Codeword n)
    (hfind : grandFind H Y order = some c) :
    forall (i : Fin (n - k)), H.matrix.mulVec c i = 0 :=
  grandFind_zero_syndrome H Y order c hfind

/-! ## ML-optimality of GRAND -/

/-! ### `Codeword.xor` algebra (pointwise lifts of ZMod 2 arithmetic) -/

/-- `0 xor a = a`.  Pointwise `zero_add`. -/
theorem Codeword.zero_xor {n : Nat} (a : Codeword n) :
    Codeword.xor 0 a = a :=
  funext fun i => zero_add (a i)

/-- `a xor 0 = a`.  Pointwise `add_zero`. -/
theorem Codeword.xor_zero {n : Nat} (a : Codeword n) :
    Codeword.xor a 0 = a :=
  funext fun i => add_zero (a i)

/-- `a xor a = 0`.  Pointwise `CharTwo.add_self_eq_zero`. -/
theorem Codeword.xor_self {n : Nat} (a : Codeword n) :
    Codeword.xor a a = 0 :=
  funext fun i => CharTwo.add_self_eq_zero (a i)

/-- `a xor b = b xor a`.  Pointwise `add_comm`. -/
theorem Codeword.xor_comm {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = Codeword.xor b a :=
  funext fun i => add_comm (a i) (b i)

/-- `(a xor b) xor c = a xor (b xor c)`.  Pointwise `add_assoc`. -/
theorem Codeword.xor_assoc {n : Nat} (a b c : Codeword n) :
    Codeword.xor (Codeword.xor a b) c = Codeword.xor a (Codeword.xor b c) :=
  funext fun i => add_assoc (a i) (b i) (c i)

/-- XOR involution: `Y xor (Y xor Ng) = Ng` in `ZMod 2`.

    Derivable from the algebra above (`xor_assoc.symm.trans (congrArg ... xor_self).trans zero_xor`),
    but kept inline because the `grand_ml_optimal` proof predates the
    algebra batch. -/
private theorem Codeword.xor_xor_self {n : Nat} (Y Ng : Codeword n) :
    Codeword.xor Y (Codeword.xor Y Ng) = Ng :=
  funext fun i =>
    -- Pointwise: `Y i + (Y i + Ng i) = (Y i + Y i) + Ng i = 0 + Ng i = Ng i`.
    let h1 : Y i + (Y i + Ng i) = (Y i + Y i) + Ng i :=
      (add_assoc (Y i) (Y i) (Ng i)).symm
    let h2 : (Y i + Y i) + Ng i = (0 : ZMod 2) + Ng i :=
      congrArg (· + Ng i) (CharTwo.add_self_eq_zero (Y i))
    let h3 : (0 : ZMod 2) + Ng i = Ng i := zero_add (Ng i)
    h1.trans (h2.trans h3)

/-- *ML-optimality of GRAND* (paper, IV.A).

    When the noise-guess list `order` is sorted in non-increasing
    posterior `p`, `grandFind H Y order = some c` produces a
    codeword `c = Y xor Ng_i` whose corresponding noise `Y xor c`
    has the largest posterior among all noises in `order` that
    produce a codeword (zero syndrome).

    Proof: structural induction on `order`.  In the `cons` case
    we split on whether the head's syndrome is zero (`dif_pos`)
    or non-zero (`dif_neg`), and within each on whether `Ng'` is
    the head or in the tail.  The non-zero / head sub-case is
    impossible (head has non-zero syndrome, contradiction with the
    hypothesis that `Ng'` has zero syndrome).  The tail sub-cases
    use the induction hypothesis on `rest`, with the order's
    sorted_dec lifted to `rest` via `Nat.succ_le_succ` on the
    indices. -/
theorem grand_ml_optimal
    {n k : Nat} :
    forall (p : Codeword n -> Real) (H : ParityCheck n k) (Y : Codeword n)
      (order : List (Codeword n))
      (_ : forall (Ng Ng' : Codeword n) (i j : Nat),
          order[i]? = some Ng -> order[j]? = some Ng' ->
          i <= j -> p Ng' <= p Ng)
      (c : Codeword n)
      (_ : grandFind H Y order = some c)
      (Ng' : Codeword n)
      (_ : Ng' ∈ order)
      (_ : forall (j : Fin (n - k)),
          H.matrix.mulVec (Codeword.xor Y Ng') j = 0),
      p Ng' <= p (Codeword.xor Y c)
  | _, _, _, [],            _,          _, hfind, _,   _,   _    => nomatch hfind
  | p, H, Y, (Ng :: rest),  sorted_dec, c, hfind, Ng', hin, hsyn =>
      let hdite : (if _hp : forall (i : Fin (n - k)),
                    H.matrix.mulVec (Codeword.xor Y Ng) i = 0 then
                    some (Codeword.xor Y Ng)
                  else grandFind H Y rest) = some c := hfind
      if hp : forall (j : Fin (n - k)),
          H.matrix.mulVec (Codeword.xor Y Ng) j = 0 then
        -- Head has zero syndrome: c = Y xor Ng, so Y xor c = Y xor (Y xor Ng) = Ng.
        let hsome : some (Codeword.xor Y Ng) = some c :=
          (dif_pos hp).symm.trans hdite
        let heq : Codeword.xor Y Ng = c := Option.some.inj hsome
        -- Sub-goal: p Ng' <= p Ng (handled by sorted_dec).
        let goal_p : p Ng' <= p Ng :=
          match hin with
          | List.Mem.head _ => le_refl (p Ng')
          | List.Mem.tail _ hrest =>
              let ⟨k, hk⟩ := List.getElem?_of_mem hrest
              sorted_dec Ng Ng' 0 (k + 1) rfl hk (Nat.zero_le _)
        -- Lift to goal: p Ng' <= p (Y xor c).
        --   Y xor c = Y xor (Y xor Ng) (by heq.symm)
        --           = Ng (by Codeword.xor_xor_self)
        -- So p (Y xor c) = p Ng, and goal_p concludes.
        heq.symm ▸ (Codeword.xor_xor_self Y Ng).symm ▸ goal_p
      else
        -- Head has non-zero syndrome: c is from grandFind H Y rest by IH.
        let hrest : grandFind H Y rest = some c :=
          (dif_neg hp).symm.trans hdite
        let sorted_dec_rest :
            forall (Mg Mg' : Codeword n) (i j : Nat),
              rest[i]? = some Mg -> rest[j]? = some Mg' ->
              i <= j -> p Mg' <= p Mg :=
          fun Mg Mg' i j h_i h_j h_le =>
            sorted_dec Mg Mg' (i + 1) (j + 1) h_i h_j (Nat.succ_le_succ h_le)
        match hin with
        | List.Mem.head _ =>
            -- Ng' = Ng; hsyn says Ng has zero syndrome, hp says it does NOT.
            absurd hsyn hp
        | List.Mem.tail _ hrest_mem =>
            grand_ml_optimal p H Y rest sorted_dec_rest c hrest Ng' hrest_mem hsyn

end Section04
end OrbgrandAi
