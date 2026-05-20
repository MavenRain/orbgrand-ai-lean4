import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
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

/-! ## ML-optimality (placeholder, gated on the soundness above) -/

/-- *ML-optimality of GRAND* (paper, IV.A).

    When the noise-guess sequence is enumerated in non-increasing
    posterior `p(N = N_g | Y)`, `grandFind` returns the
    most-likely codeword consistent with `Y`, i.e., the
    maximum-likelihood decoded codeword.

    *Placeholder shape.*  Encodes the statement: for any noise `Ng'`
    that is in the order list AND has zero syndrome, the posterior
    `p Ng'` is at most the posterior of the noise `Y xor c` that
    GRAND chose.  Proof is structural induction on the candidate
    list, using the just-proved `grandFind_zero_syndrome` for the
    base case (the True branch of `dif_pos`) and the sorted_dec
    hypothesis to compare positions.

    The non-trivial step is establishing that `Ng' ∈ order` at some
    position `j` AND `j >= i` (where `i` is GRAND's accept index):
    for `j < i`, every prior `order[j]?` has non-zero syndrome (else
    GRAND would have stopped earlier), so `Ng' = order[j]?` cannot
    have zero syndrome.  Scheduled for follow-up. -/
theorem grand_ml_optimal_statement
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (p : Codeword n -> Real)
    (order : List (Codeword n))
    (sorted_dec : forall (Ng Ng' : Codeword n) (i j : Nat),
        order[i]? = some Ng -> order[j]? = some Ng' ->
        i <= j -> p Ng' <= p Ng) :
    (forall (c : Codeword n),
        grandFind H Y order = some c ->
          forall (Ng' : Codeword n),
            Ng' ∈ order ->
            (forall (j : Fin (n - k)),
              H.matrix.mulVec (Codeword.xor Y Ng') j = 0) ->
            p Ng' <= p (Codeword.xor Y c)) -> True := by
  kan_intro _h
  kan_constructor

end Section04
end OrbgrandAi
