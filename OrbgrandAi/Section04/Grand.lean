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

/-! ## Boundary cases of `grandFind` -/

/-- *Empty candidate list.*  With no noise candidates, `grandFind`
    returns `none`. -/
theorem grandFind_nil
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    grandFind H Y [] = none :=
  rfl

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

/-- *XOR provenance of GRAND output.*  If `grandFind` returns `some c`,
    then there exists a noise candidate `Ng` in the input order list
    such that `c = Codeword.xor Y Ng`.  Together with
    `grandFind_zero_syndrome`, this characterises valid GRAND outputs
    as "candidates from the input that have zero syndrome". -/
theorem grandFind_returns_xor
    {n k : Nat} :
    forall (H : ParityCheck n k) (Y : Codeword n)
      (order : List (Codeword n)) (c : Codeword n),
      grandFind H Y order = some c ->
        exists Ng, Ng ∈ order /\ c = Codeword.xor Y Ng
  | _, _, [],            _, h => nomatch h
  | H, Y, (Ng :: rest),  c, h =>
      let hdite : (if _hp : forall (i : Fin (n - k)),
                    H.matrix.mulVec (Codeword.xor Y Ng) i = 0 then
                    some (Codeword.xor Y Ng)
                  else grandFind H Y rest) = some c := h
      if hp : forall (j : Fin (n - k)),
          H.matrix.mulVec (Codeword.xor Y Ng) j = 0 then
        let hsome : some (Codeword.xor Y Ng) = some c :=
          (dif_pos hp).symm.trans hdite
        let heq : Codeword.xor Y Ng = c := Option.some.inj hsome
        ⟨Ng, List.mem_cons_self, heq.symm⟩
      else
        let hrest : grandFind H Y rest = some c :=
          (dif_neg hp).symm.trans hdite
        let ⟨Ng', hmem, hceq⟩ :=
          grandFind_returns_xor H Y rest c hrest
        ⟨Ng', List.mem_cons_of_mem Ng hmem, hceq⟩

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

    Derived from the algebra: `Y xor (Y xor Ng) = (Y xor Y) xor Ng
    = 0 xor Ng = Ng`. -/
theorem Codeword.xor_xor_self {n : Nat} (Y Ng : Codeword n) :
    Codeword.xor Y (Codeword.xor Y Ng) = Ng :=
  let h1 : Codeword.xor Y (Codeword.xor Y Ng)
      = Codeword.xor (Codeword.xor Y Y) Ng :=
    (Codeword.xor_assoc Y Y Ng).symm
  let h2 : Codeword.xor (Codeword.xor Y Y) Ng
      = Codeword.xor 0 Ng :=
    congrArg (fun z => Codeword.xor z Ng) (Codeword.xor_self Y)
  let h3 : Codeword.xor 0 Ng = Ng := Codeword.zero_xor Ng
  h1.trans (h2.trans h3)

/-- `Codeword.xor` is left-cancellable: `a xor b = a xor c → b = c`.

    Apply `Codeword.xor a` to both sides of `a xor b = a xor c`,
    then collapse via `xor_xor_self`.

    Proof: from `h : a xor b = a xor c`, get
    `a xor (a xor b) = a xor (a xor c)` by `congrArg`, then both
    sides simplify to `b` and `c` respectively via the involution. -/
theorem Codeword.xor_left_cancel {n : Nat} {a b c : Codeword n}
    (h : Codeword.xor a b = Codeword.xor a c) : b = c :=
  let h1 : Codeword.xor a (Codeword.xor a b)
      = Codeword.xor a (Codeword.xor a c) :=
    congrArg (Codeword.xor a) h
  let h2 : b = Codeword.xor a (Codeword.xor a b) :=
    (Codeword.xor_xor_self a b).symm
  let h3 : Codeword.xor a (Codeword.xor a c) = c :=
    Codeword.xor_xor_self a c
  h2.trans (h1.trans h3)

/-- `Codeword.xor` is right-cancellable: `a xor c = b xor c → a = b`.

    Proof: from `h : a xor c = b xor c`, get `a xor (c xor c) = b xor (c xor c)`
    by `congrArg` and `xor_assoc`, then `c xor c = 0` and `_ xor 0 = _`. -/
theorem Codeword.xor_right_cancel {n : Nat} {a b c : Codeword n}
    (h : Codeword.xor a c = Codeword.xor b c) : a = b :=
  let h1 : Codeword.xor (Codeword.xor a c) c = Codeword.xor (Codeword.xor b c) c :=
    congrArg (fun z => Codeword.xor z c) h
  let lhs_eq : Codeword.xor (Codeword.xor a c) c = a :=
    let step1 : Codeword.xor (Codeword.xor a c) c = Codeword.xor a (Codeword.xor c c) :=
      Codeword.xor_assoc a c c
    let step2 : Codeword.xor a (Codeword.xor c c) = Codeword.xor a 0 :=
      congrArg (Codeword.xor a) (Codeword.xor_self c)
    let step3 : Codeword.xor a 0 = a := Codeword.xor_zero a
    step1.trans (step2.trans step3)
  let rhs_eq : Codeword.xor (Codeword.xor b c) c = b :=
    let step1 : Codeword.xor (Codeword.xor b c) c = Codeword.xor b (Codeword.xor c c) :=
      Codeword.xor_assoc b c c
    let step2 : Codeword.xor b (Codeword.xor c c) = Codeword.xor b 0 :=
      congrArg (Codeword.xor b) (Codeword.xor_self c)
    let step3 : Codeword.xor b 0 = b := Codeword.xor_zero b
    step1.trans (step2.trans step3)
  lhs_eq.symm.trans (h1.trans rhs_eq)

/-- `a = b ↔ a xor b = 0` -- equality via XOR.  The "transmitted
    codeword agrees with the received vector exactly when the noise
    vector is zero". -/
theorem Codeword.eq_iff_xor_eq_zero {n : Nat} (a b : Codeword n) :
    a = b ↔ Codeword.xor a b = 0 :=
  ⟨fun h => h ▸ Codeword.xor_self a,
   fun h =>
     -- From `a xor b = 0`, derive `a = b` by `(a xor b) xor b = b`
     -- on the right and `a xor (b xor b) = a` on the left.
     let h1 : Codeword.xor (Codeword.xor a b) b = Codeword.xor 0 b :=
       congrArg (fun z => Codeword.xor z b) h
     let h2 : Codeword.xor (Codeword.xor a b) b = Codeword.xor a (Codeword.xor b b) :=
       Codeword.xor_assoc a b b
     let h3 : Codeword.xor a (Codeword.xor b b) = Codeword.xor a 0 :=
       congrArg (Codeword.xor a) (Codeword.xor_self b)
     let h4 : Codeword.xor a 0 = a := Codeword.xor_zero a
     let h5 : Codeword.xor 0 b = b := Codeword.zero_xor b
     -- a = a xor 0 = a xor (b xor b) = (a xor b) xor b = 0 xor b = b
     ((h4.symm.trans h3.symm).trans h2.symm).trans (h1.trans h5)⟩

/-- A specific witness of `xor_eq_zero_iff`: from `a xor b = 0`,
    conclude `a = b`. -/
theorem Codeword.eq_of_xor_eq_zero {n : Nat} {a b : Codeword n}
    (h : Codeword.xor a b = 0) : a = b :=
  (Codeword.eq_iff_xor_eq_zero a b).mpr h

/-- A specific witness of `xor_eq_zero_iff`: from `a = b`, conclude
    `a xor b = 0`. -/
theorem Codeword.xor_eq_zero_of_eq {n : Nat} {a b : Codeword n}
    (h : a = b) : Codeword.xor a b = 0 :=
  (Codeword.eq_iff_xor_eq_zero a b).mp h

/-- *Zero-noise short-circuit.*  If `Y` is already a codeword (zero
    syndrome) and the zero-noise candidate is the head of the
    candidate list, `grandFind` returns `Y` immediately.  Composes the
    if-pos branch with `Codeword.xor_zero` to identify `Y xor 0` with
    `Y`. -/
theorem grandFind_zero_first
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (rest : List (Codeword n))
    (h_cw : forall (i : Fin (n - k)), H.matrix.mulVec Y i = 0) :
    grandFind H Y (0 :: rest) = some Y :=
  let xz : Codeword.xor Y 0 = Y := Codeword.xor_zero Y
  let hp : forall (i : Fin (n - k)),
      H.matrix.mulVec (Codeword.xor Y 0) i = 0 :=
    fun i => xz.symm ▸ h_cw i
  (dif_pos hp).trans (congrArg some xz)

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
