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

/-- *Pointwise application of `Codeword.xor`.*  Direct rfl unfolding:
    `(a xor b) i = a i + b i`.  Useful when reasoning about specific
    bit positions. -/
theorem Codeword.xor_apply {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a b i = a i + b i := rfl

/-- *Pointwise value of the zero codeword.*  Every bit of `(0 : Codeword n)`
    is `0` (the zero of `ZMod 2`).  Direct rfl via the `Pi.instZero`
    instance. -/
theorem Codeword.zero_apply {n : Nat} (i : Fin n) :
    (0 : Codeword n) i = 0 := rfl

/-- *Codeword equals zero iff every bit is zero.*  Composes
    `funext` with `Codeword.zero_apply` (the rfl that aligns
    `(0 : Codeword n) i` with `0`). -/
theorem Codeword.eq_zero_iff_apply_zero {n : Nat} (a : Codeword n) :
    a = 0 <-> forall i, a i = 0 :=
  ⟨fun h i => congrFun h i, fun h => funext h⟩

/-- *Pointwise `add_zero` on `Codeword`.*  One-liner via `congrFun`
    on the additive-monoid `add_zero` identity. -/
theorem Codeword.add_zero_apply {n : Nat} (a : Codeword n) (i : Fin n) :
    (a + 0) i = a i :=
  congrFun (add_zero a) i

/-- *Pointwise `zero_add` on `Codeword`.*  Dual of `add_zero_apply`. -/
theorem Codeword.zero_add_apply {n : Nat} (a : Codeword n) (i : Fin n) :
    (0 + a) i = a i :=
  congrFun (zero_add a) i

/-- *Codeword equality iff pointwise equality.*  Standard
    `funext`/`congrFun` wrapper at the `Codeword` type.  Useful as a
    named API surface when downstream code dispatches on the iff. -/
theorem Codeword.eq_iff_apply_eq {n : Nat} (a b : Codeword n) :
    a = b <-> forall i, a i = b i :=
  ⟨congrFun, funext⟩

/-- *Pointwise application of `+` on `Codeword`.*  Direct rfl via the
    `Pi.instAdd` instance: `(a + b) i = a i + b i`.  Companion of
    `xor_apply`; useful as a named API surface when reasoning about
    individual bit positions under the `+` form. -/
theorem Codeword.add_apply {n : Nat} (a b : Codeword n) (i : Fin n) :
    (a + b) i = a i + b i := rfl

/-- *Pointwise application of double XOR.*  `(a xor b) xor c` evaluated
    at `i` is `a i + b i + c i`.  Direct rfl through two
    `Codeword.xor` unfoldings.  Useful when reasoning about three-arg
    XOR chains at individual bit positions. -/
theorem Codeword.xor_xor_apply {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) c i = a i + b i + c i := rfl

/-- *XOR equals add pointwise.*  Named application form of
    `xor_eq_add`: `(Codeword.xor a b) i = (a + b) i`.  Useful when
    rewriting between the `xor` and `+` views at a single bit. -/
theorem Codeword.xor_eq_add_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a b i = (a + b) i :=
  (Codeword.xor_apply a b i).trans (Codeword.add_apply a b i).symm

/-- *One-XOR equality via pointwise addition.*  `xor a b = c` iff
    `∀ i, a i + b i = c i`.  Simpler than the two-XOR version: only
    one side has the `xor` form. -/
theorem Codeword.xor_eq_iff_apply_eq
    {n : Nat} (a b c : Codeword n) :
    Codeword.xor a b = c <-> forall i, a i + b i = c i :=
  ⟨fun h i =>
    (Codeword.xor_apply a b i).symm.trans (congrFun h i),
   fun h => funext fun i =>
    (Codeword.xor_apply a b i).trans (h i)⟩

/-- *XOR-zero pointwise form.*  `xor a b = 0` iff `∀ i, a i + b i = 0`.
    Specialisation of `xor_eq_iff_apply_eq` at `c = 0`; relies on
    `Codeword.zero_apply` (rfl) for the RHS reduction. -/
theorem Codeword.xor_eq_zero_iff_apply_zero {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = 0 <-> forall i, a i + b i = 0 :=
  Codeword.xor_eq_iff_apply_eq a b 0

/-- *Two-XOR equality via pointwise addition.*  `xor a b = xor c d`
    iff `∀ i, a i + b i = c i + d i`.  Lifts function equality to
    pointwise comparison after `xor_apply` unfolds both sides. -/
theorem Codeword.xor_eq_iff_apply_eq_apply
    {n : Nat} (a b c d : Codeword n) :
    Codeword.xor a b = Codeword.xor c d
      <-> forall i, a i + b i = c i + d i :=
  ⟨fun h i =>
    let s1 : Codeword.xor a b i = a i + b i :=
      Codeword.xor_apply a b i
    let s2 : Codeword.xor a b i = Codeword.xor c d i := congrFun h i
    let s3 : Codeword.xor c d i = c i + d i :=
      Codeword.xor_apply c d i
    s1.symm.trans (s2.trans s3),
   fun h => funext fun i =>
    let s1 : Codeword.xor a b i = a i + b i :=
      Codeword.xor_apply a b i
    let s2 : a i + b i = c i + d i := h i
    let s3 : c i + d i = Codeword.xor c d i :=
      (Codeword.xor_apply c d i).symm
    s1.trans (s2.trans s3)⟩

/-- *Pointwise XOR with zero on the right.*  `(a xor 0) i = a i`.
    Combines `xor_apply` with `Codeword.zero_apply` and `add_zero`.
    Captures the identity-on-the-right behavior at a single bit. -/
theorem Codeword.xor_zero_apply {n : Nat} (a : Codeword n) (i : Fin n) :
    Codeword.xor a 0 i = a i :=
  (Codeword.xor_apply a 0 i).trans
    ((congrArg (a i + ·) (Codeword.zero_apply i)).trans (add_zero (a i)))

/-- *Pointwise XOR with zero on the left.*  `(0 xor a) i = a i`.
    Dual of `xor_zero_apply`; composes `xor_apply` + `zero_apply` +
    `zero_add` on the left summand. -/
theorem Codeword.zero_xor_apply {n : Nat} (a : Codeword n) (i : Fin n) :
    Codeword.xor 0 a i = a i :=
  (Codeword.xor_apply 0 a i).trans
    ((congrArg (· + a i) (Codeword.zero_apply i)).trans (zero_add (a i)))


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

/-! ## Syndrome decomposition -/

/-- *Linearity of the syndrome.*  Syndrome decomposes into the
    parity-check applied separately to the received vector and the
    noise candidate:

      `syndrome H Y N_g i = H * Y i + H * N_g i`.

    Direct application of `Matrix.mulVec_add` since
    `Codeword.xor` is pointwise `ZMod 2` addition. -/
theorem syndrome_decomp
    {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n)
    (i : Fin (n - k)) :
    syndrome H Y N_g i = H.matrix.mulVec Y i + H.matrix.mulVec N_g i :=
  congrFun (H.matrix.mulVec_add Y N_g) i

/-- *Syndrome on a codeword receiver.*  If the received vector `Y` is
    itself a codeword (zero parity-check image), the syndrome of any
    noise candidate reduces to the parity-check applied to the noise
    alone.  Composes `syndrome_decomp` with `zero_add`. -/
theorem syndrome_codeword
    {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n)
    (h : forall i, H.matrix.mulVec Y i = 0)
    (i : Fin (n - k)) :
    syndrome H Y N_g i = H.matrix.mulVec N_g i :=
  let step1 : syndrome H Y N_g i
              = H.matrix.mulVec Y i + H.matrix.mulVec N_g i :=
    syndrome_decomp H Y N_g i
  let step2 : H.matrix.mulVec Y i + H.matrix.mulVec N_g i
              = 0 + H.matrix.mulVec N_g i :=
    congrArg (· + H.matrix.mulVec N_g i) (h i)
  step1.trans (step2.trans (zero_add _))

/-- *Syndrome-zero equivalence under a codeword receiver.*  When `Y`
    is already a codeword, `syndromeZero H Y N_g` (the GRAND acceptance
    condition) is equivalent to `N_g` itself being a codeword.

    Captures a structural property of GRAND: if the receiver is in the
    valid codeword set, the only noise candidates that close into a
    codeword are themselves codewords. -/
theorem syndromeZero_iff_noise_codeword
    {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n)
    (h : forall i, H.matrix.mulVec Y i = 0) :
    syndromeZero H Y N_g <->
      forall (i : Fin (n - k)), H.matrix.mulVec N_g i = 0 :=
  ⟨fun hz i => (syndrome_codeword H Y N_g h i).symm.trans (hz i),
   fun hng i => (syndrome_codeword H Y N_g h i).trans (hng i)⟩


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

/-- *Cons case, zero-syndrome branch.*  When the head candidate has
    zero syndrome, `grandFind` returns `some (Y xor Ng)` immediately
    without examining the tail. -/
theorem grandFind_cons_zero_syndrome
    {n k : Nat} (H : ParityCheck n k) (Y Ng : Codeword n)
    (rest : List (Codeword n))
    (h : forall (i : Fin (n - k)),
          H.matrix.mulVec (Codeword.xor Y Ng) i = 0) :
    grandFind H Y (Ng :: rest) = some (Codeword.xor Y Ng) :=
  dif_pos h

/-- *Cons case, nonzero-syndrome branch.*  When the head candidate
    has nonzero syndrome, `grandFind` discards the head and recurses
    on the tail. -/
theorem grandFind_cons_nonzero_syndrome
    {n k : Nat} (H : ParityCheck n k) (Y Ng : Codeword n)
    (rest : List (Codeword n))
    (h : ¬ (forall (i : Fin (n - k)),
            H.matrix.mulVec (Codeword.xor Y Ng) i = 0)) :
    grandFind H Y (Ng :: rest) = grandFind H Y rest :=
  dif_neg h

/-- *Unified cons dispatch.*  Direct definitional characterization
    of `grandFind` on a cons list: the syndrome check on the head
    dispatches via an `if-then-else`.  Subsumes both
    `grandFind_cons_zero_syndrome` (then branch) and
    `grandFind_cons_nonzero_syndrome` (else branch) into one
    rewrite.  `rfl` directly. -/
theorem grandFind_cons_eq
    {n k : Nat} (H : ParityCheck n k) (Y Ng : Codeword n)
    (rest : List (Codeword n)) :
    grandFind H Y (Ng :: rest)
      = if _hp : forall (i : Fin (n - k)),
            H.matrix.mulVec (Codeword.xor Y Ng) i = 0 then
          some (Codeword.xor Y Ng)
        else
          grandFind H Y rest := rfl

/-- *Singleton candidate list.*  With exactly one noise candidate,
    `grandFind` reduces to a single syndrome check: return
    `some (Y xor Ng)` if the syndrome is zero, else `none`.  This is
    pure definitional unfolding: the cons arm fires, the else branch
    is `grandFind H Y []` which reduces to `none` by `grandFind_nil`. -/
theorem grandFind_singleton
    {n k : Nat} (H : ParityCheck n k) (Y Ng : Codeword n) :
    grandFind H Y [Ng]
      = if _hp : forall (i : Fin (n - k)),
            H.matrix.mulVec (Codeword.xor Y Ng) i = 0 then
          some (Codeword.xor Y Ng)
        else
          none :=
  rfl

/-- *List-extension stability.*  Appending more candidates to the end
    of the order list cannot undo an acceptance: if the original order
    finds `some c`, so does any extension.  Structural recursion on
    `order1` with `List.cons_append` (which is definitional) carrying
    the equality through. -/
theorem grandFind_append_left
    {n k : Nat} :
    forall (H : ParityCheck n k) (Y : Codeword n)
      (order1 : List (Codeword n)) (c : Codeword n),
      grandFind H Y order1 = some c ->
      forall (order2 : List (Codeword n)),
        grandFind H Y (order1 ++ order2) = some c
  | _, _, [],            _, h, _      => nomatch h
  | H, Y, (Ng :: rest1), c, h, order2 =>
      let hdite : (if _hp : forall (i : Fin (n - k)),
                    H.matrix.mulVec (Codeword.xor Y Ng) i = 0 then
                    some (Codeword.xor Y Ng)
                  else grandFind H Y rest1) = some c := h
      if hp : forall (j : Fin (n - k)),
          H.matrix.mulVec (Codeword.xor Y Ng) j = 0 then
        let hsome : some (Codeword.xor Y Ng) = some c :=
          (dif_pos hp).symm.trans hdite
        (dif_pos hp).trans hsome
      else
        let hrest1 : grandFind H Y rest1 = some c :=
          (dif_neg hp).symm.trans hdite
        let hrest1_app : grandFind H Y (rest1 ++ order2) = some c :=
          grandFind_append_left H Y rest1 c hrest1 order2
        (dif_neg hp).trans hrest1_app

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

/-- *Full soundness specification of `grandFind`.*  If `grandFind`
    returns `some c`, then `c` simultaneously
    (1) has zero syndrome (it is a codeword), and
    (2) is `Y xor Ng` for some candidate `Ng` from the input list.
    The conjunction captures the no-hallucination property: GRAND's
    output is always one of the proposed candidates, and that
    candidate is always a valid codeword. -/
theorem grandFind_sound
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) (c : Codeword n)
    (hfind : grandFind H Y order = some c) :
    (forall (i : Fin (n - k)), H.matrix.mulVec c i = 0)
    /\ (exists Ng, Ng ∈ order /\ c = Codeword.xor Y Ng) :=
  ⟨grandFind_zero_syndrome H Y order c hfind,
   grandFind_returns_xor H Y order c hfind⟩

/-! ## ML-optimality of GRAND -/

/-! ### `Codeword.xor` algebra (pointwise lifts of ZMod 2 arithmetic) -/

/-- `Codeword.xor` is just pointwise `ZMod 2` addition, lifted from
    `Pi.instAdd`.  The bespoke `Codeword.xor` and the generic `+`
    coincide. -/
theorem Codeword.xor_eq_add {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = a + b :=
  rfl

/-- *Subtraction is XOR.*  In `ZMod 2`, pointwise subtraction
    coincides with `Codeword.xor`.  Lifted from `CharTwo.sub_eq_add`. -/
theorem Codeword.sub_eq_xor {n : Nat} (a b : Codeword n) :
    a - b = Codeword.xor a b :=
  funext fun i => CharTwo.sub_eq_add (a i) (b i)

/-- *Negation is the identity.*  In `ZMod 2`, `-a = a` pointwise. -/
theorem Codeword.neg_eq_self {n : Nat} (a : Codeword n) :
    -a = a :=
  funext fun i => CharTwo.neg_eq (a i)

/-- *Pointwise self-negation in `ZMod 2`.*  `(-a) i = a i`.  One-liner
    via `congrFun` on `Codeword.neg_eq_self`. -/
theorem Codeword.neg_eq_self_apply {n : Nat} (a : Codeword n) (i : Fin n) :
    (-a) i = a i :=
  congrFun (Codeword.neg_eq_self a) i

/-- *XOR with negation equals XOR.*  In `ZMod 2`, `-b = b`, so XOR
    with `-b` is the same as XOR with `b`.  Composes
    `Codeword.neg_eq_self` under `Codeword.xor a` via `congrArg`. -/
theorem Codeword.xor_neg_eq_xor {n : Nat} (a b : Codeword n) :
    Codeword.xor a (-b) = Codeword.xor a b :=
  congrArg (Codeword.xor a) (Codeword.neg_eq_self b)

/-- *Pointwise XOR-with-negation equals XOR.*  `(Codeword.xor a (-b)) i
    = (Codeword.xor a b) i`.  One-liner via `congrFun` on
    `Codeword.xor_neg_eq_xor`. -/
theorem Codeword.xor_neg_eq_xor_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a (-b) i = Codeword.xor a b i :=
  congrFun (Codeword.xor_neg_eq_xor a b) i

/-- *XOR with negation on the left equals XOR.*  In `ZMod 2`, `-a = a`,
    so XOR of `-a` with `b` is the same as XOR of `a` with `b`.  Left
    dual of `Codeword.xor_neg_eq_xor`; composes `Codeword.neg_eq_self`
    under the `fun z => Codeword.xor z b` slot via `congrArg`. -/
theorem Codeword.neg_xor_eq_xor {n : Nat} (a b : Codeword n) :
    Codeword.xor (-a) b = Codeword.xor a b :=
  congrArg (fun z => Codeword.xor z b) (Codeword.neg_eq_self a)

/-- *Pointwise XOR-with-negation on the left equals XOR.*
    `(Codeword.xor (-a) b) i = (Codeword.xor a b) i`.  One-liner via
    `congrFun` on `Codeword.neg_xor_eq_xor`.  Left dual of
    `Codeword.xor_neg_eq_xor_apply`. -/
theorem Codeword.neg_xor_eq_xor_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (-a) b i = Codeword.xor a b i :=
  congrFun (Codeword.neg_xor_eq_xor a b) i

/-- *Double-negation XOR equals XOR.*  In `ZMod 2`, `-a = a` pointwise,
    so XOR of two negated codewords collapses to XOR of the originals.
    Chains `Codeword.neg_xor_eq_xor` (eliminating the left negation)
    with `Codeword.xor_neg_eq_xor` (eliminating the right negation). -/
theorem Codeword.neg_xor_neg_eq_xor {n : Nat} (a b : Codeword n) :
    Codeword.xor (-a) (-b) = Codeword.xor a b :=
  (Codeword.neg_xor_eq_xor a (-b)).trans (Codeword.xor_neg_eq_xor a b)

/-- *Pointwise double-negation XOR equals XOR.*  `(Codeword.xor (-a) (-b)) i
    = (Codeword.xor a b) i`.  One-liner via `congrFun` on
    `Codeword.neg_xor_neg_eq_xor`. -/
theorem Codeword.neg_xor_neg_eq_xor_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (-a) (-b) i = Codeword.xor a b i :=
  congrFun (Codeword.neg_xor_neg_eq_xor a b) i

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

/-- *Pointwise self-XOR vanishes.*  `(a xor a) i = 0`.  Direct
    `congrFun` of `xor_self` followed by the rfl `zero_apply`. -/
theorem Codeword.xor_self_apply {n : Nat} (a : Codeword n) (i : Fin n) :
    Codeword.xor a a i = 0 :=
  (congrFun (Codeword.xor_self a) i).trans (Codeword.zero_apply i)

/-- *XOR with own negation vanishes.*  `Codeword.xor a (-a) = 0`: in
    `ZMod 2`, `-a = a`, so XOR of any codeword with its own negation
    collapses to self-XOR and hence to zero. -/
theorem Codeword.xor_neg_self {n : Nat} (a : Codeword n) :
    Codeword.xor a (-a) = 0 :=
  (Codeword.xor_neg_eq_xor a a).trans (Codeword.xor_self a)

/-- *Left-negation XOR with self vanishes.*  `Codeword.xor (-a) a = 0`.
    Left dual of `Codeword.xor_neg_self`; chains `Codeword.neg_xor_eq_xor`
    with `Codeword.xor_self`. -/
theorem Codeword.neg_xor_self {n : Nat} (a : Codeword n) :
    Codeword.xor (-a) a = 0 :=
  (Codeword.neg_xor_eq_xor a a).trans (Codeword.xor_self a)

/-- *Pointwise XOR with own negation vanishes.*  `(Codeword.xor a (-a)) i = 0`.
    Direct `congrFun` of `xor_neg_self` followed by `zero_apply`. -/
theorem Codeword.xor_neg_self_apply {n : Nat} (a : Codeword n) (i : Fin n) :
    Codeword.xor a (-a) i = 0 :=
  (congrFun (Codeword.xor_neg_self a) i).trans (Codeword.zero_apply i)

/-- *Pointwise left-negation XOR with self vanishes.*  `(Codeword.xor (-a) a) i = 0`.
    Direct `congrFun` of `neg_xor_self` followed by `zero_apply`. -/
theorem Codeword.neg_xor_self_apply {n : Nat} (a : Codeword n) (i : Fin n) :
    Codeword.xor (-a) a i = 0 :=
  (congrFun (Codeword.neg_xor_self a) i).trans (Codeword.zero_apply i)

/-- *Negation swap across XOR.*  `Codeword.xor a (-b) = Codeword.xor (-a) b`:
    in `ZMod 2`, negation can hop between the two XOR arguments without
    changing the result. -/
theorem Codeword.xor_neg_eq_neg_xor {n : Nat} (a b : Codeword n) :
    Codeword.xor a (-b) = Codeword.xor (-a) b :=
  (Codeword.xor_neg_eq_xor a b).trans (Codeword.neg_xor_eq_xor a b).symm

/-- *Double-negation self-XOR vanishes.*  `Codeword.xor (-a) (-a) = 0`:
    in `ZMod 2`, negating both arguments collapses to plain `xor a a`,
    which is zero. -/
theorem Codeword.neg_xor_neg_self {n : Nat} (a : Codeword n) :
    Codeword.xor (-a) (-a) = 0 :=
  (Codeword.neg_xor_neg_eq_xor a a).trans (Codeword.xor_self a)

/-- *Pointwise double-negation self-XOR vanishes.*  `(Codeword.xor (-a) (-a)) i = 0`.
    Direct `congrFun` of `neg_xor_neg_self` followed by `zero_apply`. -/
theorem Codeword.neg_xor_neg_self_apply {n : Nat} (a : Codeword n) (i : Fin n) :
    Codeword.xor (-a) (-a) i = 0 :=
  (congrFun (Codeword.neg_xor_neg_self a) i).trans (Codeword.zero_apply i)

/-- *Pointwise negation swap across XOR.*  `(Codeword.xor a (-b)) i
    = (Codeword.xor (-a) b) i`.  One-liner via `congrFun` on
    `Codeword.xor_neg_eq_neg_xor`. -/
theorem Codeword.xor_neg_eq_neg_xor_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a (-b) i = Codeword.xor (-a) b i :=
  congrFun (Codeword.xor_neg_eq_neg_xor a b) i

/-- `a xor b = b xor a`.  Pointwise `add_comm`. -/
theorem Codeword.xor_comm {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = Codeword.xor b a :=
  funext fun i => add_comm (a i) (b i)

/-- `(a xor b) xor c = a xor (b xor c)`.  Pointwise `add_assoc`. -/
theorem Codeword.xor_assoc {n : Nat} (a b c : Codeword n) :
    Codeword.xor (Codeword.xor a b) c = Codeword.xor a (Codeword.xor b c) :=
  funext fun i => add_assoc (a i) (b i) (c i)

/-- *Pointwise XOR associativity.*  One-liner via `congrFun` on
    `xor_assoc`: at each index, the associativity holds. -/
theorem Codeword.xor_assoc_apply
    {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) c i
      = Codeword.xor a (Codeword.xor b c) i :=
  congrFun (Codeword.xor_assoc a b c) i

/-- *Pointwise XOR commutativity.*  One-liner via `congrFun` on
    `xor_comm`. -/
theorem Codeword.xor_comm_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a b i = Codeword.xor b a i :=
  congrFun (Codeword.xor_comm a b) i



/-- *Four-argument XOR shuffle.*  `(a xor b) xor (c xor d)
    = (a xor c) xor (b xor d)`: the abelian-group rearrangement
    swapping the inner-pair partition.  Pointwise `add_add_add_comm`. -/
theorem Codeword.xor_xor_comm {n : Nat} (a b c d : Codeword n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor c d)
      = Codeword.xor (Codeword.xor a c) (Codeword.xor b d) :=
  funext fun i => add_add_add_comm (a i) (b i) (c i) (d i)

/-- *Pointwise four-argument XOR shuffle.*  `congrFun` on
    `xor_xor_comm`: at each index, the four-arg rearrangement holds. -/
theorem Codeword.xor_xor_comm_apply
    {n : Nat} (a b c d : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor c d) i
      = Codeword.xor (Codeword.xor a c) (Codeword.xor b d) i :=
  congrFun (Codeword.xor_xor_comm a b c d) i

/-- *Left self-XOR cancels.*  `(a xor a) xor b = b`: a self-XOR
    prefix is the identity.  Direct composition of `xor_self` and
    `zero_xor`. -/
theorem Codeword.xor_self_left_eq {n : Nat} (a b : Codeword n) :
    Codeword.xor (Codeword.xor a a) b = b :=
  (congrArg (fun z => Codeword.xor z b) (Codeword.xor_self a)).trans
    (Codeword.zero_xor b)

/-- *Right self-XOR cancels.*  `a xor (b xor b) = a`: a self-XOR
    suffix is the identity.  Direct composition of `xor_self` and
    `xor_zero`. -/
theorem Codeword.xor_self_right_eq {n : Nat} (a b : Codeword n) :
    Codeword.xor a (Codeword.xor b b) = a :=
  (congrArg (Codeword.xor a) (Codeword.xor_self b)).trans
    (Codeword.xor_zero a)

/-- *Pointwise left self-XOR cancellation.*  `((a xor a) xor b) i = b i`. -/
theorem Codeword.xor_self_left_eq_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a a) b i = b i :=
  congrFun (Codeword.xor_self_left_eq a b) i

/-- *Pointwise right self-XOR cancellation.*  `(a xor (b xor b)) i = a i`. -/
theorem Codeword.xor_self_right_eq_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a (Codeword.xor b b) i = a i :=
  congrFun (Codeword.xor_self_right_eq a b) i

/-- *Common-suffix cancellation.*  `(a xor b) xor (c xor b) = a xor c`:
    a shared last argument on both sides drops out under XOR.  Dual
    of `xor_xor_xor_self`; derived from `xor_xor_comm` (regrouping
    `b xor b` together) followed by `xor_self` and `xor_zero`. -/
theorem Codeword.xor_xor_xor_self_right {n : Nat} (a b c : Codeword n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor c b)
      = Codeword.xor a c :=
  let s1 : Codeword.xor (Codeword.xor a b) (Codeword.xor c b)
         = Codeword.xor (Codeword.xor a c) (Codeword.xor b b) :=
    Codeword.xor_xor_comm a b c b
  let s2 : Codeword.xor (Codeword.xor a c) (Codeword.xor b b)
         = Codeword.xor (Codeword.xor a c) 0 :=
    congrArg (Codeword.xor (Codeword.xor a c)) (Codeword.xor_self b)
  let s3 : Codeword.xor (Codeword.xor a c) 0 = Codeword.xor a c :=
    Codeword.xor_zero _
  s1.trans (s2.trans s3)

/-- *Common-prefix cancellation.*  `(a xor b) xor (a xor c) = b xor c`:
    a shared first argument on both sides drops out under XOR.
    Derived from `xor_xor_comm` (rearranging to put `a xor a` together)
    followed by `xor_self` and `zero_xor`. -/
theorem Codeword.xor_xor_xor_self {n : Nat} (a b c : Codeword n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor a c)
      = Codeword.xor b c :=
  let s1 : Codeword.xor (Codeword.xor a b) (Codeword.xor a c)
         = Codeword.xor (Codeword.xor a a) (Codeword.xor b c) :=
    Codeword.xor_xor_comm a b a c
  let s2 : Codeword.xor (Codeword.xor a a) (Codeword.xor b c)
         = Codeword.xor 0 (Codeword.xor b c) :=
    congrArg (fun z => Codeword.xor z (Codeword.xor b c))
      (Codeword.xor_self a)
  let s3 : Codeword.xor 0 (Codeword.xor b c) = Codeword.xor b c :=
    Codeword.zero_xor _
  s1.trans (s2.trans s3)

/-- *Pointwise common-prefix cancellation.*  `congrFun` on
    `xor_xor_xor_self` gives `((a xor b) xor (a xor c)) i = (b xor c) i`. -/
theorem Codeword.xor_xor_xor_self_apply
    {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor a c) i
      = Codeword.xor b c i :=
  congrFun (Codeword.xor_xor_xor_self a b c) i

/-- *Pointwise common-suffix cancellation.*  `congrFun` on
    `xor_xor_xor_self_right` gives `((a xor b) xor (c xor b)) i = (a xor c) i`. -/
theorem Codeword.xor_xor_xor_self_right_apply
    {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor c b) i
      = Codeword.xor a c i :=
  congrFun (Codeword.xor_xor_xor_self_right a b c) i

/-- *Left transposition of XOR.*  `a xor (b xor c) = b xor (a xor c)`:
    the outer left arg swaps with the inner left arg.  Dual of
    `xor_right_comm`; derived from `xor_assoc.symm` + `xor_comm` on
    the outer pair + `xor_assoc`. -/
theorem Codeword.xor_left_comm {n : Nat} (a b c : Codeword n) :
    Codeword.xor a (Codeword.xor b c)
      = Codeword.xor b (Codeword.xor a c) :=
  let s1 : Codeword.xor a (Codeword.xor b c)
         = Codeword.xor (Codeword.xor a b) c :=
    (Codeword.xor_assoc a b c).symm
  let s2 : Codeword.xor (Codeword.xor a b) c
         = Codeword.xor (Codeword.xor b a) c :=
    congrArg (fun z => Codeword.xor z c) (Codeword.xor_comm a b)
  let s3 : Codeword.xor (Codeword.xor b a) c
         = Codeword.xor b (Codeword.xor a c) :=
    Codeword.xor_assoc b a c
  s1.trans (s2.trans s3)

/-- *Pointwise XOR left-commutativity.*  One-liner via `congrFun`
    on `xor_left_comm`. -/
theorem Codeword.xor_left_comm_apply
    {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor a (Codeword.xor b c) i
      = Codeword.xor b (Codeword.xor a c) i :=
  congrFun (Codeword.xor_left_comm a b c) i

/-- *Right transposition of XOR.*  `(a xor b) xor c = (a xor c) xor b`:
    the right-hand two arguments swap freely, the classic
    commutative-monoid `right_comm` law.  Derived from `xor_assoc`
    together with `xor_comm` on the inner pair. -/
theorem Codeword.xor_right_comm {n : Nat} (a b c : Codeword n) :
    Codeword.xor (Codeword.xor a b) c
      = Codeword.xor (Codeword.xor a c) b :=
  let s1 : Codeword.xor (Codeword.xor a b) c
         = Codeword.xor a (Codeword.xor b c) :=
    Codeword.xor_assoc a b c
  let s2 : Codeword.xor a (Codeword.xor b c)
         = Codeword.xor a (Codeword.xor c b) :=
    congrArg (Codeword.xor a) (Codeword.xor_comm b c)
  let s3 : Codeword.xor a (Codeword.xor c b)
         = Codeword.xor (Codeword.xor a c) b :=
    (Codeword.xor_assoc a c b).symm
  s1.trans (s2.trans s3)

/-- *Pointwise XOR right-commutativity.*  One-liner via `congrFun`
    on `xor_right_comm`.  Companion of `xor_left_comm_apply`. -/
theorem Codeword.xor_right_comm_apply
    {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) c i
      = Codeword.xor (Codeword.xor a c) b i :=
  congrFun (Codeword.xor_right_comm a b c) i

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

/-- *Pointwise XOR involution.*  `(Y xor (Y xor Ng)) i = Ng i`.
    One-liner via `congrFun` on `xor_xor_self`. -/
theorem Codeword.xor_xor_self_apply
    {n : Nat} (Y Ng : Codeword n) (i : Fin n) :
    Codeword.xor Y (Codeword.xor Y Ng) i = Ng i :=
  congrFun (Codeword.xor_xor_self Y Ng) i


/-- *Involution variant: outer-left matches inner-right.*
    `a xor (b xor a) = b`.  Complements `xor_xor_self` (outer-left
    matches inner-left) and `xor_xor_right` (outer-right matches
    inner-right).  Derived by `xor_comm` on the inner pair plus
    `xor_xor_self`. -/
theorem Codeword.xor_xor_left {n : Nat} (a b : Codeword n) :
    Codeword.xor a (Codeword.xor b a) = b :=
  let s1 : Codeword.xor a (Codeword.xor b a)
         = Codeword.xor a (Codeword.xor a b) :=
    congrArg (Codeword.xor a) (Codeword.xor_comm b a)
  s1.trans (Codeword.xor_xor_self a b)

/-- *Pointwise variant-left involution.*  `(a xor (b xor a)) i = b i`.
    One-liner via `congrFun` on `xor_xor_left`. -/
theorem Codeword.xor_xor_left_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a (Codeword.xor b a) i = b i :=
  congrFun (Codeword.xor_xor_left a b) i

/-- Right-cancel form: `(a xor b) xor b = a` in `ZMod 2`.  XOR is its
    own right inverse.  Proof: `xor_assoc` + `xor_self` + `xor_zero`. -/
theorem Codeword.xor_xor_right {n : Nat} (a b : Codeword n) :
    Codeword.xor (Codeword.xor a b) b = a :=
  let s1 : Codeword.xor (Codeword.xor a b) b
         = Codeword.xor a (Codeword.xor b b) :=
    Codeword.xor_assoc a b b
  let s2 : Codeword.xor a (Codeword.xor b b) = Codeword.xor a 0 :=
    congrArg (Codeword.xor a) (Codeword.xor_self b)
  s1.trans (s2.trans (Codeword.xor_zero a))

/-- *Pointwise XOR right cancellation.*  `((a xor b) xor b) i = a i`.
    One-liner via `congrFun` on `xor_xor_right`. -/
theorem Codeword.xor_xor_right_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) b i = a i :=
  congrFun (Codeword.xor_xor_right a b) i

/-- *Outer-right matches inner-left involution.*  `(a xor b) xor a = b`:
    completes the 2x2 grid of two-XOR self-cancellations alongside
    `xor_xor_self` (`a xor (a xor b) = b`, outer-left/inner-left),
    `xor_xor_left` (`a xor (b xor a) = b`, outer-left/inner-right), and
    `xor_xor_right` (`(a xor b) xor b = a`, outer-right/inner-right).
    Derived by `xor_right_comm` (swap outer-`b` and outer-`a`) followed
    by `xor_self_left_eq` (the resulting `(a xor a) xor b` prefix collapses
    to `b`). -/
theorem Codeword.xor_xor_self_left {n : Nat} (a b : Codeword n) :
    Codeword.xor (Codeword.xor a b) a = b :=
  (Codeword.xor_right_comm a b a).trans (Codeword.xor_self_left_eq a b)

/-- *Pointwise outer-right/inner-left involution.*  `((a xor b) xor a) i = b i`.
    One-liner via `congrFun` on `xor_xor_self_left`.  Completes the 2x2
    grid of pointwise self-cancellation forms alongside `xor_xor_self_apply`,
    `xor_xor_left_apply`, and `xor_xor_right_apply`. -/
theorem Codeword.xor_xor_self_left_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) a i = b i :=
  congrFun (Codeword.xor_xor_self_left a b) i

/-- *XOR transposition.*  `a xor b = c` iff `a = c xor b`.  The
    fundamental "move XOR to the other side" rule for ZMod 2. -/
theorem Codeword.xor_eq_iff_eq_xor {n : Nat} (a b c : Codeword n) :
    Codeword.xor a b = c <-> a = Codeword.xor c b :=
  ⟨fun h =>
    (Codeword.xor_xor_right a b).symm.trans
      (congrArg (fun x => Codeword.xor x b) h),
   fun h =>
    (congrArg (fun x => Codeword.xor x b) h).trans
      (Codeword.xor_xor_right c b)⟩

/-- *XOR transposition (left-arg move).*  `a xor b = c` iff
    `b = a xor c`: the LEFT argument moves to the right side
    instead of the right argument.  Dual of `xor_eq_iff_eq_xor`;
    derived via `xor_xor_self` (instead of `xor_xor_right`). -/
theorem Codeword.xor_eq_iff_left_eq_xor {n : Nat} (a b c : Codeword n) :
    Codeword.xor a b = c <-> b = Codeword.xor a c :=
  ⟨fun h =>
    (Codeword.xor_xor_self a b).symm.trans
      (congrArg (Codeword.xor a) h),
   fun h =>
    (congrArg (Codeword.xor a) h).trans
      (Codeword.xor_xor_self a c)⟩


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

/-- *Left cancellation iff.*  `a xor b = a xor c ↔ b = c`.  Iff form
    of `Codeword.xor_left_cancel`. -/
theorem Codeword.xor_left_eq_iff {n : Nat} (a b c : Codeword n) :
    Codeword.xor a b = Codeword.xor a c <-> b = c :=
  ⟨Codeword.xor_left_cancel, fun h => congrArg (Codeword.xor a) h⟩

/-- *Right cancellation iff.*  `a xor c = b xor c ↔ a = b`.  Iff form
    of `Codeword.xor_right_cancel`. -/
theorem Codeword.xor_right_eq_iff {n : Nat} (a b c : Codeword n) :
    Codeword.xor a c = Codeword.xor b c <-> a = b :=
  ⟨Codeword.xor_right_cancel, fun h => congrArg (fun x => Codeword.xor x c) h⟩

/-- *Double-cancellation iff.*  `(a xor b) xor c = (a xor d) xor c ↔
    b = d`: peel off the shared `c` via `xor_right_eq_iff`, then the
    shared `a` via `xor_left_eq_iff`.  Saves a two-step cancellation
    chain on every use. -/
theorem Codeword.xor_xor_eq_xor_xor_iff {n : Nat} (a b c d : Codeword n) :
    Codeword.xor (Codeword.xor a b) c = Codeword.xor (Codeword.xor a d) c
      <-> b = d :=
  (Codeword.xor_right_eq_iff (Codeword.xor a b)
      (Codeword.xor a d) c).trans
    (Codeword.xor_left_eq_iff a b d)

/-- *XOR is identity iff right argument is zero.*  `a xor b = a ↔ b = 0`.
    Captures the standard "XOR with 0 is no-op" characterisation. -/
theorem Codeword.xor_eq_self_iff {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = a <-> b = 0 :=
  ⟨fun h => Codeword.xor_left_cancel (h.trans (Codeword.xor_zero a).symm),
   fun h => (congrArg (Codeword.xor a) h).trans (Codeword.xor_zero a)⟩

/-- *XOR is identity iff left argument is zero.*  `a xor b = b ↔
    a = 0`.  Dual of `xor_eq_self_iff`. -/
theorem Codeword.xor_self_eq_iff_right {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = b <-> a = 0 :=
  ⟨fun h => Codeword.xor_right_cancel (h.trans (Codeword.zero_xor b).symm),
   fun h => (congrArg (fun x => Codeword.xor x b) h).trans (Codeword.zero_xor b)⟩

/-- *Four-argument XOR associativity.*  Fully left-associated XOR
    equals fully right-associated XOR. -/
theorem Codeword.xor_assoc4 {n : Nat} (a b c d : Codeword n) :
    Codeword.xor (Codeword.xor (Codeword.xor a b) c) d
      = Codeword.xor a (Codeword.xor b (Codeword.xor c d)) :=
  (Codeword.xor_assoc (Codeword.xor a b) c d).trans
    (Codeword.xor_assoc a b (Codeword.xor c d))

/-- *Pointwise four-argument XOR associativity.*  One-liner via
    `congrFun` on `xor_assoc4`: at each index, the fully left-associated
    XOR equals the fully right-associated XOR. -/
theorem Codeword.xor_assoc4_apply
    {n : Nat} (a b c d : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor (Codeword.xor a b) c) d i
      = Codeword.xor a (Codeword.xor b (Codeword.xor c d)) i :=
  congrFun (Codeword.xor_assoc4 a b c d) i

/-- *Paired self-XOR vanishes.*  `(a xor a) xor (b xor b) = 0`. -/
theorem Codeword.xor_self_xor_self {n : Nat} (a b : Codeword n) :
    Codeword.xor (Codeword.xor a a) (Codeword.xor b b) = 0 :=
  (Codeword.xor_self_left_eq a (Codeword.xor b b)).trans (Codeword.xor_self b)

/-- *Zero XOR zero is zero.*  Specialises `Codeword.zero_xor` at
    `a = 0`: absorbing-identity boundary case of XOR. -/
theorem Codeword.zero_xor_zero {n : Nat} :
    Codeword.xor (0 : Codeword n) (0 : Codeword n) = 0 :=
  Codeword.zero_xor 0

/-- *Pointwise paired self-XOR vanishes.*  `((a xor a) xor (b xor b)) i = 0`.
    Pointwise form of `xor_self_xor_self`. -/
theorem Codeword.xor_self_xor_self_apply
    {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a a) (Codeword.xor b b) i = 0 :=
  (congrFun (Codeword.xor_self_xor_self a b) i).trans (Codeword.zero_apply i)

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

/-- *XOR-zero characterises equality (reversed).*  `xor a b = 0 ↔ a = b`:
    `.symm` of `eq_iff_xor_eq_zero`. -/
theorem Codeword.xor_eq_zero_iff_eq {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = 0 <-> a = b :=
  (Codeword.eq_iff_xor_eq_zero a b).symm

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

/-- *`+` form of equality characterisation.*  `a + b = 0 ↔ a = b`
    (using `Codeword.xor = +` via `xor_eq_add`).  Convenient for
    downstream code expressing the equation in `+` form. -/
theorem Codeword.add_eq_zero_iff {n : Nat} (a b : Codeword n) :
    a + b = 0 <-> a = b :=
  (Codeword.eq_iff_xor_eq_zero a b).symm

/-- *Pairwise XOR equality rearrangement.*  `a xor b = c xor d ↔
    a xor c = b xor d`: the equation can be rearranged by moving
    `b` and `c` to the opposite sides.  Both directions convert to
    `(_ xor _) = 0` via `eq_iff_xor_eq_zero`, then `xor_xor_comm`
    rearranges the four arguments. -/
theorem Codeword.xor_eq_xor_iff_xor_eq_xor {n : Nat} (a b c d : Codeword n) :
    (Codeword.xor a b = Codeword.xor c d)
      <-> (Codeword.xor a c = Codeword.xor b d) :=
  ⟨fun h =>
    let s1 : Codeword.xor (Codeword.xor a c) (Codeword.xor b d)
           = Codeword.xor (Codeword.xor a b) (Codeword.xor c d) :=
      Codeword.xor_xor_comm a c b d
    let s2 : Codeword.xor (Codeword.xor a b) (Codeword.xor c d)
           = Codeword.xor (Codeword.xor c d) (Codeword.xor c d) :=
      congrArg (fun z => Codeword.xor z (Codeword.xor c d)) h
    let s3 : Codeword.xor (Codeword.xor c d) (Codeword.xor c d) = 0 :=
      Codeword.xor_self _
    let h_zero : Codeword.xor (Codeword.xor a c) (Codeword.xor b d) = 0 :=
      s1.trans (s2.trans s3)
    (Codeword.eq_iff_xor_eq_zero (Codeword.xor a c)
        (Codeword.xor b d)).mpr h_zero,
   fun h =>
    let s1 : Codeword.xor (Codeword.xor a b) (Codeword.xor c d)
           = Codeword.xor (Codeword.xor a c) (Codeword.xor b d) :=
      Codeword.xor_xor_comm a b c d
    let s2 : Codeword.xor (Codeword.xor a c) (Codeword.xor b d)
           = Codeword.xor (Codeword.xor b d) (Codeword.xor b d) :=
      congrArg (fun z => Codeword.xor z (Codeword.xor b d)) h
    let s3 : Codeword.xor (Codeword.xor b d) (Codeword.xor b d) = 0 :=
      Codeword.xor_self _
    let h_zero : Codeword.xor (Codeword.xor a b) (Codeword.xor c d) = 0 :=
      s1.trans (s2.trans s3)
    (Codeword.eq_iff_xor_eq_zero (Codeword.xor a b)
        (Codeword.xor c d)).mpr h_zero⟩

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

/-! ## Characterisation of `grandFind = none` -/

/-- *Forward direction.*  If `grandFind` returns `none`, every
    noise candidate in the input order has nonzero syndrome.
    Structural induction on the order list. -/
theorem grandFind_none_imp
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    forall (order : List (Codeword n)),
      grandFind H Y order = none ->
      forall Ng, Ng ∈ order ->
        ¬ (forall (i : Fin (n - k)),
            H.matrix.mulVec (Codeword.xor Y Ng) i = 0)
  | [],              _,     _,  hmem => (List.not_mem_nil hmem).elim
  | Ng_head :: rest, hnone, Ng, hmem =>
      let hdite : (if _hp : forall (i : Fin (n - k)),
                    H.matrix.mulVec (Codeword.xor Y Ng_head) i = 0 then
                    some (Codeword.xor Y Ng_head)
                  else grandFind H Y rest) = none := hnone
      if hp : forall (j : Fin (n - k)),
          H.matrix.mulVec (Codeword.xor Y Ng_head) j = 0 then
        nomatch (dif_pos hp).symm.trans hdite
      else
        let hrest : grandFind H Y rest = none :=
          (dif_neg hp).symm.trans hdite
        match hmem with
        | List.Mem.head _      => hp
        | List.Mem.tail _ hrm  => grandFind_none_imp H Y rest hrest Ng hrm

/-- *Backward direction.*  If every noise candidate in the order list
    has nonzero syndrome, `grandFind` returns `none`.  Structural
    induction on the order list. -/
theorem grandFind_none_mpr
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    forall (order : List (Codeword n)),
      (forall Ng, Ng ∈ order ->
        ¬ (forall (i : Fin (n - k)),
            H.matrix.mulVec (Codeword.xor Y Ng) i = 0)) ->
      grandFind H Y order = none
  | [],              _     => rfl
  | Ng_head :: rest, hnone =>
      let hno : ¬ (forall (i : Fin (n - k)),
                    H.matrix.mulVec (Codeword.xor Y Ng_head) i = 0) :=
        hnone Ng_head List.mem_cons_self
      let h_rest_none : grandFind H Y rest = none :=
        grandFind_none_mpr H Y rest
          (fun Ng hmem => hnone Ng (List.mem_cons_of_mem _ hmem))
      (dif_neg hno).trans h_rest_none

/-- *Characterisation of GRAND failure.*  `grandFind H Y order = none`
    iff every candidate noise vector in `order` has nonzero syndrome.
    Combines the two directions. -/
theorem grandFind_none_iff
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) :
    grandFind H Y order = none <->
      forall Ng, Ng ∈ order ->
        ¬ (forall (i : Fin (n - k)),
            H.matrix.mulVec (Codeword.xor Y Ng) i = 0) :=
  ⟨grandFind_none_imp H Y order, grandFind_none_mpr H Y order⟩

/-- *Singleton-list failure characterization.*  Specialises
    `grandFind_none_iff` to a length-1 candidate list: the GRAND
    search returns `none` iff the single candidate has nonzero
    syndrome.  Uses `List.mem_singleton` to collapse the universal
    quantifier over `[Ng]`. -/
theorem grandFind_singleton_none_iff
    {n k : Nat} (H : ParityCheck n k) (Y Ng : Codeword n) :
    grandFind H Y [Ng] = none
      <-> ¬ (forall (i : Fin (n - k)),
              H.matrix.mulVec (Codeword.xor Y Ng) i = 0) :=
  ⟨fun h =>
    (grandFind_none_iff H Y [Ng]).mp h Ng (List.mem_singleton.mpr rfl),
   fun h_nss =>
    (grandFind_none_iff H Y [Ng]).mpr fun Ng' h_mem =>
      let h_eq : Ng' = Ng := List.mem_singleton.mp h_mem
      h_eq ▸ h_nss⟩

/-! ## Syndrome boundary algebra -/

/-- *Syndrome with zero noise.*  The syndrome of a zero-noise
    candidate is the parity-check image of the received vector. -/
theorem syndrome_zero_noise
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) (i : Fin (n - k)) :
    syndrome H Y 0 i = H.matrix.mulVec Y i :=
  congrArg (fun v => H.matrix.mulVec v i) (Codeword.xor_zero Y)

/-- *Function-level syndrome with zero noise.*  Function-extensional
    form of `syndrome_zero_noise`: the entire syndrome map agrees
    with the parity-check image of the received vector. -/
theorem syndrome_zero_noise_funext
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    syndrome H Y 0 = fun i => H.matrix.mulVec Y i :=
  funext fun i => syndrome_zero_noise H Y i

/-- *Syndrome with zero received vector.*  The syndrome from a zero
    receiver is the parity-check image of the noise candidate alone. -/
theorem syndrome_zero_received
    {n k : Nat} (H : ParityCheck n k) (N_g : Codeword n) (i : Fin (n - k)) :
    syndrome H 0 N_g i = H.matrix.mulVec N_g i :=
  congrArg (fun v => H.matrix.mulVec v i) (Codeword.zero_xor N_g)

/-- *Function-level syndrome with zero received vector.*
    Function-extensional form of `syndrome_zero_received`. -/
theorem syndrome_zero_received_funext
    {n k : Nat} (H : ParityCheck n k) (N_g : Codeword n) :
    syndrome H 0 N_g = fun i => H.matrix.mulVec N_g i :=
  funext fun i => syndrome_zero_received H N_g i

/-- *Syndrome symmetry.*  Swapping the received vector and noise
    candidate leaves the syndrome unchanged.  Algebraically this is
    just `Codeword.xor_comm` lifted under the parity-check map. -/
theorem syndrome_comm
    {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n) (i : Fin (n - k)) :
    syndrome H Y N_g i = syndrome H N_g Y i :=
  congrArg (fun v => H.matrix.mulVec v i) (Codeword.xor_comm Y N_g)

/-- *Function-level syndrome symmetry.*  Function-extensional form
    of `syndrome_comm`: swapping the two arguments leaves the entire
    syndrome map unchanged. -/
theorem syndrome_comm_funext
    {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n) :
    syndrome H Y N_g = syndrome H N_g Y :=
  funext fun i => syndrome_comm H Y N_g i

/-- *Zero is a codeword.*  The all-zero codeword always lies in the
    kernel of `H.matrix.mulVec`, since multiplying any matrix by the
    zero vector gives zero. -/
theorem Codeword.zero_is_codeword {n k : Nat} (H : ParityCheck n k)
    (i : Fin (n - k)) :
    H.matrix.mulVec 0 i = 0 :=
  congrFun H.matrix.mulVec_zero i

/-- *Syndrome of self.*  When the noise candidate equals the received
    vector, the XOR cancels and the syndrome is zero on every
    coordinate.  Composes `Codeword.xor_self` (under the parity-check
    map via `congrArg`) with `Codeword.zero_is_codeword`. -/
theorem syndrome_self
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) (i : Fin (n - k)) :
    syndrome H Y Y i = 0 :=
  (congrArg (fun v => H.matrix.mulVec v i) (Codeword.xor_self Y)).trans
    (Codeword.zero_is_codeword H i)

/-- *Function-level self-syndrome vanishing.*  Function-extensional
    form of `syndrome_self`: the entire syndrome map `syndrome H Y Y`
    is the constantly-zero function.  `funext` lift of
    `syndrome_self` over the index variable. -/
theorem syndrome_self_funext
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    syndrome H Y Y = fun _ => 0 :=
  funext fun i => syndrome_self H Y i

/-- *Syndrome at zero/zero.*  With both received vector and noise
    candidate equal to the zero codeword, the syndrome vanishes
    pointwise.  Composes `syndrome_zero_noise` (collapses the noise
    side) with `Codeword.zero_is_codeword`. -/
theorem syndrome_zero_zero
    {n k : Nat} (H : ParityCheck n k) (i : Fin (n - k)) :
    syndrome H 0 0 i = 0 :=
  (syndrome_zero_noise H 0 i).trans (Codeword.zero_is_codeword H i)

/-- *Function-level syndrome at zero/zero.*  Function-extensional
    form of `syndrome_zero_zero`: the entire syndrome map is the
    constantly-zero function. -/
theorem syndrome_zero_zero_funext
    {n k : Nat} (H : ParityCheck n k) :
    syndrome H (0 : Codeword n) (0 : Codeword n) = fun _ => 0 :=
  funext fun i => syndrome_zero_zero H i

/-- *`syndromeZero` of self.*  Any received vector trivially
    satisfies the GRAND acceptance condition against itself as
    noise candidate: `Y xor Y = 0`, and the zero codeword has zero
    syndrome.  Pointwise lift of `syndrome_self`. -/
theorem syndromeZero_self
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    syndromeZero H Y Y :=
  fun i => syndrome_self H Y i

/-- *`syndromeZero` at zero/zero.*  With both received vector and
    noise candidate equal to the zero codeword, the GRAND acceptance
    condition trivially holds: every coordinate of the syndrome
    vanishes.  Pointwise lift of `syndrome_zero_zero`. -/
theorem syndromeZero_zero_zero
    {n k : Nat} (H : ParityCheck n k) :
    syndromeZero H (0 : Codeword n) (0 : Codeword n) :=
  fun i => syndrome_zero_zero H i

/-- *Alternative `syndromeZero` at zero/zero via self-acceptance.*
    Specialises `syndromeZero_self` to `Y = 0`. -/
theorem syndromeZero_self_of_zero
    {n k : Nat} (H : ParityCheck n k) :
    syndromeZero H (0 : Codeword n) (0 : Codeword n) :=
  syndromeZero_self H 0

/-- *`syndromeZero` symmetry.*  Swapping the received vector and the
    noise candidate preserves the GRAND acceptance condition.
    Pointwise lift of `syndrome_comm`. -/
theorem syndromeZero_symm
    {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n) :
    syndromeZero H Y N_g <-> syndromeZero H N_g Y :=
  ⟨fun h i => (syndrome_comm H Y N_g i).symm.trans (h i),
   fun h i => (syndrome_comm H Y N_g i).trans (h i)⟩

/-- *Syndrome under XOR-cancel cycle.*  Setting the noise candidate
    to `Y xor c` collapses the syndrome to the parity-check image of
    `c` alone: `Y xor (Y xor c) = c` under XOR involution.  Composes
    `Codeword.xor_xor_self` under `H.matrix.mulVec`. -/
theorem syndrome_xor_self_noise
    {n k : Nat} (H : ParityCheck n k) (Y c : Codeword n) (i : Fin (n - k)) :
    syndrome H Y (Codeword.xor Y c) i = H.matrix.mulVec c i :=
  congrArg (fun v => H.matrix.mulVec v i) (Codeword.xor_xor_self Y c)

/-- *Function-level XOR-cancel cycle on the noise side.*  Function-
    extensional form of `syndrome_xor_self_noise`. -/
theorem syndrome_xor_self_noise_funext
    {n k : Nat} (H : ParityCheck n k) (Y c : Codeword n) :
    syndrome H Y (Codeword.xor Y c) = fun i => H.matrix.mulVec c i :=
  funext fun i => syndrome_xor_self_noise H Y c i

/-- *Syndrome under XOR-cancel cycle on the receiver side.*  Dual of
    `syndrome_xor_self_noise`: setting the received vector to
    `N_g xor c` collapses the syndrome to the parity-check image of
    `c` alone.  Algebraically `(N_g xor c) xor N_g = c` via
    `xor_comm` followed by `xor_xor_self`. -/
theorem syndrome_xor_self_received
    {n k : Nat} (H : ParityCheck n k) (N_g c : Codeword n)
    (i : Fin (n - k)) :
    syndrome H (Codeword.xor N_g c) N_g i = H.matrix.mulVec c i :=
  let step : Codeword.xor (Codeword.xor N_g c) N_g = c :=
    (Codeword.xor_comm (Codeword.xor N_g c) N_g).trans
      (Codeword.xor_xor_self N_g c)
  congrArg (fun v => H.matrix.mulVec v i) step

/-- *Function-level XOR-cancel cycle on the receiver side.*
    Function-extensional form of `syndrome_xor_self_received`. -/
theorem syndrome_xor_self_received_funext
    {n k : Nat} (H : ParityCheck n k) (N_g c : Codeword n) :
    syndrome H (Codeword.xor N_g c) N_g = fun i => H.matrix.mulVec c i :=
  funext fun i => syndrome_xor_self_received H N_g c i

/-- *Acceptance under noise XOR-cancel cycle.*  Lifts
    `syndrome_xor_self_noise` to the `syndromeZero` predicate: the
    GRAND acceptance condition with noise candidate `Y xor c` is
    equivalent to `c` itself being a codeword.  Both directions
    chain through the per-coordinate identity. -/
theorem syndromeZero_xor_self_noise_iff
    {n k : Nat} (H : ParityCheck n k) (Y c : Codeword n) :
    syndromeZero H Y (Codeword.xor Y c)
      <-> forall (i : Fin (n - k)), H.matrix.mulVec c i = 0 :=
  ⟨fun h i => (syndrome_xor_self_noise H Y c i).symm.trans (h i),
   fun h i => (syndrome_xor_self_noise H Y c i).trans (h i)⟩

/-- *Acceptance under receiver XOR-cancel cycle.*  Dual of
    `syndromeZero_xor_self_noise_iff`: lifts
    `syndrome_xor_self_received` to the `syndromeZero` predicate. -/
theorem syndromeZero_xor_self_received_iff
    {n k : Nat} (H : ParityCheck n k) (N_g c : Codeword n) :
    syndromeZero H (Codeword.xor N_g c) N_g
      <-> forall (i : Fin (n - k)), H.matrix.mulVec c i = 0 :=
  ⟨fun h i => (syndrome_xor_self_received H N_g c i).symm.trans (h i),
   fun h i => (syndrome_xor_self_received H N_g c i).trans (h i)⟩

/-- *Parity-check map is XOR-linear.*  `H * (a xor b) = H * a + H * b`:
    rewrites `xor` to `+` (via `xor_eq_add`) and then applies
    `Matrix.mulVec_add`. -/
theorem Codeword.mulVec_xor {n k : Nat} (H : ParityCheck n k)
    (a b : Codeword n) :
    H.matrix.mulVec (Codeword.xor a b)
      = H.matrix.mulVec a + H.matrix.mulVec b :=
  let h_add : H.matrix.mulVec (Codeword.xor a b)
            = H.matrix.mulVec (a + b) :=
    congrArg H.matrix.mulVec (Codeword.xor_eq_add a b)
  h_add.trans (H.matrix.mulVec_add a b)

/-- *Pointwise XOR linearity of the parity-check map.*  `congrFun` on
    `mulVec_xor` gives the per-coordinate form
    `H * (a xor b) i = H * a i + H * b i`. -/
theorem Codeword.mulVec_xor_apply {n k : Nat} (H : ParityCheck n k)
    (a b : Codeword n) (i : Fin (n - k)) :
    H.matrix.mulVec (Codeword.xor a b) i
      = H.matrix.mulVec a i + H.matrix.mulVec b i :=
  congrFun (Codeword.mulVec_xor H a b) i

/-- *Codeword-left shift is invisible under the parity-check map.*
    If `a` is a codeword (zero parity-check image), then
    `H * (a xor b) = H * b` for any `b`.  Derived from `mulVec_xor`
    plus `ha i` and `zero_add`. -/
theorem Codeword.mulVec_xor_codeword_left {n k : Nat} (H : ParityCheck n k)
    {a b : Codeword n}
    (ha : forall (i : Fin (n - k)), H.matrix.mulVec a i = 0)
    (i : Fin (n - k)) :
    H.matrix.mulVec (Codeword.xor a b) i = H.matrix.mulVec b i :=
  let s1 : H.matrix.mulVec (Codeword.xor a b) i
         = H.matrix.mulVec a i + H.matrix.mulVec b i :=
    congrFun (Codeword.mulVec_xor H a b) i
  let s2 : H.matrix.mulVec a i + H.matrix.mulVec b i
         = 0 + H.matrix.mulVec b i :=
    congrArg (· + H.matrix.mulVec b i) (ha i)
  let s3 : (0 : ZMod 2) + H.matrix.mulVec b i = H.matrix.mulVec b i :=
    zero_add _
  s1.trans (s2.trans s3)

/-- *Codeword-right shift is invisible under the parity-check map.*
    If `b` is a codeword (zero parity-check image), then
    `H * (a xor b) = H * a` for any `a`.  Dual of
    `mulVec_xor_codeword_left`; same three-step structure with
    `hb i` and `add_zero` on the right summand. -/
theorem Codeword.mulVec_xor_codeword_right {n k : Nat} (H : ParityCheck n k)
    {a b : Codeword n}
    (hb : forall (i : Fin (n - k)), H.matrix.mulVec b i = 0)
    (i : Fin (n - k)) :
    H.matrix.mulVec (Codeword.xor a b) i = H.matrix.mulVec a i :=
  let s1 : H.matrix.mulVec (Codeword.xor a b) i
         = H.matrix.mulVec a i + H.matrix.mulVec b i :=
    congrFun (Codeword.mulVec_xor H a b) i
  let s2 : H.matrix.mulVec a i + H.matrix.mulVec b i
         = H.matrix.mulVec a i + 0 :=
    congrArg (H.matrix.mulVec a i + ·) (hb i)
  let s3 : H.matrix.mulVec a i + (0 : ZMod 2) = H.matrix.mulVec a i :=
    add_zero _
  s1.trans (s2.trans s3)

/-- *Codewords are closed under XOR.*  If `a` and `b` are both
    codewords (each in the kernel of `H.matrix.mulVec`), then their
    XOR `a xor b` is also a codeword.  This is the standard
    "linear code is a subspace" property: `Matrix.mulVec` is linear,
    so its kernel is closed under addition (= XOR in ZMod 2). -/
theorem Codeword.xor_codeword_is_codeword {n k : Nat} (H : ParityCheck n k)
    {a b : Codeword n}
    (ha : forall (i : Fin (n - k)), H.matrix.mulVec a i = 0)
    (hb : forall (i : Fin (n - k)), H.matrix.mulVec b i = 0) :
    forall (i : Fin (n - k)),
      H.matrix.mulVec (Codeword.xor a b) i = 0 :=
  fun i =>
    (congrFun (H.matrix.mulVec_add a b) i).trans
      ((congrArg₂ (· + ·) (ha i) (hb i)).trans (add_zero 0))

/-- *Codeword-shift preserves codeword-membership.*  Given a fixed
    codeword `a`, the XOR-shift `b ↦ a xor b` is a bijection on the
    codeword set: `a xor b` is a codeword iff `b` is.  The forward
    direction uses `mulVec_xor_codeword_left` to extract
    `H * b = H * (a xor b) = 0`; the backward direction is
    `xor_codeword_is_codeword`. -/
theorem Codeword.xor_codeword_iff_codeword_of_left {n k : Nat}
    (H : ParityCheck n k) {a b : Codeword n}
    (ha : forall (i : Fin (n - k)), H.matrix.mulVec a i = 0) :
    (forall (i : Fin (n - k)),
        H.matrix.mulVec (Codeword.xor a b) i = 0)
      <-> (forall (i : Fin (n - k)), H.matrix.mulVec b i = 0) :=
  ⟨fun hxor i =>
    let s : H.matrix.mulVec (Codeword.xor a b) i = H.matrix.mulVec b i :=
      Codeword.mulVec_xor_codeword_left H ha i
    s.symm.trans (hxor i),
   fun hb => Codeword.xor_codeword_is_codeword H ha hb⟩

/-- *Right-side codeword-shift preserves codeword-membership.*  Dual
    of `xor_codeword_iff_codeword_of_left`: given a fixed codeword
    `b`, the XOR-shift `a ↦ a xor b` is a bijection on the codeword
    set.  Forward via `mulVec_xor_codeword_right`; backward via
    `xor_codeword_is_codeword`. -/
theorem Codeword.xor_codeword_iff_codeword_of_right {n k : Nat}
    (H : ParityCheck n k) {a b : Codeword n}
    (hb : forall (i : Fin (n - k)), H.matrix.mulVec b i = 0) :
    (forall (i : Fin (n - k)),
        H.matrix.mulVec (Codeword.xor a b) i = 0)
      <-> (forall (i : Fin (n - k)), H.matrix.mulVec a i = 0) :=
  ⟨fun hxor i =>
    let s : H.matrix.mulVec (Codeword.xor a b) i = H.matrix.mulVec a i :=
      Codeword.mulVec_xor_codeword_right H hb i
    s.symm.trans (hxor i),
   fun ha => Codeword.xor_codeword_is_codeword H ha hb⟩

/-- *Syndrome is invariant under codeword shifts of the receiver.*  If
    `c` is a codeword (zero parity-check image), then XOR-shifting the
    received vector by `c` leaves the syndrome unchanged.  Captures
    the standard "coset" property of syndrome decoding: codewords with
    the same syndrome form a coset of the codebook. -/
theorem syndrome_invariant_under_codeword
    {n k : Nat} (H : ParityCheck n k) (Y N c : Codeword n)
    (h_c : forall (i : Fin (n - k)), H.matrix.mulVec c i = 0)
    (i : Fin (n - k)) :
    syndrome H (Codeword.xor Y c) N i = syndrome H Y N i :=
  let step_assoc : Codeword.xor (Codeword.xor Y c) N
                 = Codeword.xor (Codeword.xor Y N) c :=
    (Codeword.xor_assoc Y c N).trans
      ((congrArg (Codeword.xor Y) (Codeword.xor_comm c N)).trans
        (Codeword.xor_assoc Y N c).symm)
  let step1 : syndrome H (Codeword.xor Y c) N i
            = H.matrix.mulVec (Codeword.xor (Codeword.xor Y N) c) i :=
    congrArg (fun v => H.matrix.mulVec v i) step_assoc
  let step2 : H.matrix.mulVec (Codeword.xor (Codeword.xor Y N) c) i
            = H.matrix.mulVec (Codeword.xor Y N) i + H.matrix.mulVec c i :=
    congrFun (H.matrix.mulVec_add (Codeword.xor Y N) c) i
  let step3 : H.matrix.mulVec (Codeword.xor Y N) i + H.matrix.mulVec c i
            = H.matrix.mulVec (Codeword.xor Y N) i + 0 :=
    congrArg (H.matrix.mulVec (Codeword.xor Y N) i + ·) (h_c i)
  step1.trans (step2.trans (step3.trans (add_zero _)))

/-- *Zero-noise syndrome-zero ↔ codeword.*  With `N = 0`, the syndrome
    becomes `H * (Y xor 0) = H * Y`, so `syndromeZero H Y 0` is
    exactly the assertion that `Y` lies in the codebook. -/
theorem syndromeZero_zero_noise_iff_codeword
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    syndromeZero H Y 0
      <-> forall (i : Fin (n - k)), H.matrix.mulVec Y i = 0 :=
  ⟨fun h i =>
    let s : syndrome H Y 0 i = H.matrix.mulVec Y i :=
      congrArg (fun v => H.matrix.mulVec v i) (Codeword.xor_zero Y)
    s.symm.trans (h i),
   fun h i =>
    let s : syndrome H Y 0 i = H.matrix.mulVec Y i :=
      congrArg (fun v => H.matrix.mulVec v i) (Codeword.xor_zero Y)
    s.trans (h i)⟩

/-- *Zero-received syndrome-zero ↔ noise codeword.*  Dual of
    `syndromeZero_zero_noise_iff_codeword`: with `Y = 0`, the
    syndrome reduces to `H * N`, so `syndromeZero H 0 N` is exactly
    the assertion that `N` is a codeword. -/
theorem syndromeZero_zero_received_iff_codeword
    {n k : Nat} (H : ParityCheck n k) (N : Codeword n) :
    syndromeZero H 0 N
      <-> forall (i : Fin (n - k)), H.matrix.mulVec N i = 0 :=
  ⟨fun h i =>
    let s : syndrome H 0 N i = H.matrix.mulVec N i :=
      congrArg (fun v => H.matrix.mulVec v i) (Codeword.zero_xor N)
    s.symm.trans (h i),
   fun h i =>
    let s : syndrome H 0 N i = H.matrix.mulVec N i :=
      congrArg (fun v => H.matrix.mulVec v i) (Codeword.zero_xor N)
    s.trans (h i)⟩

/-- *Syndrome is invariant under codeword shifts of the noise.*
    Symmetric to `syndrome_invariant_under_codeword`: XOR-shifting the
    noise candidate `N` by a codeword `c` leaves the syndrome
    unchanged.  Cleaner two-step proof using
    `mulVec_xor_codeword_right`: re-associate to bring `c` to the
    right of `(Y xor N)`, then drop it. -/
theorem syndrome_invariant_under_codeword_noise
    {n k : Nat} (H : ParityCheck n k) (Y N c : Codeword n)
    (h_c : forall (i : Fin (n - k)), H.matrix.mulVec c i = 0)
    (i : Fin (n - k)) :
    syndrome H Y (Codeword.xor N c) i = syndrome H Y N i :=
  let assoc : Codeword.xor Y (Codeword.xor N c)
            = Codeword.xor (Codeword.xor Y N) c :=
    (Codeword.xor_assoc Y N c).symm
  let step1 : syndrome H Y (Codeword.xor N c) i
            = H.matrix.mulVec (Codeword.xor (Codeword.xor Y N) c) i :=
    congrArg (fun v => H.matrix.mulVec v i) assoc
  let step2 : H.matrix.mulVec (Codeword.xor (Codeword.xor Y N) c) i
            = H.matrix.mulVec (Codeword.xor Y N) i :=
    Codeword.mulVec_xor_codeword_right H h_c i
  step1.trans step2

/-- *`syndromeZero` is invariant under codeword shifts of the receiver.*
    Lifts `syndrome_invariant_under_codeword` to the `syndromeZero`
    predicate.  Dual of `syndromeZero_xor_codeword_noise_iff`;
    same iff-chaining structure. -/
theorem syndromeZero_xor_codeword_received_iff
    {n k : Nat} (H : ParityCheck n k) (Y N c : Codeword n)
    (h_c : forall (i : Fin (n - k)), H.matrix.mulVec c i = 0) :
    syndromeZero H (Codeword.xor Y c) N <-> syndromeZero H Y N :=
  ⟨fun h i =>
    let s : syndrome H (Codeword.xor Y c) N i = syndrome H Y N i :=
      syndrome_invariant_under_codeword H Y N c h_c i
    s.symm.trans (h i),
   fun h i =>
    let s : syndrome H (Codeword.xor Y c) N i = syndrome H Y N i :=
      syndrome_invariant_under_codeword H Y N c h_c i
    s.trans (h i)⟩

/-- *`syndromeZero` is invariant under codeword shifts of the noise.*
    Lifts `syndrome_invariant_under_codeword_noise` to the
    `syndromeZero` predicate: XOR-shifting the noise candidate by a
    codeword preserves the acceptance condition.  Both iff
    directions chain through the entry-level invariance. -/
theorem syndromeZero_xor_codeword_noise_iff
    {n k : Nat} (H : ParityCheck n k) (Y N c : Codeword n)
    (h_c : forall (i : Fin (n - k)), H.matrix.mulVec c i = 0) :
    syndromeZero H Y (Codeword.xor N c) <-> syndromeZero H Y N :=
  ⟨fun h i =>
    let s : syndrome H Y (Codeword.xor N c) i = syndrome H Y N i :=
      syndrome_invariant_under_codeword_noise H Y N c h_c i
    s.symm.trans (h i),
   fun h i =>
    let s : syndrome H Y (Codeword.xor N c) i = syndrome H Y N i :=
      syndrome_invariant_under_codeword_noise H Y N c h_c i
    s.trans (h i)⟩

/-- *`syndromeZero` is invariant under simultaneous codeword shifts.*
    Given codewords `c_r` and `c_n`, XOR-shifting the receiver by
    `c_r` and the noise candidate by `c_n` leaves the acceptance
    condition unchanged.  Composes `syndromeZero_xor_codeword_received_iff`
    (drops `c_r`) with `syndromeZero_xor_codeword_noise_iff` (drops
    `c_n`) via `Iff.trans`. -/
theorem syndromeZero_xor_codeword_both_iff
    {n k : Nat} (H : ParityCheck n k) (Y N c_r c_n : Codeword n)
    (h_cr : forall (i : Fin (n - k)), H.matrix.mulVec c_r i = 0)
    (h_cn : forall (i : Fin (n - k)), H.matrix.mulVec c_n i = 0) :
    syndromeZero H (Codeword.xor Y c_r) (Codeword.xor N c_n)
      <-> syndromeZero H Y N :=
  (syndromeZero_xor_codeword_received_iff H Y
      (Codeword.xor N c_n) c_r h_cr).trans
    (syndromeZero_xor_codeword_noise_iff H Y N c_n h_cn)

/-- *Syndrome-zero equivalence under a codeword noise candidate.*
    Dual of `syndromeZero_iff_noise_codeword`: when the noise
    candidate `N_g` is a codeword, the syndrome reduces to `H * Y`,
    so the GRAND acceptance condition is equivalent to `Y` itself
    being a codeword.  Two-step proof via
    `Codeword.mulVec_xor_codeword_right` in both directions. -/
theorem syndromeZero_iff_received_codeword
    {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n)
    (h : forall i, H.matrix.mulVec N_g i = 0) :
    syndromeZero H Y N_g <->
      forall (i : Fin (n - k)), H.matrix.mulVec Y i = 0 :=
  ⟨fun hz i =>
    let s : syndrome H Y N_g i = H.matrix.mulVec Y i :=
      Codeword.mulVec_xor_codeword_right H h i
    s.symm.trans (hz i),
   fun hy i =>
    let s : syndrome H Y N_g i = H.matrix.mulVec Y i :=
      Codeword.mulVec_xor_codeword_right H h i
    s.trans (hy i)⟩

/-- *Syndrome-zero is the codeword condition on `Y xor N`.*
    Unconditional reformulation: by definition `syndrome H Y N i =
    H.matrix.mulVec (Codeword.xor Y N) i`, so `syndromeZero H Y N`
    is exactly the assertion that `Y xor N` lies in the codebook.
    Direct `Iff.rfl` (no preconditions, no codeword hypotheses).
    Subsumes the conditioned forms `syndromeZero_iff_noise_codeword`
    and `syndromeZero_iff_received_codeword` in the general case. -/
theorem syndromeZero_iff_xor_codeword
    {n k : Nat} (H : ParityCheck n k) (Y N : Codeword n) :
    syndromeZero H Y N <->
      forall (i : Fin (n - k)),
        H.matrix.mulVec (Codeword.xor Y N) i = 0 :=
  Iff.rfl

/-- *GRAND output with noise recovery.*  Extends `grandFind_sound`
    with the noise-recovery identity `Y xor c = Ng`: the guessed
    noise candidate is recoverable from the decoder output and the
    receiver via XOR.  Composes `grandFind_sound` with
    `Codeword.xor_xor_self` (XOR involution). -/
theorem grandFind_output_characterization
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) (c : Codeword n)
    (hfind : grandFind H Y order = some c) :
    (forall (i : Fin (n - k)), H.matrix.mulVec c i = 0)
    /\ (exists Ng, Ng ∈ order /\ c = Codeword.xor Y Ng
                /\ Codeword.xor Y c = Ng) :=
  let ⟨h_syn, ⟨Ng, h_mem, h_eq⟩⟩ := grandFind_sound H Y order c hfind
  ⟨h_syn, Ng, h_mem, h_eq, h_eq ▸ Codeword.xor_xor_self Y Ng⟩

/-- *Append with failed prefix.*  When `grandFind H Y order1` returns
    `none` (every candidate in `order1` has nonzero syndrome), then
    `grandFind H Y (order1 ++ order2) = grandFind H Y order2`: the
    suffix takes over once the prefix is exhausted.  Structural
    recursion on `order1` with case-split on the head's syndrome via
    `grandFind_cons_zero_syndrome` / `_cons_nonzero_syndrome`. -/
theorem grandFind_append_none
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    forall (order1 : List (Codeword n)),
      grandFind H Y order1 = none ->
      forall (order2 : List (Codeword n)),
        grandFind H Y (order1 ++ order2) = grandFind H Y order2
  | [],         _      => fun _ => rfl
  | Ng :: rest, h_none => fun order2 =>
      if h_synd : forall (i : Fin (n - k)),
                    H.matrix.mulVec (Codeword.xor Y Ng) i = 0 then
        let h_some : grandFind H Y (Ng :: rest)
                   = some (Codeword.xor Y Ng) :=
          grandFind_cons_zero_syndrome H Y Ng rest h_synd
        nomatch h_some.symm.trans h_none
      else
        let h_rest_none : grandFind H Y rest = none :=
          (grandFind_cons_nonzero_syndrome H Y Ng rest h_synd).symm.trans
            h_none
        let h_cons_append :
            grandFind H Y ((Ng :: rest) ++ order2)
              = grandFind H Y (rest ++ order2) :=
          grandFind_cons_nonzero_syndrome H Y Ng (rest ++ order2) h_synd
        h_cons_append.trans
          (grandFind_append_none H Y rest h_rest_none order2)

/-- *Combined append dispatch.*  The append behavior of `grandFind`
    is fully determined by the prefix result: if the prefix yields
    `some c`, the append yields `some c`; if the prefix yields
    `none`, the append yields the suffix's own result.  Composes
    `grandFind_append_left` and `grandFind_append_none` into a
    single rewrite via `match h : ... with`. -/
theorem grandFind_append_eq
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order1 order2 : List (Codeword n)) :
    grandFind H Y (order1 ++ order2)
      = match grandFind H Y order1 with
        | some c => some c
        | none   => grandFind H Y order2 :=
  match h : grandFind H Y order1 with
  | some c => grandFind_append_left H Y order1 c h order2
  | none   => grandFind_append_none H Y order1 h order2

/-- *GRAND output syndrome decomposition.*  When `grandFind` returns
    `some c`, there exists a noise candidate `Ng` in the order list
    such that `c = Y xor Ng` AND the per-coordinate sum
    `H * Y i + H * Ng i = 0`.  Composes three theorems:
    `grandFind_returns_xor`, `grandFind_syndromeZero`, and
    `Codeword.mulVec_xor` (linearity of the parity-check map). -/
theorem grandFind_output_syndrome_decomp
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) (c : Codeword n)
    (hfind : grandFind H Y order = some c) :
    exists Ng, Ng ∈ order /\ c = Codeword.xor Y Ng /\
      forall (i : Fin (n - k)),
        H.matrix.mulVec Y i + H.matrix.mulVec Ng i = 0 :=
  let ⟨Ng, hmem, heq⟩ := grandFind_returns_xor H Y order c hfind
  let hsyn := grandFind_syndromeZero H Y order c hfind
  ⟨Ng, hmem, heq, fun i =>
    let step1 : H.matrix.mulVec c i = 0 := hsyn i
    let step3 : H.matrix.mulVec (Codeword.xor Y Ng) i = 0 :=
      heq ▸ step1
    let step4 : H.matrix.mulVec Y i + H.matrix.mulVec Ng i
              = H.matrix.mulVec (Codeword.xor Y Ng) i :=
      (congrFun (Codeword.mulVec_xor H Y Ng) i).symm
    step4.trans step3⟩

/-- *Self-syndrome agrees with zero/zero syndrome.* -/
theorem syndrome_self_eq_zero_zero_funext
    {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    syndrome H Y Y = syndrome H (0 : Codeword n) (0 : Codeword n) :=
  (syndrome_self_funext H Y).trans (funext fun i => (syndrome_zero_zero H i)).symm

end Section04
end OrbgrandAi
