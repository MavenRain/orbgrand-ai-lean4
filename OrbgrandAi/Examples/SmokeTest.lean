import OrbgrandAi

/-!
# OrbgrandAi.Examples.SmokeTest

End-to-end smoke test exercising the public API of `OrbgrandAi`.
Each `example` invokes a proved theorem to check that its type
signature is usable from outside the library and that the helper
lemmas compose cleanly.

This file is not part of the core library proofs; it exists as a
sanity check and a reading aid for new users.  If any `example`
below fails to type-check, the corresponding theorem's API has
changed and downstream uses will break.
-/

set_option autoImplicit false

namespace OrbgrandAi.Examples.SmokeTest

open OrbgrandAi.Section02 OrbgrandAi.Section03 OrbgrandAi.Section04 OrbgrandAi.Section06

/-! ## Section II.  Channel-model lemmas -/

/-- Dicode channel is causal (entries `i < j` vanish). -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).causal :=
  dicode_causal sigma rho

/-- Dicode channel has bandwidth at most `1`. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 1 :=
  dicode_bandwidth sigma rho

/-- Dicode zero-forcing equalisation produces the Gauss-Markov
    auto-covariance template. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s) :
    (gaussMarkovCov n_s sigma rho) i j =
      let d : Nat := if i.val <= j.val then j.val - i.val else i.val - j.val
      (sigma.val : Complex) * ((rho.val : Complex) ^ d) :=
  dicode_zf_equalisation sigma rho i j

/-- The general diagonal entry of the Gauss-Markov auto-covariance. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i : Fin n_s) :
    (gaussMarkovCov n_s sigma rho) i i = (sigma.val : Complex) :=
  gaussMarkovCov_diag sigma rho i

/-- An off-diagonal entry with `i.val < j.val`. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s) (h : i.val ≤ j.val) :
    (gaussMarkovCov n_s sigma rho) i j
      = (sigma.val : Complex) * (rho.val : Complex) ^ (j.val - i.val) :=
  gaussMarkovCov_entry_of_le sigma rho i j h

/-- Delay-tap channel is causal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val < j.val) :
    delayTapMatrix n_s paths f_s i j = (0 : Complex) :=
  delayTap_causal paths f_s i j h

/-- RFView channel is causal. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).causal :=
  rfView_causal rowTaps sigma

/-- RFView channel has bandwidth at most `6`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 6 :=
  rfView_bandwidth rowTaps sigma

/-! ## Section III.  Entropy rates and determinants -/

/-- The first-order Gauss-Markov entropy rate equals the closed form. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (n_s : Nat) :
    entropyRate1 sigma rho n_s
      = Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
        + (1 - (1 : Real) / (n_s : Real))
            * Real.log (1 - rho.val ^ 2) :=
  entropyRate1_eq sigma rho n_s

/-- The block-`b` entropy rate equals the closed form. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    entropyRate1_block sigma rho b
      = Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
        + (1 - (1 : Real) / (b.toNat : Real))
            * Real.log (1 - rho.val ^ 2) :=
  entropyRate1_block_eq sigma rho b

/-- The 2x2 first-order Gauss-Markov determinant has the factored form
    `sigma^2 * (1 - rho^2)`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho).det
      = (sigma.val : Complex) ^ 2 * (1 - (rho.val : Complex) ^ 2) :=
  cov1_det_fin_two_factored sigma rho

/-- The Yule-Walker variance bound forces a positive denominator. -/
example (rho1 rho2 : CorrelationCoefficient)
    (h : yuleWalker_variance_bound rho1 rho2) :
    0 < 1 - rho1.val ^ 2 :=
  yuleWalker_denom_pos rho1 rho2 h

/-! ## Section IV.  GRAND decoder -/

/-- `Codeword.xor` is associative. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor (Codeword.xor a b) c = Codeword.xor a (Codeword.xor b c) :=
  Codeword.xor_assoc a b c

/-- `Codeword.xor` is self-inverse: `a xor a = 0`. -/
example {n : Nat} (a : Codeword n) :
    Codeword.xor a a = 0 :=
  Codeword.xor_self a

/-- GRAND output has zero syndrome. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) (c : Codeword n)
    (hfind : grandFind H Y order = some c) :
    forall (i : Fin (n - k)), H.matrix.mulVec c i = 0 :=
  grandFind_zero_syndrome H Y order c hfind

/-- ORBGRAND-AI accept gate is sound (returns codewords passing the
    membership oracle). -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (c : Codeword n_s)
    (h : orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi budget patterns = some c) :
    Phi c = true :=
  orbgrandAi_accept_sound Y Phi budget patterns c h

/-- ORBGRAND-AI output is a substitution of the received vector. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (c : Codeword n_s)
    (h : orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi budget patterns = some c) :
    exists e, e ∈ patterns /\ c = substitute Y e :=
  orbgrandAi_returns_substituted Y Phi budget patterns c h

/-- ORBGRAND-AI with a vacuous codebook never accepts. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) budget patterns = none :=
  orbgrandAi_empty_codebook Y budget patterns

/-- GRAND output equals `Y xor Ng` for some `Ng` from the candidate list. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) (c : Codeword n)
    (hfind : grandFind H Y order = some c) :
    exists Ng, Ng ∈ order /\ c = Codeword.xor Y Ng :=
  grandFind_returns_xor H Y order c hfind

/-- GRAND short-circuits on the zero-noise candidate when `Y` is a codeword. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (rest : List (Codeword n))
    (h_cw : forall (i : Fin (n - k)), H.matrix.mulVec Y i = 0) :
    grandFind H Y (0 :: rest) = some Y :=
  grandFind_zero_first H Y rest h_cw

/-- Syndrome decomposes as `H * Y + H * N_g`. -/
example {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n)
    (i : Fin (n - k)) :
    syndrome H Y N_g i = H.matrix.mulVec Y i + H.matrix.mulVec N_g i :=
  syndrome_decomp H Y N_g i

/-- On a codeword receiver, the syndrome reduces to `H * N_g`. -/
example {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n)
    (h : forall i, H.matrix.mulVec Y i = 0) (i : Fin (n - k)) :
    syndrome H Y N_g i = H.matrix.mulVec N_g i :=
  syndrome_codeword H Y N_g h i

/-- Identity channel receive law: `receive X N = X + N`. -/
example {n_s : Nat} (X N : SymbolVector n_s) (noiseCov : CovMatrix n_s) :
    LinearIsi.receive { channel := 1, noiseCov := noiseCov } X N
      = fun k => X k + N k :=
  LinearIsi.receive_one X N noiseCov

/-- Noise-free receive: `receive X 0 = h * X`. -/
example {n_s : Nat} (ch : LinearIsi n_s) (X : SymbolVector n_s) :
    ch.receive X 0 = fun k => ch.channel.mulVec X k :=
  LinearIsi.receive_zero_noise ch X

/-- Signal-free receive: `receive 0 N = N`. -/
example {n_s : Nat} (ch : LinearIsi n_s) (N : SymbolVector n_s) :
    ch.receive 0 N = N :=
  LinearIsi.receive_zero_signal ch N

/-- Receive is additive in the noise. -/
example {n_s : Nat} (ch : LinearIsi n_s) (X N1 N2 : SymbolVector n_s) :
    ch.receive X (N1 + N2) = ch.receive X N1 + N2 :=
  LinearIsi.receive_noise_add ch X N1 N2

/-- Full linearity of the receiver. -/
example {n_s : Nat} (ch : LinearIsi n_s) (X1 X2 N1 N2 : SymbolVector n_s) :
    ch.receive (X1 + X2) (N1 + N2) = ch.receive X1 N1 + ch.receive X2 N2 :=
  LinearIsi.receive_add ch X1 X2 N1 N2

/-- ORBGRAND ordering soundness: lower logistic weight => earlier bucket. -/
example {n : Nat} (pi : ReliabilityRank n) (e1 e2 : Fin n -> Bool)
    (h : logisticWeight pi e1 < logisticWeight pi e2) :
    exists (i j : Nat),
      i < j /\
      landslideBucket pi i e1 /\
      landslideBucket pi j e2 :=
  orbgrand_ordering_sound pi e1 e2 h

/-- Yule-Walker variance bound forces `rho_1 < 1`. -/
example (rho1 rho2 : CorrelationCoefficient)
    (h : yuleWalker_variance_bound rho1 rho2) :
    rho1.val < 1 :=
  yuleWalker_rho1_lt_one rho1 rho2 h

/-- Full soundness specification of GRAND: zero syndrome AND a candidate
    from the input list. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) (c : Codeword n)
    (hfind : grandFind H Y order = some c) :
    (forall (i : Fin (n - k)), H.matrix.mulVec c i = 0)
    /\ (exists Ng, Ng ∈ order /\ c = Codeword.xor Y Ng) :=
  grandFind_sound H Y order c hfind

/-- Full soundness specification of ORBGRAND-AI: codebook acceptance AND
    a substitution of the input. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (c : Codeword n_s)
    (h : orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi budget patterns = some c) :
    Phi c = true /\ (exists e, e ∈ patterns /\ c = substitute Y e) :=
  orbgrandAi_sound Y Phi budget patterns c h

/-- GRAND on a singleton candidate list reduces to a single syndrome check. -/
example {n k : Nat} (H : ParityCheck n k) (Y Ng : Codeword n) :
    grandFind H Y [Ng]
      = if _hp : forall (i : Fin (n - k)),
            H.matrix.mulVec (Codeword.xor Y Ng) i = 0 then
          some (Codeword.xor Y Ng)
        else
          none :=
  grandFind_singleton H Y Ng

/-- GRAND extension stability: appending more candidates preserves acceptance. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order1 order2 : List (Codeword n)) (c : Codeword n)
    (h : grandFind H Y order1 = some c) :
    grandFind H Y (order1 ++ order2) = some c :=
  grandFind_append_left H Y order1 c h order2

/-- ORBGRAND-AI extension stability: appending more patterns preserves acceptance. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (p1 p2 : List (Fin (n_s / b) -> Fin numCandidates))
    (c : Codeword n_s)
    (h : orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi budget p1 = some c) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget (p1 ++ p2) = some c :=
  orbgrandAi_append_left Y Phi budget p1 p2 c h

/-- ORBGRAND-AI strong soundness: output is `substitute Y e` for some `e` passing both gates. -/
example {n_s b numCandidates : Nat}
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
  orbgrandAi_returns_strong Y Phi budget patterns c h

/-- ORBGRAND-AI all-fail sufficient condition: returns none when every pattern fails. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (hfail : forall e, e ∈ patterns ->
      ¬ noSubstitutionConflict e ∨ ¬ Phi (substitute Y e)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget patterns = none :=
  orbgrandAi_none_of_all_fail Y Phi budget patterns hfail

/-- GRAND failure characterisation: returns none iff every candidate fails. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) :
    grandFind H Y order = none <->
      forall Ng, Ng ∈ order ->
        ¬ (forall (i : Fin (n - k)),
            H.matrix.mulVec (Codeword.xor Y Ng) i = 0) :=
  grandFind_none_iff H Y order

/-- ORBGRAND-AI failure characterisation under sufficient budget. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (hbudget : patterns.length <= budget.toNat) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget patterns = none <->
      forall e, e ∈ patterns ->
        ¬ noSubstitutionConflict e ∨ ¬ Phi (substitute Y e) :=
  orbgrandAi_none_iff_of_budget Y Phi budget patterns hbudget

/-- Codeword.xor and `+` coincide as pointwise ZMod 2 addition. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = a + b :=
  Codeword.xor_eq_add a b

/-- Codeword negation is the identity in ZMod 2. -/
example {n : Nat} (a : Codeword n) : -a = a :=
  Codeword.neg_eq_self a

/-- Bandwidth monotonicity: a stronger (smaller) bandwidth implies a weaker one. -/
example {n_s : Nat} (ch : LinearIsi n_s) (b b' : Nat) (hb : b <= b')
    (h : ch.bandwidth b) : ch.bandwidth b' :=
  LinearIsi.bandwidth_le hb h

/-- AR(2) closed-form at index 2. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 2 = phi1 * z2 + phi2 * z1 :=
  ar2_two phi1 phi2 z1 z2

/-- Imperfect-CSI perturbation preserves causality. -/
example {n_s : Nat} {h : ChannelMatrix n_s}
    {epsilon : Matrix (Fin n_s) (Fin n_s) Complex}
    (hcausal : forall (i j : Fin n_s), i.val < j.val -> h i j = 0)
    (i j : Fin n_s) (hij : i.val < j.val) :
    perturbChannel h epsilon i j = 0 :=
  perturbChannel_causal_of_causal hcausal i j hij

/-- BPSK is a concrete `Constellation Bool`. -/
example : Constellation Bool := bpsk

/-- BPSK exceedance is 0 on agreement. -/
example (s : Bool) : bpsk.exceed s s = 0 :=
  bpsk_exceed_self s

/-- BPSK exceedance is 1 on disagreement. -/
example {s s_hat : Bool} (h : s ≠ s_hat) : bpsk.exceed s s_hat = 1 :=
  bpsk_exceed_diff h

/-- `landslide n w` exactly enumerates length-`n` patterns of bit-weight `w`. -/
example (n w : Nat) (e : Fin n -> Bool) :
    e ∈ landslide n w <-> bitWeight e = w :=
  landslide_correct n w e

/-- Every pattern is in its own bit-weight bucket. -/
example {n : Nat} (e : Fin n -> Bool) :
    e ∈ landslide n (bitWeight e) :=
  landslide_self_mem e

/-- A pattern's bucket is uniquely determined. -/
example {n w1 w2 : Nat} {e : Fin n -> Bool}
    (h1 : e ∈ landslide n w1) (h2 : e ∈ landslide n w2) :
    w1 = w2 :=
  landslide_unique_bucket h1 h2

/-- The bit-weight is zero iff all bits are false. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight e = 0 <-> forall i, e i = false :=
  bitWeight_zero_iff_all_false e

/-- The constant-false pattern is in bucket 0. -/
example {n : Nat} : (fun _ : Fin n => false) ∈ landslide n 0 :=
  const_false_mem_landslide_zero

/-- Bucket 0 has length 1 for any n. -/
example {n : Nat} : (landslide n 0).length = 1 :=
  landslide_zero_length

/-- Bucket 0 is exactly `[fun _ => false]`. -/
example {n : Nat} : landslide n 0 = [fun _ : Fin n => false] :=
  landslide_zero_singleton

/-- Bit-weight is bounded above by the all-true bit-weight. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight e ≤ bitWeight (fun _ : Fin n => true) :=
  bitWeight_le_const_true e

/-- All-true bit-weight equals the rank-sum. -/
example {n : Nat} :
    bitWeight (fun _ : Fin n => true)
      = Finset.univ.sum (fun i : Fin n => i.val + 1) :=
  bitWeight_const_true

/-- Buckets above the max weight are empty. -/
example {n w : Nat} (h : bitWeight (fun _ : Fin n => true) < w) :
    landslide n w = [] :=
  landslide_eq_nil_of_too_large h

/-- QPSK is a concrete `Constellation (Fin 4)`. -/
example : Constellation (Fin 4) := qpsk

/-- QPSK exceedance is 0 on agreement. -/
example (s : Fin 4) : qpsk.exceed s s = 0 :=
  qpsk_exceed_self s

/-- QPSK exceedance is 1 on disagreement. -/
example {s s_hat : Fin 4} (h : s ≠ s_hat) : qpsk.exceed s s_hat = 1 :=
  qpsk_exceed_diff h

/-- Bit-weight is strictly less than the max iff there is a false bit. -/
example {n : Nat} (e : Fin n -> Bool) (h : ∃ i, e i = false) :
    bitWeight e < bitWeight (fun _ : Fin n => true) :=
  bitWeight_lt_const_true_of_exists_false e h

/-- Bit-weight equals the max iff every bit is true. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight e = bitWeight (fun _ : Fin n => true) <-> forall i, e i = true :=
  bitWeight_eq_const_true_iff e

/-- A bucket is empty iff no pattern has that bit-weight. -/
example {n w : Nat} :
    landslide n w = [] <-> forall (e : Fin n -> Bool), bitWeight e ≠ w :=
  landslide_eq_nil_iff

/-- Unified extension weight rule. -/
example {n : Nat} (b : Bool) (e : Fin n -> Bool) :
    bitWeight (landslideExtend b e)
      = bitWeight e + (if b then n + 1 else 0) :=
  bitWeight_landslideExtend b e

/-- Max-weight bucket is exactly the all-true singleton. -/
example {n : Nat} :
    landslide n (bitWeight (fun _ : Fin n => true))
      = [fun _ : Fin n => true] :=
  landslide_max_singleton

/-- Zero bit-weight iff equal to the all-false pattern. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight e = 0 <-> e = (fun _ : Fin n => false) :=
  bitWeight_zero_iff_eq_const_false e

/-- Max bit-weight iff equal to the all-true pattern. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight e = bitWeight (fun _ : Fin n => true)
      <-> e = (fun _ : Fin n => true) :=
  bitWeight_eq_max_iff_eq_const_true e

/-- Syndrome is invariant under XOR-shift of the receiver by a codeword. -/
example {n k : Nat} (H : ParityCheck n k) (Y N c : Codeword n)
    (h_c : forall (i : Fin (n - k)), H.matrix.mulVec c i = 0)
    (i : Fin (n - k)) :
    syndrome H (Codeword.xor Y c) N i = syndrome H Y N i :=
  syndrome_invariant_under_codeword H Y N c h_c i

/-- The zero codeword is a codeword. -/
example {n k : Nat} (H : ParityCheck n k) (i : Fin (n - k)) :
    H.matrix.mulVec 0 i = 0 :=
  Codeword.zero_is_codeword H i

/-- Codewords are closed under XOR. -/
example {n k : Nat} (H : ParityCheck n k) {a b : Codeword n}
    (ha : forall (i : Fin (n - k)), H.matrix.mulVec a i = 0)
    (hb : forall (i : Fin (n - k)), H.matrix.mulVec b i = 0)
    (i : Fin (n - k)) :
    H.matrix.mulVec (Codeword.xor a b) i = 0 :=
  Codeword.xor_codeword_is_codeword H ha hb i

/-- Codeword XOR right cancel: `(a xor b) xor b = a`. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor (Codeword.xor a b) b = a :=
  Codeword.xor_xor_right a b

/-- Codeword XOR transposition: `a xor b = c ↔ a = c xor b`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor a b = c <-> a = Codeword.xor c b :=
  Codeword.xor_eq_iff_eq_xor a b c

/-- `landslideExtend` is injective in both top bit and restriction. -/
example {n : Nat} {b1 b2 : Bool} {e1 e2 : Fin n -> Bool} :
    landslideExtend b1 e1 = landslideExtend b2 e2
      <-> b1 = b2 /\ e1 = e2 :=
  landslideExtend_eq_iff

/-- Constellation: strict positivity of exceedance iff symbols differ. -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    0 < cs.exceed s s_hat <-> s ≠ s_hat :=
  cs.exceed_pos_iff_ne s s_hat

/-- AR(1)-like AR(2): `phi_1 = 1, phi_2 = 0` gives constant z2 from index 1. -/
example (z1 z2 : Complex) (n : Nat) : ar2 1 0 z1 z2 (n + 1) = z2 :=
  ar2_phi1_one_phi2_zero z1 z2 n

/-- BPSK exceedance is symmetric. -/
example (s s_hat : Bool) : bpsk.exceed s s_hat = bpsk.exceed s_hat s :=
  bpsk_exceed_symm s s_hat

/-- QPSK exceedance is symmetric. -/
example (s s_hat : Fin 4) : qpsk.exceed s s_hat = qpsk.exceed s_hat s :=
  qpsk_exceed_symm s s_hat

/-- Zero channel stays zero under any perturbation. -/
example {n_s : Nat} (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) :
    perturbChannel 0 epsilon = 0 :=
  perturbChannel_zero_channel epsilon

/-- Max-weight bucket has no duplicates. -/
example {n : Nat} :
    (landslide n (bitWeight (fun _ : Fin n => true))).Nodup :=
  landslide_max_nodup

/-- Zero-weight bucket has no duplicates. -/
example {n : Nat} : (landslide n 0).Nodup :=
  landslide_zero_nodup

/-- Max-weight bucket has length 1. -/
example {n : Nat} :
    (landslide n (bitWeight (fun _ : Fin n => true))).length = 1 :=
  landslide_max_length

/-- Singleton-bucket element is unique. -/
example {n w : Nat} {e : Fin n -> Bool}
    (h : landslide n w = [e]) (e' : Fin n -> Bool) (h_eq : bitWeight e' = w) :
    e' = e :=
  landslide_singleton_unique h e' h_eq

/-- Non-membership iff wrong bit-weight. -/
example {n w : Nat} (e : Fin n -> Bool) :
    e ∉ landslide n w <-> bitWeight e ≠ w :=
  landslide_not_mem_iff e

/-- Trivial AR coefficients vanish for `cov2_lag` past lag 2. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (n : Nat) :
    cov2_lag sigma rho1 rho2 0 0 (n + 3) = 0 :=
  cov2_lag_beta_zero sigma rho1 rho2 n

/-- Extension never decreases bit-weight. -/
example {n : Nat} (b : Bool) (e : Fin n -> Bool) :
    bitWeight e ≤ bitWeight (landslideExtend b e) :=
  bitWeight_le_landslideExtend b e

/-- Extension by `true` strictly increases bit-weight. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight e < bitWeight (landslideExtend true e) :=
  bitWeight_lt_landslideExtend_true e

/-- `landslideExtend` as a bijection. -/
example {n : Nat} :
    Function.Bijective (fun (p : Bool × (Fin n -> Bool)) =>
      landslideExtend p.1 p.2) :=
  landslideExtend_bijective

/-- The inverse `landslideExtend_inv` is a left inverse. -/
example {n : Nat} (b : Bool) (e : Fin n -> Bool) :
    landslideExtend_inv (landslideExtend b e) = (b, e) :=
  landslideExtend_inv_landslideExtend b e

/-- Codeword `+`-form equality characterisation. -/
example {n : Nat} (a b : Codeword n) : a + b = 0 <-> a = b :=
  Codeword.add_eq_zero_iff a b

/-- Codeword XOR is identity iff right arg is zero. -/
example {n : Nat} (a b : Codeword n) : Codeword.xor a b = a <-> b = 0 :=
  Codeword.xor_eq_self_iff a b

/-- Trivial constellation exceedance is zero. -/
example (s s_hat : Unit) : trivialConstellation.exceed s s_hat = 0 :=
  trivialConstellation_exceed s s_hat

/-- Restriction never increases bit-weight. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    bitWeight (e ∘ Fin.castSucc) ≤ bitWeight e :=
  bitWeight_castSucc_le e

/-- Restriction strict-decreases when top bit was true. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) (h : e (Fin.last n) = true) :
    bitWeight (e ∘ Fin.castSucc) < bitWeight e :=
  bitWeight_castSucc_lt_of_last_true e h

/-- Every length-`(n + 1)` pattern decomposes as an extension. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    ∃ b : Bool, ∃ e' : Fin n -> Bool, e = landslideExtend b e' :=
  landslideExtend_exists e

/-- Asymptotic entropy rate unfolding. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    entropyRate1_asymp sigma rho
      = Real.log (2 * Real.exp 1 * Real.pi * sigma.val
                  * (1 - rho.val ^ 2)) :=
  entropyRate1_asymp_eq sigma rho

/-- Delay-tap response with no paths is zero. -/
example (paths : Fin 0 -> DelayTapPath) (f_s : SamplingFreq)
    (k' : SymbolIndex) :
    delayTapImpulseResponse paths f_s k' = 0 :=
  delayTapImpulseResponse_empty paths f_s k'

/-- RFView matrix diagonal entry equals tap1. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i : Fin n_s) :
    rfViewMatrix n_s rowTaps i i = (rowTaps i).tap1 :=
  rfViewMatrix_diag rowTaps i

/-- DelayTap matrix entry above diagonal is zero. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (hij : i.val < j.val) :
    delayTapMatrix n_s paths f_s i j = (0 : Complex) :=
  delayTapMatrix_zero_above_diag paths f_s i j hij

/-- RFView matrix at six-below-diagonal is zero (boundary just inside
    the out-of-band region: `tap?_7` is `none`). -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (h : i.val = j.val + 6) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  rfViewMatrix_at_six_below_diag rowTaps i j h

/-- All-true logistic weight equals all-true bit-weight (rank-invariant maximum). -/
example {n : Nat} (pi : ReliabilityRank n) :
    logisticWeight pi (fun _ : Fin n => true)
      = bitWeight (fun _ : Fin n => true) :=
  logisticWeight_const_true_eq_bitWeight_const_true pi

/-- Logistic weight is zero iff every bit at every rank position is false. -/
example {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    logisticWeight pi e = 0 <-> forall i, e (pi.perm i) = false :=
  logisticWeight_zero_iff_all_false_at_perm pi e

/-- Logistic weight equals bit-weight of the rank-permuted pattern. -/
example {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    logisticWeight pi e = bitWeight (e ∘ pi.perm) :=
  logisticWeight_eq_bitWeight_comp pi e

/-- 2x2 Gauss-Markov covariance: explicit off-diagonal symmetry. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho) 0 1 = (gaussMarkovCov 2 sigma rho) 1 0 :=
  gaussMarkovCov_two_01_eq_10 sigma rho

/-- Logistic weight is upper-bounded by the all-true weight. -/
example {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    logisticWeight pi e
      <= logisticWeight pi (fun _ : Fin n => true) :=
  logisticWeight_le_const_true pi e

/-- The all-true noise pattern has rank-sum logistic weight. -/
example {n : Nat} (pi : ReliabilityRank n) :
    logisticWeight pi (fun _ : Fin n => true)
      = Finset.univ.sum (fun i : Fin n => i.val + 1) :=
  logisticWeight_const_true pi

/-- The all-false noise pattern has zero logistic weight. -/
example {n : Nat} (pi : ReliabilityRank n) :
    logisticWeight pi (fun _ : Fin n => false) = 0 :=
  logisticWeight_const_false pi

/-- Involution variant `a xor (b xor a) = b`. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor a (Codeword.xor b a) = b :=
  Codeword.xor_xor_left a b

/-- Zero-received syndrome-zero is exactly the noise-codeword condition. -/
example {n k : Nat} (H : ParityCheck n k) (N : Codeword n) :
    syndromeZero H 0 N
      <-> forall (i : Fin (n - k)), H.matrix.mulVec N i = 0 :=
  syndromeZero_zero_received_iff_codeword H N

/-- Zero-noise syndrome-zero is exactly the codeword condition. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    syndromeZero H Y 0
      <-> forall (i : Fin (n - k)), H.matrix.mulVec Y i = 0 :=
  syndromeZero_zero_noise_iff_codeword H Y

/-- Bandwidth depends only on the channel matrix. -/
example {n_s : Nat} {ch1 ch2 : LinearIsi n_s} (h : ch1.channel = ch2.channel)
    (b : Nat) :
    ch1.bandwidth b <-> ch2.bandwidth b :=
  LinearIsi.bandwidth_iff_of_eq_channels h b

/-- Causality depends only on the channel matrix. -/
example {n_s : Nat} {ch1 ch2 : LinearIsi n_s} (h : ch1.channel = ch2.channel) :
    ch1.causal <-> ch2.causal :=
  LinearIsi.causal_iff_of_eq_channels h

/-- Receiver depends only on the channel matrix (noiseCov is unread). -/
example {n_s : Nat} (ch1 ch2 : LinearIsi n_s)
    (h : ch1.channel = ch2.channel) (X N : SymbolVector n_s) :
    ch1.receive X N = ch2.receive X N :=
  LinearIsi.receive_of_eq_channels ch1 ch2 h X N

/-- `rfView.channel` unfolds to `rfViewMatrix`. -/
example (n_s : Nat) (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).channel = rfViewMatrix n_s rowTaps :=
  rfView_channel n_s rowTaps sigma

/-- `dicode.channel` unfolds to `dicodeMatrix`. -/
example (n_s : Nat) (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).channel = dicodeMatrix n_s rho :=
  dicode_channel n_s sigma rho

/-- `dicode.noiseCov` unfolds to `gaussMarkovCov`. -/
example (n_s : Nat) (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).noiseCov = gaussMarkovCov n_s sigma rho :=
  dicode_noiseCov n_s sigma rho

/-- rfView noise covariance: diagonal entry is `sigma.val`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower)
    (i : Fin n_s) :
    (rfView n_s rowTaps sigma).noiseCov i i = (sigma.val : Complex) :=
  rfView_noiseCov_diag rowTaps sigma i

/-- rfView noise covariance: off-diagonal is zero (white noise). -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower)
    (i j : Fin n_s) (h : i.val ≠ j.val) :
    (rfView n_s rowTaps sigma).noiseCov i j = (0 : Complex) :=
  rfView_noiseCov_off rowTaps sigma i j h

/-- Extending by `false` leaves the bit-weight unchanged. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight (landslideExtend false e) = bitWeight e :=
  bitWeight_extend_false e

/-- Extending by `true` adds `n + 1` to the bit-weight. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight (landslideExtend true e) = bitWeight e + (n + 1) :=
  bitWeight_extend_true e

/-- Bit-weight of the unique length-0 pattern is zero. -/
example (e : Fin 0 -> Bool) : bitWeight e = 0 :=
  bitWeight_fin_zero e

/-- AR(2) with `phi_1 = 0` skips the immediate predecessor. -/
example (phi2 z1 z2 : Complex) (n : Nat) :
    ar2 0 phi2 z1 z2 (n + 2) = phi2 * ar2 0 phi2 z1 z2 n :=
  ar2_phi1_zero_succ phi2 z1 z2 n

/-- AR(2) with `phi_2 = 0` collapses to a geometric step. -/
example (phi1 z1 z2 : Complex) (n : Nat) :
    ar2 phi1 0 z1 z2 (n + 2) = phi1 * ar2 phi1 0 z1 z2 (n + 1) :=
  ar2_phi2_zero_succ phi1 z1 z2 n

/-- Receiver agreement at fixed noise iff channel images agree. -/
example {n_s : Nat} (ch : LinearIsi n_s) (X1 X2 N : SymbolVector n_s) :
    ch.receive X1 N = ch.receive X2 N
      <-> ch.channel.mulVec X1 = ch.channel.mulVec X2 :=
  LinearIsi.receive_eq_iff_mulVec_eq ch X1 X2 N

/-- Receiver is noise-injective at a fixed signal. -/
example {n_s : Nat} (ch : LinearIsi n_s) (X N1 N2 : SymbolVector n_s) :
    ch.receive X N1 = ch.receive X N2 <-> N1 = N2 :=
  LinearIsi.receive_eq_iff_noise_eq ch X N1 N2

/-- XOR involution: `Y xor (Y xor Ng) = Ng`. -/
example {n : Nat} (Y Ng : Codeword n) :
    Codeword.xor Y (Codeword.xor Y Ng) = Ng :=
  Codeword.xor_xor_self Y Ng

/-- Codeword XOR right-cancel: `(a xor b) xor b = a`. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor (Codeword.xor a b) b = a :=
  Codeword.xor_xor_right a b

/-- Codeword XOR left cancellation: `a xor b = a xor c → b = c`. -/
example {n : Nat} {a b c : Codeword n}
    (h : Codeword.xor a b = Codeword.xor a c) : b = c :=
  Codeword.xor_left_cancel h

/-- Codeword XOR right cancellation: `a xor c = b xor c → a = b`. -/
example {n : Nat} {a b c : Codeword n}
    (h : Codeword.xor a c = Codeword.xor b c) : a = b :=
  Codeword.xor_right_cancel h

/-- Perturbed channel entry is zero iff the underlying entry is zero
    or the `1 + epsilon` factor cancels. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    (i j : Fin n_s) :
    perturbChannel h epsilon i j = 0
      <-> h i j = 0 ∨ 1 + epsilon i j = 0 :=
  perturbChannel_eq_zero_iff h epsilon i j

/-- `syndromeZero` is invariant under codeword shifts of the receiver. -/
example {n k : Nat} (H : ParityCheck n k) (Y N c : Codeword n)
    (h_c : forall (i : Fin (n - k)), H.matrix.mulVec c i = 0) :
    syndromeZero H (Codeword.xor Y c) N <-> syndromeZero H Y N :=
  syndromeZero_xor_codeword_received_iff H Y N c h_c

/-- `syndromeZero` is invariant under codeword shifts of the noise candidate. -/
example {n k : Nat} (H : ParityCheck n k) (Y N c : Codeword n)
    (h_c : forall (i : Fin (n - k)), H.matrix.mulVec c i = 0) :
    syndromeZero H Y (Codeword.xor N c) <-> syndromeZero H Y N :=
  syndromeZero_xor_codeword_noise_iff H Y N c h_c

/-- Syndrome is invariant under codeword shifts of the noise candidate. -/
example {n k : Nat} (H : ParityCheck n k) (Y N c : Codeword n)
    (h_c : forall (i : Fin (n - k)), H.matrix.mulVec c i = 0)
    (i : Fin (n - k)) :
    syndrome H Y (Codeword.xor N c) i = syndrome H Y N i :=
  syndrome_invariant_under_codeword_noise H Y N c h_c i

/-- Right-side codeword-shift preserves codeword-membership: with `b` a codeword,
    `a xor b` is a codeword iff `a` is. -/
example {n k : Nat} (H : ParityCheck n k) {a b : Codeword n}
    (hb : forall (i : Fin (n - k)), H.matrix.mulVec b i = 0) :
    (forall (i : Fin (n - k)),
        H.matrix.mulVec (Codeword.xor a b) i = 0)
      <-> (forall (i : Fin (n - k)), H.matrix.mulVec a i = 0) :=
  Codeword.xor_codeword_iff_codeword_of_right H hb

/-- Codeword-shift preserves codeword-membership: with `a` a codeword,
    `a xor b` is a codeword iff `b` is. -/
example {n k : Nat} (H : ParityCheck n k) {a b : Codeword n}
    (ha : forall (i : Fin (n - k)), H.matrix.mulVec a i = 0) :
    (forall (i : Fin (n - k)),
        H.matrix.mulVec (Codeword.xor a b) i = 0)
      <-> (forall (i : Fin (n - k)), H.matrix.mulVec b i = 0) :=
  Codeword.xor_codeword_iff_codeword_of_left H ha

/-- Codeword-right shift is invisible under the parity-check map. -/
example {n k : Nat} (H : ParityCheck n k) {a b : Codeword n}
    (hb : forall (i : Fin (n - k)), H.matrix.mulVec b i = 0)
    (i : Fin (n - k)) :
    H.matrix.mulVec (Codeword.xor a b) i = H.matrix.mulVec a i :=
  Codeword.mulVec_xor_codeword_right H hb i

/-- Codeword-left shift is invisible under the parity-check map. -/
example {n k : Nat} (H : ParityCheck n k) {a b : Codeword n}
    (ha : forall (i : Fin (n - k)), H.matrix.mulVec a i = 0)
    (i : Fin (n - k)) :
    H.matrix.mulVec (Codeword.xor a b) i = H.matrix.mulVec b i :=
  Codeword.mulVec_xor_codeword_left H ha i

/-- Parity-check map is XOR-linear: `H * (a xor b) = H * a + H * b`. -/
example {n k : Nat} (H : ParityCheck n k) (a b : Codeword n) :
    H.matrix.mulVec (Codeword.xor a b)
      = H.matrix.mulVec a + H.matrix.mulVec b :=
  Codeword.mulVec_xor H a b

/-- Pairwise XOR equality rearrangement: `a xor b = c xor d ↔ a xor c = b xor d`. -/
example {n : Nat} (a b c d : Codeword n) :
    (Codeword.xor a b = Codeword.xor c d)
      <-> (Codeword.xor a c = Codeword.xor b d) :=
  Codeword.xor_eq_xor_iff_xor_eq_xor a b c d

/-- Codeword XOR common-suffix cancellation: `(a xor b) xor (c xor b) = a xor c`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor c b)
      = Codeword.xor a c :=
  Codeword.xor_xor_xor_self_right a b c

/-- Codeword XOR common-prefix cancellation: `(a xor b) xor (a xor c) = b xor c`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor a c)
      = Codeword.xor b c :=
  Codeword.xor_xor_xor_self a b c

/-- Codeword XOR is commutative. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = Codeword.xor b a :=
  Codeword.xor_comm a b

/-- Codeword XOR has zero on the left as identity. -/
example {n : Nat} (a : Codeword n) :
    Codeword.xor 0 a = a :=
  Codeword.zero_xor a

/-- Codeword XOR has zero on the right as identity. -/
example {n : Nat} (a : Codeword n) :
    Codeword.xor a 0 = a :=
  Codeword.xor_zero a

/-- `orbgrandAiLoop` with zero steps and a non-empty list returns `none`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAiLoop Y Phi 0 (e :: rest) = none :=
  orbgrandAiLoop_zero_steps_cons Y Phi e rest

/-- QPSK exceedance is binary-valued (0 or 1). -/
example (s s_hat : Fin 4) :
    qpsk.exceed s s_hat = 0 ∨ qpsk.exceed s s_hat = 1 :=
  qpsk_exceed_zero_or_one s s_hat

/-- BPSK exceedance is binary-valued (0 or 1). -/
example (s s_hat : Bool) :
    bpsk.exceed s s_hat = 0 ∨ bpsk.exceed s s_hat = 1 :=
  bpsk_exceed_zero_or_one s s_hat

/-- At zero noise, `receive X 0 = 0` iff `h * X = 0`. -/
example {n_s : Nat} (ch : LinearIsi n_s) (X : SymbolVector n_s) :
    ch.receive X 0 = 0 <-> ch.channel.mulVec X = 0 :=
  LinearIsi.receive_zero_noise_eq_zero_iff ch X

/-- `perturbChannel` preserves zero entries pointwise. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i j : Fin n_s} (hzero : h i j = 0) :
    perturbChannel h epsilon i j = 0 :=
  perturbChannel_zero_entry h epsilon hzero

/-- Four-argument XOR shuffle: `(a xor b) xor (c xor d) = (a xor c) xor (b xor d)`. -/
example {n : Nat} (a b c d : Codeword n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor c d)
      = Codeword.xor (Codeword.xor a c) (Codeword.xor b d) :=
  Codeword.xor_xor_comm a b c d

/-- Constellation exceedance is non-zero iff the symbols differ. -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s_hat ≠ 0 <-> s ≠ s_hat :=
  cs.exceed_ne_zero_iff_ne s s_hat

/-- Single-path delay-tap impulse response is the attenuation times sinc. -/
example (paths : Fin 1 -> DelayTapPath) (f_s : SamplingFreq) (k' : SymbolIndex) :
    delayTapImpulseResponse paths f_s k'
      = (paths 0).attenuation *
        (((sinc ((paths 0).delay * f_s.val - (k'.toNat : Real))
          : Real)) : Complex) :=
  delayTapImpulseResponse_single paths f_s k'

/-- Delay-tap matrix vanishes entirely when every path has zero attenuation. -/
example {n_s p : Nat} (paths : Fin p -> DelayTapPath)
    (h_zero : forall d, (paths d).attenuation = 0)
    (f_s : SamplingFreq) (i j : Fin n_s) :
    delayTapMatrix n_s paths f_s i j = (0 : Complex) :=
  delayTapMatrix_zero_attenuations paths h_zero f_s i j

/-- `receive` is additive in the signal at zero noise. -/
example {n_s : Nat} (ch : LinearIsi n_s) (X1 X2 : SymbolVector n_s) :
    ch.receive (X1 + X2) 0 = ch.receive X1 0 + ch.receive X2 0 :=
  LinearIsi.receive_signal_add_zero_noise ch X1 X2

/-- Left transposition of Codeword XOR: `a xor (b xor c) = b xor (a xor c)`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor a (Codeword.xor b c)
      = Codeword.xor b (Codeword.xor a c) :=
  Codeword.xor_left_comm a b c

/-- Right transposition of Codeword XOR: `(a xor b) xor c = (a xor c) xor b`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor (Codeword.xor a b) c
      = Codeword.xor (Codeword.xor a c) b :=
  Codeword.xor_right_comm a b c

/-- AR(2) with `phi_1 = 0, phi_2 = 1` is 2-periodic. -/
example (z1 z2 : Complex) (n : Nat) :
    ar2 0 1 z1 z2 (n + 2) = ar2 0 1 z1 z2 n :=
  ar2_phi1_zero_phi2_one z1 z2 n

/-- `cov2_lag` at lag 4: two-step recurrence expansion. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 4
      = beta1 * (beta1 * (sigma.val * rho2.val)
                  + beta2 * (sigma.val * rho1.val))
        + beta2 * (sigma.val * rho2.val) :=
  cov2_lag_four sigma rho1 rho2 beta1 beta2

/-- Generic constellation exceedance vanishes on the diagonal. -/
example {chi : Type} (cs : Constellation chi) (s : chi) :
    cs.exceed s s = 0 :=
  cs.exceed_self s

/-- A row of `rfViewMatrix` is zero when all six of its taps are zero. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i : Fin n_s)
    (h1 : (rowTaps i).tap1 = 0) (h2 : (rowTaps i).tap2 = 0)
    (h3 : (rowTaps i).tap3 = 0) (h4 : (rowTaps i).tap4 = 0)
    (h5 : (rowTaps i).tap5 = 0) (h6 : (rowTaps i).tap6 = 0)
    (j : Fin n_s) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  rfViewMatrix_row_zero_of_taps_zero rowTaps i h1 h2 h3 h4 h5 h6 j

end OrbgrandAi.Examples.SmokeTest
