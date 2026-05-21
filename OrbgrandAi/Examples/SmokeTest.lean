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

open OrbgrandAi.Section02 OrbgrandAi.Section03 OrbgrandAi.Section04

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

end OrbgrandAi.Examples.SmokeTest
