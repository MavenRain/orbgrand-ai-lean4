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

open OrbgrandAi.Section00 OrbgrandAi.Section02 OrbgrandAi.Section03 OrbgrandAi.Section04 OrbgrandAi.Section06

/-! ## Section II.  Channel-model lemmas -/

/-- Dicode channel: combined causality + bandwidth-1 conjunction. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).causal
      /\ (dicode n_s sigma rho).bandwidth 1 :=
  dicode_structural sigma rho

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

/-- Off-diagonal entry with `j.val < i.val`. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s) (h : j.val < i.val) :
    (gaussMarkovCov n_s sigma rho) i j
      = (sigma.val : Complex) * (rho.val : Complex) ^ (i.val - j.val) :=
  gaussMarkovCov_entry_of_ge sigma rho i j h

/-- Gauss-Markov covariance is symmetric: `(gaussMarkovCov ...) i j = (...) j i`. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s) :
    (gaussMarkovCov n_s sigma rho) i j
      = (gaussMarkovCov n_s sigma rho) j i :=
  gaussMarkovCov_sym sigma rho i j

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

/-- RFView channel: combined causality + bandwidth-6 conjunction. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).causal
      /\ (rfView n_s rowTaps sigma).bandwidth 6 :=
  rfView_structural rowTaps sigma

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

/-- Second-order determinant formula vanishes at zero noise power (for `0 < n_s`). -/
example (rho1 rho2 : CorrelationCoefficient) {n_s : Nat} (h_pos : 0 < n_s) :
    cov2DetFormula ⟨0, le_refl 0⟩ rho1 rho2 n_s = 0 :=
  cov2DetFormula_zero_sigma rho1 rho2 h_pos

/-- Section III closed-form determinant statement: locks the quantifier shape
    (`sigma`, `rho1`, `rho2`, `4 <= n_s`) and the equation `det (gaussMarkov2 ...)
      = cov2DetFormula ...`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) (h4 : 4 <= n_s)
    (h : (gaussMarkov2 sigma rho1 rho2 n_s).det
          = cov2DetFormula sigma rho1 rho2 n_s) :
    True :=
  cov2_det_formula_statement sigma rho1 rho2 n_s h4 h

/-- `gaussMarkov2` at size 3 and off-diagonal `(0, 2)` collapses to
    `sigma.val * rho2.val` via the `cov2_lag` lag-2 base case. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 3 0 2 = sigma.val * rho2.val := rfl

/-- `gaussMarkov2` at size 3 and off-diagonal `(2, 1)` fires the ELSE branch of
    `if i.val <= j.val` (`i.val - j.val = 1`), then the `cov2_lag` lag-1 base
    case `sigma.val * rho1.val`.  Complements the `(0, 2)` THEN-branch lock. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 3 2 1 = sigma.val * rho1.val := rfl

/-- Section III Hadamard log-det bound statement: locks
    `(1 / n_s) * log (cov2DetFormula ...) <= log (sigma^2)`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) (h4 : 4 <= n_s)
    (h : (1 / (n_s : Real))
            * Real.log (cov2DetFormula sigma rho1 rho2 n_s)
          <= Real.log (sigma.val ^ 2)) :
    True :=
  hadamard_log_det_bound_statement sigma rho1 rho2 n_s h4 h

/-- Section III capacity upper bound statement: any abstract capacity `C`
    bounded above by `capacityUpperBound` uniformly over `4 <= n_s`. -/
example (sigmaX : SignalPower) (sigmaN : NoisePower)
    (rho1 rho2 : CorrelationCoefficient) (C : Real)
    (h : forall (n_s : Nat), 4 <= n_s ->
          C <= capacityUpperBound sigmaX sigmaN rho1 rho2 n_s) :
    True :=
  capacity_upper_bound_statement sigmaX sigmaN rho1 rho2 C h

/-- Section III second-order noise entropy-rate bound: `H_bar(N') <=
    log(2 pi e sigma^2)`, the Gaussian maximum-entropy upper bound. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) (h4 : 4 <= n_s)
    (h : entropyRate2 sigma rho1 rho2 n_s
          <= Real.log (2 * Real.pi * Real.exp 1 * sigma.val ^ 2)) :
    True :=
  second_order_noise_entropy_rate_bound_statement sigma rho1 rho2 n_s h4 h

/-- Section III determinant positivity under the Yule-Walker variance bound:
    the closed-form determinant is strictly positive on the stability region. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) (h4 : 4 <= n_s)
    (hyw : yuleWalker_variance_bound rho1 rho2)
    (hpos : 0 < cov2DetFormula sigma rho1 rho2 n_s) :
    True :=
  cov2_det_pos_under_yule_walker_statement sigma rho1 rho2 n_s h4 hyw hpos

/-- Section III Yule-Walker implies the `rho1^2` bound `rho1^2 < (rho2 + 1)/2`. -/
example (rho1 rho2 : CorrelationCoefficient)
    (h : yuleWalker_variance_bound rho1 rho2 ->
          yuleWalker_rho1_sq_bound rho1 rho2) :
    True :=
  yuleWalker_implies_rho1_sq_bound_statement rho1 rho2 h

/-- The 2x2 first-order Gauss-Markov determinant: unfactored form. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho).det
      = (sigma.val : Complex) * (sigma.val : Complex)
        - ((sigma.val : Complex) * (rho.val : Complex))
          * ((sigma.val : Complex) * (rho.val : Complex)) :=
  cov1_det_fin_two sigma rho

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

/-- `substitutionPenalty?` definitional unfold: `Option.map` of the
    `log p(t*) - log p(t)` log-ratio over the hard-decision block. -/
example {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates) :
    substitutionPenalty? post t
      = (hardDecisionBlock? post).map (fun tStar =>
          Real.log (post tStar) - Real.log (post t)) := rfl

/-- `hardDecisionBlock?` definitional unfold: `List.finRange numCandidates |>.argmax post`. -/
example {numCandidates : Nat} (post : BlockPosterior numCandidates) :
    hardDecisionBlock? post = (List.finRange numCandidates).argmax post :=
  hardDecisionBlock?_eq post

/-- `hardDecisionBlock?` on the empty candidate set returns `none`. -/
example (post : BlockPosterior 0) :
    hardDecisionBlock? post = none :=
  hardDecisionBlock?_empty post

/-- ORBGRAND-AI returns `none` on the empty pattern list at the public entry point. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget [] = none :=
  orbgrandAi_empty_patterns Y Phi budget

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

/-- GRAND accepts the head candidate when its syndrome is zero, ignoring the tail. -/
example {n k : Nat} (H : ParityCheck n k) (Y Ng : Codeword n)
    (rest : List (Codeword n))
    (h : forall (i : Fin (n - k)),
          H.matrix.mulVec (Codeword.xor Y Ng) i = 0) :
    grandFind H Y (Ng :: rest) = some (Codeword.xor Y Ng) :=
  grandFind_cons_zero_syndrome H Y Ng rest h

/-- GRAND on the empty candidate list returns `none`. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    grandFind H Y [] = none :=
  grandFind_nil H Y

/-- GRAND discards the head when its syndrome is nonzero, recursing on the tail. -/
example {n k : Nat} (H : ParityCheck n k) (Y Ng : Codeword n)
    (rest : List (Codeword n))
    (h : ¬ (forall (i : Fin (n - k)),
            H.matrix.mulVec (Codeword.xor Y Ng) i = 0)) :
    grandFind H Y (Ng :: rest) = grandFind H Y rest :=
  grandFind_cons_nonzero_syndrome H Y Ng rest h

/-- GRAND soundness in `syndromeZero` form: a returned `c` has zero parity-check image. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) (c : Codeword n)
    (hfind : grandFind H Y order = some c) :
    forall (i : Fin (n - k)), H.matrix.mulVec c i = 0 :=
  grandFind_syndromeZero H Y order c hfind

/-- Forward direction of GRAND failure: `grandFind = none` implies every
    candidate noise has nonzero syndrome. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n))
    (hnone : grandFind H Y order = none)
    (Ng : Codeword n) (hmem : Ng ∈ order) :
    ¬ (forall (i : Fin (n - k)),
        H.matrix.mulVec (Codeword.xor Y Ng) i = 0) :=
  grandFind_none_imp H Y order hnone Ng hmem

/-- Backward direction of GRAND failure: if every candidate has nonzero
    syndrome, `grandFind` returns `none`. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n))
    (hnone : forall Ng, Ng ∈ order ->
      ¬ (forall (i : Fin (n - k)),
          H.matrix.mulVec (Codeword.xor Y Ng) i = 0)) :
    grandFind H Y order = none :=
  grandFind_none_mpr H Y order hnone

/-- GRAND is ML-optimal: when the candidate list is sorted by non-increasing
    posterior, the returned codeword's posterior beats any zero-syndrome candidate. -/
example {n k : Nat} (p : Codeword n -> Real) (H : ParityCheck n k)
    (Y : Codeword n) (order : List (Codeword n))
    (sorted_dec : forall (Ng Ng' : Codeword n) (i j : Nat),
        order[i]? = some Ng -> order[j]? = some Ng' ->
        i <= j -> p Ng' <= p Ng)
    (c : Codeword n) (hfind : grandFind H Y order = some c)
    (Ng' : Codeword n) (hin : Ng' ∈ order)
    (hsyn : forall (j : Fin (n - k)),
        H.matrix.mulVec (Codeword.xor Y Ng') j = 0) :
    p Ng' <= p (Codeword.xor Y c) :=
  grand_ml_optimal p H Y order sorted_dec c hfind Ng' hin hsyn

/-- When `Y` is a codeword, the syndrome-zero predicate holds iff `Ng` is a codeword. -/
example {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n)
    (h : forall i, H.matrix.mulVec Y i = 0) :
    syndromeZero H Y N_g <->
      forall (i : Fin (n - k)), H.matrix.mulVec N_g i = 0 :=
  syndromeZero_iff_noise_codeword H Y N_g h

/-- Syndrome decomposes as `H * Y + H * N_g`. -/
example {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n)
    (i : Fin (n - k)) :
    syndrome H Y N_g i = H.matrix.mulVec Y i + H.matrix.mulVec N_g i :=
  syndrome_decomp H Y N_g i

/-- Syndrome with zero noise reduces to `H * Y`. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) (i : Fin (n - k)) :
    syndrome H Y 0 i = H.matrix.mulVec Y i :=
  syndrome_zero_noise H Y i

/-- Syndrome with zero received vector reduces to `H * N_g`. -/
example {n k : Nat} (H : ParityCheck n k) (N_g : Codeword n) (i : Fin (n - k)) :
    syndrome H 0 N_g i = H.matrix.mulVec N_g i :=
  syndrome_zero_received H N_g i

/-- Syndrome is symmetric in `Y` and `N_g`. -/
example {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n)
    (i : Fin (n - k)) :
    syndrome H Y N_g i = syndrome H N_g Y i :=
  syndrome_comm H Y N_g i

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

/-- Same bucket implies equal logistic weight. -/
example {n : Nat} (pi : ReliabilityRank n) {w : Nat}
    {e1 e2 : Fin n -> Bool}
    (h1 : landslideBucket pi w e1) (h2 : landslideBucket pi w e2) :
    logisticWeight pi e1 = logisticWeight pi e2 :=
  landslideBucket_eq_of_same_bucket pi h1 h2

/-- Landslide bucket uniqueness: each pattern has at most one bucket. -/
example {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat} {e : Fin n -> Bool}
    (h1 : landslideBucket pi w1 e) (h2 : landslideBucket pi w2 e) :
    w1 = w2 :=
  landslideBucket_unique pi h1 h2

/-- ORBGRAND ordering soundness: lower logistic weight => earlier bucket. -/
example {n : Nat} (pi : ReliabilityRank n) (e1 e2 : Fin n -> Bool)
    (h : logisticWeight pi e1 < logisticWeight pi e2) :
    exists (i j : Nat),
      i < j /\
      landslideBucket pi i e1 /\
      landslideBucket pi j e2 :=
  orbgrand_ordering_sound pi e1 e2 h

/-- Yule-Walker bound: `rho_1^2 < 1` (the squared form). -/
example (rho1 rho2 : CorrelationCoefficient)
    (h : yuleWalker_variance_bound rho1 rho2) :
    rho1.val ^ 2 < 1 :=
  yuleWalker_rho1_sq_lt_one rho1 rho2 h

/-- Yule-Walker bound: numerator strictly less than denominator. -/
example (rho1 rho2 : CorrelationCoefficient)
    (h : yuleWalker_variance_bound rho1 rho2) :
    rho1.val ^ 2 + rho2.val ^ 2 - 2 * rho1.val ^ 2 * rho2.val
      < 1 - rho1.val ^ 2 :=
  yuleWalker_num_lt_denom rho1 rho2 h

/-- Yule-Walker bound after clearing the denominator and reorganising:
    `2 rho_1^2 + rho_2^2 - 2 rho_1^2 rho_2 < 1`. -/
example (rho1 rho2 : CorrelationCoefficient)
    (h : yuleWalker_variance_bound rho1 rho2) :
    2 * rho1.val ^ 2 + rho2.val ^ 2 - 2 * rho1.val ^ 2 * rho2.val < 1 :=
  yuleWalker_step3 rho1 rho2 h

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

/-- GRAND output syndrome decomposition: `H * Y i + H * Ng i = 0` componentwise. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) (c : Codeword n)
    (hfind : grandFind H Y order = some c) :
    exists Ng, Ng ∈ order /\ c = Codeword.xor Y Ng /\
      forall (i : Fin (n - k)),
        H.matrix.mulVec Y i + H.matrix.mulVec Ng i = 0 :=
  grandFind_output_syndrome_decomp H Y order c hfind

/-- GRAND output with noise recovery: `Y xor c = Ng` extracted from soundness. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order : List (Codeword n)) (c : Codeword n)
    (hfind : grandFind H Y order = some c) :
    (forall (i : Fin (n - k)), H.matrix.mulVec c i = 0)
    /\ (exists Ng, Ng ∈ order /\ c = Codeword.xor Y Ng
                /\ Codeword.xor Y c = Ng) :=
  grandFind_output_characterization H Y order c hfind

/-- `grandFind` on singleton list returns `none` iff the candidate has nonzero syndrome. -/
example {n k : Nat} (H : ParityCheck n k) (Y Ng : Codeword n) :
    grandFind H Y [Ng] = none
      <-> ¬ (forall (i : Fin (n - k)),
              H.matrix.mulVec (Codeword.xor Y Ng) i = 0) :=
  grandFind_singleton_none_iff H Y Ng

/-- `grandFind` cons dispatch: syndrome-check on the head determines branch. -/
example {n k : Nat} (H : ParityCheck n k) (Y Ng : Codeword n)
    (rest : List (Codeword n)) :
    grandFind H Y (Ng :: rest)
      = if _hp : forall (i : Fin (n - k)),
            H.matrix.mulVec (Codeword.xor Y Ng) i = 0 then
          some (Codeword.xor Y Ng)
        else
          grandFind H Y rest :=
  grandFind_cons_eq H Y Ng rest

/-- GRAND on a singleton candidate list reduces to a single syndrome check. -/
example {n k : Nat} (H : ParityCheck n k) (Y Ng : Codeword n) :
    grandFind H Y [Ng]
      = if _hp : forall (i : Fin (n - k)),
            H.matrix.mulVec (Codeword.xor Y Ng) i = 0 then
          some (Codeword.xor Y Ng)
        else
          none :=
  grandFind_singleton H Y Ng

/-- GRAND append: dispatch on prefix result. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order1 order2 : List (Codeword n)) :
    grandFind H Y (order1 ++ order2)
      = match grandFind H Y order1 with
        | some c => some c
        | none   => grandFind H Y order2 :=
  grandFind_append_eq H Y order1 order2

/-- GRAND on a `none`-yielding prefix: the suffix takes over. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n)
    (order1 : List (Codeword n)) (h_none : grandFind H Y order1 = none)
    (order2 : List (Codeword n)) :
    grandFind H Y (order1 ++ order2) = grandFind H Y order2 :=
  grandFind_append_none H Y order1 h_none order2

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

/-- ORBGRAND-AI loop `none` (with sufficient budget) implies every enumerated
    pattern fails an acceptance gate: either a substitution conflict, or
    `Phi` rejects the substituted candidate. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (steps : Nat)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (hbudget : patterns.length <= steps)
    (hnone : orbgrandAiLoop Y Phi steps patterns = none)
    (e : Fin (n_s / b) -> Fin numCandidates) (hmem : e ∈ patterns) :
    ¬ noSubstitutionConflict e ∨ ¬ Phi (substitute Y e) :=
  orbgrandAiLoop_none_imp_all_fail_of_budget
    Y Phi steps patterns hbudget hnone e hmem

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

/-- The zero channel is causal (vacuously: every entry is zero). -/
example {n_s : Nat} (noiseCov : CovMatrix n_s) :
    ({ channel := 0, noiseCov := noiseCov } : LinearIsi n_s).causal :=
  LinearIsi.zero_causal noiseCov

/-- The identity channel is causal (off-diagonals vanish). -/
example {n_s : Nat} (noiseCov : CovMatrix n_s) :
    ({ channel := 1, noiseCov := noiseCov } : LinearIsi n_s).causal :=
  LinearIsi.one_causal noiseCov

/-- The zero channel has any bandwidth. -/
example {n_s : Nat} (noiseCov : CovMatrix n_s) (b : Nat) :
    ({ channel := 0, noiseCov := noiseCov } : LinearIsi n_s).bandwidth b :=
  LinearIsi.zero_bandwidth noiseCov b

/-- The identity channel has any bandwidth. -/
example {n_s : Nat} (noiseCov : CovMatrix n_s) (b : Nat) :
    ({ channel := 1, noiseCov := noiseCov } : LinearIsi n_s).bandwidth b :=
  LinearIsi.one_bandwidth noiseCov b

/-- Receiving through the zero channel delivers only the noise: `receive X N = N`. -/
example {n_s : Nat} (noiseCov : CovMatrix n_s) (X N : SymbolVector n_s) :
    ({ channel := 0, noiseCov := noiseCov } : LinearIsi n_s).receive X N = N :=
  LinearIsi.zero_channel_receive noiseCov X N

/-- Capacity upper-bound definitional unfolding. -/
example (sigmaX : SignalPower) (sigmaN : NoisePower)
    (rho1 rho2 : CorrelationCoefficient) (n_s : Nat) :
    capacityUpperBound sigmaX sigmaN rho1 rho2 n_s
      = (1 / 2 : Real) * Real.log (2 * Real.pi * Real.exp 1)
        + (1 / 2 : Real) * Real.log (sigmaX.val + sigmaN.val)
        - (1 / 2 : Real)
            * Real.log (2 * Real.pi * Real.exp 1 * sigmaN.val)
        - (1 / (2 * (n_s : Real)))
            * Real.log
                (- (rho2.val - 1) ^ (n_s - 2)
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (n_s - 2)
                  / (rho1.val ^ 2 - 1) ^ (n_s - 3)) :=
  capacityUpperBound_eq sigmaX sigmaN rho1 rho2 n_s

/-- Constant log-density-ratio gives lim-inf information rate equal to the constant. -/
example (c : Real) :
    liminfInformationRate (fun _ => c) = c :=
  liminfInformationRate_const c

/-- Constant log-inverse-density gives lim-sup entropy rate equal to the constant. -/
example (c : Real) :
    limsupEntropyRate (fun _ => c) = c :=
  limsupEntropyRate_const c

/-- Zero log-density-ratio gives lim-inf information rate `0`. -/
example : liminfInformationRate (fun _ : Nat => (0 : Real)) = 0 :=
  liminfInformationRate_zero

/-- Zero log-inverse-density gives lim-sup entropy rate `0`. -/
example : limsupEntropyRate (fun _ : Nat => (0 : Real)) = 0 :=
  limsupEntropyRate_zero

/-- Unit log-density-ratio gives lim-inf information rate `1`. -/
example : liminfInformationRate (fun _ : Nat => (1 : Real)) = 1 :=
  liminfInformationRate_one

/-- Unit log-inverse-density gives lim-sup entropy rate `1`. -/
example : limsupEntropyRate (fun _ : Nat => (1 : Real)) = 1 :=
  limsupEntropyRate_one

/-- At constants, liminf information rate is at most limsup entropy rate. -/
example (c : Real) :
    liminfInformationRate (fun _ => c) <= limsupEntropyRate (fun _ => c) :=
  liminfInformationRate_le_limsupEntropyRate_const c

/-- For bounded sequences, liminf information rate <= limsup entropy rate. -/
example (u : Nat -> Real)
    (h : Filter.IsBoundedUnder (· <= ·) Filter.atTop u)
    (h' : Filter.IsBoundedUnder (· >= ·) Filter.atTop u) :
    liminfInformationRate u <= limsupEntropyRate u :=
  liminfInformationRate_le_limsupEntropyRate u h h'

/-- Eventually-equal sequences share the same liminf information rate. -/
example {u v : Nat -> Real} (h : ∀ᶠ n in Filter.atTop, u n = v n) :
    liminfInformationRate u = liminfInformationRate v :=
  liminfInformationRate_congr h

/-- Eventually-equal sequences share the same limsup entropy rate. -/
example {u v : Nat -> Real} (h : ∀ᶠ n in Filter.atTop, u n = v n) :
    limsupEntropyRate u = limsupEntropyRate v :=
  limsupEntropyRate_congr h

/-- AR(2) recurrence step at index 6. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 6
      = phi1 * ar2 phi1 phi2 z1 z2 5
        + phi2 * ar2 phi1 phi2 z1 z2 4 :=
  ar2_six phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 7. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 7
      = phi1 * ar2 phi1 phi2 z1 z2 6
        + phi2 * ar2 phi1 phi2 z1 z2 5 :=
  ar2_seven phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 8. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 8
      = phi1 * ar2 phi1 phi2 z1 z2 7
        + phi2 * ar2 phi1 phi2 z1 z2 6 :=
  ar2_eight phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 9. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 9
      = phi1 * ar2 phi1 phi2 z1 z2 8
        + phi2 * ar2 phi1 phi2 z1 z2 7 :=
  ar2_nine phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 10. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 10
      = phi1 * ar2 phi1 phi2 z1 z2 9
        + phi2 * ar2 phi1 phi2 z1 z2 8 :=
  ar2_ten phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 11. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 11
      = phi1 * ar2 phi1 phi2 z1 z2 10
        + phi2 * ar2 phi1 phi2 z1 z2 9 :=
  ar2_eleven phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 12. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 12
      = phi1 * ar2 phi1 phi2 z1 z2 11
        + phi2 * ar2 phi1 phi2 z1 z2 10 :=
  ar2_twelve phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 13. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 13
      = phi1 * ar2 phi1 phi2 z1 z2 12
        + phi2 * ar2 phi1 phi2 z1 z2 11 :=
  ar2_thirteen phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 14. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 14
      = phi1 * ar2 phi1 phi2 z1 z2 13
        + phi2 * ar2 phi1 phi2 z1 z2 12 :=
  ar2_fourteen phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 15. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 15
      = phi1 * ar2 phi1 phi2 z1 z2 14
        + phi2 * ar2 phi1 phi2 z1 z2 13 :=
  ar2_fifteen phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 16. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 16
      = phi1 * ar2 phi1 phi2 z1 z2 15
        + phi2 * ar2 phi1 phi2 z1 z2 14 :=
  ar2_sixteen phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 17. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 17
      = phi1 * ar2 phi1 phi2 z1 z2 16
        + phi2 * ar2 phi1 phi2 z1 z2 15 :=
  ar2_seventeen phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 18. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 18
      = phi1 * ar2 phi1 phi2 z1 z2 17
        + phi2 * ar2 phi1 phi2 z1 z2 16 :=
  ar2_eighteen phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 19. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 19
      = phi1 * ar2 phi1 phi2 z1 z2 18
        + phi2 * ar2 phi1 phi2 z1 z2 17 :=
  ar2_nineteen phi1 phi2 z1 z2

/-- `delayTapMatrix` fourth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 4) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 4 } :=
  delayTapMatrix_fourth_subdiag paths f_s i j h

/-- `delayTapMatrix` diagonal-collapse from val-equality. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val) :
    delayTapMatrix n_s paths f_s i j = delayTapMatrix n_s paths f_s i i :=
  delayTapMatrix_diag_of_val_eq paths f_s i j h

/-- `delayTapMatrix` with empty path family is zero. -/
example {n_s : Nat} (paths : Fin 0 -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) :
    delayTapMatrix n_s paths f_s i j = (0 : Complex) :=
  delayTapMatrix_empty paths f_s i j

/-- `dicode_channel` diagonal entry is `1`. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i : Fin n_s) :
    (dicode n_s sigma rho).channel i i = (1 : Complex) :=
  dicode_channel_diag sigma rho i

/-- `dicode` bandwidth widens to `2`. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 2 :=
  dicode_bandwidth_two sigma rho

/-- `rfView` bandwidth widens to `7`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 7 :=
  rfView_bandwidth_seven rowTaps sigma

/-- `NoisePower.mk?` at `0` round-trips. -/
example : NoisePower.mk? 0 = Except.ok ⟨0, le_refl 0⟩ :=
  NoisePower.mk?_zero

/-- `CorrelationCoefficient.mk?` at `0` round-trips. -/
example : CorrelationCoefficient.mk? 0
    = Except.ok ⟨0, le_refl 0, zero_le_one⟩ :=
  CorrelationCoefficient.mk?_zero

/-- `CorrelationCoefficient.mk?` at `1` round-trips. -/
example : CorrelationCoefficient.mk? 1
    = Except.ok ⟨1, zero_le_one, le_refl 1⟩ :=
  CorrelationCoefficient.mk?_one

/-- `cov2DetFormula` at zero-sigma vanishes at any successor size. -/
example (rho1 rho2 : CorrelationCoefficient) (n : Nat) :
    cov2DetFormula ⟨0, le_refl 0⟩ rho1 rho2 (n + 1) = 0 :=
  cov2DetFormula_zero_sigma_of_succ rho1 rho2 n

/-- `cov2DetFormula` at zero-sigma vanishes at `n_s = 4`. -/
example (rho1 rho2 : CorrelationCoefficient) :
    cov2DetFormula ⟨0, le_refl 0⟩ rho1 rho2 4 = 0 :=
  cov2DetFormula_zero_sigma_four rho1 rho2

/-- `entropyRate1_asymp` matches the explicit log expression (`.symm`). -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    Real.log (2 * Real.exp 1 * Real.pi * sigma.val
              * (1 - rho.val ^ 2))
      = entropyRate1_asymp sigma rho :=
  log_eq_entropyRate1_asymp sigma rho

/-- `entropyRate1_block` matches `entropyRate1` at `b.toNat` (`.symm`). -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    entropyRate1_block sigma rho b = entropyRate1 sigma rho b.toNat :=
  entropyRate1_block_eq_entropyRate1 sigma rho b

/-- Closed-form chain for `entropyRate1` at block. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    entropyRate1 sigma rho b.toNat
      = Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
        + (1 - (1 : Real) / (b.toNat : Real))
            * Real.log (1 - rho.val ^ 2) :=
  entropyRate1_at_block_eq_log_form sigma rho b

/-- `cov1_lag` at lag `-1`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-1) = sigma.val * rho.val :=
  cov1_lag_neg_one sigma rho

/-- `cov1_lag` at lag `-2`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-2) = sigma.val * rho.val ^ 2 :=
  cov1_lag_neg_two sigma rho

/-- `cov2_lag` recurrence at lag 7. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 7
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 6
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 5 :=
  cov2_lag_seven sigma rho1 rho2 beta1 beta2

/-- All-false pattern is in `landslideBucket` `0`. -/
example {n : Nat} (pi : ReliabilityRank n) :
    landslideBucket pi 0 (fun _ : Fin n => false) :=
  landslideBucket_const_false_zero pi

/-- `syndrome` at `(Y, Y)` is zero (XOR cancels). -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) (i : Fin (n - k)) :
    syndrome H Y Y i = 0 :=
  syndrome_self H Y i

/-- `syndrome` at `(0, 0)` is zero. -/
example {n k : Nat} (H : ParityCheck n k) (i : Fin (n - k)) :
    syndrome H 0 0 i = 0 :=
  syndrome_zero_zero H i

/-- `syndromeZero H Y Y` holds: GRAND accepts the trivial decoder. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    syndromeZero H Y Y :=
  syndromeZero_self H Y

/-- `argmax` reverses to `hardDecisionBlock?`. -/
example {numCandidates : Nat} (post : BlockPosterior numCandidates) :
    (List.finRange numCandidates).argmax post = hardDecisionBlock? post :=
  argmax_eq_hardDecisionBlock? post

/-- `orbgrandAiLoop` reverses to `orbgrandAi`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAiLoop Y Phi budget.toNat patterns
      = orbgrandAi (b := b) (numCandidates := numCandidates)
          Y Phi budget patterns :=
  orbgrandAiLoop_eq_orbgrandAi Y Phi budget patterns

/-- Public `orbgrandAi` at zero-budget on a non-empty pattern list is `none`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi (AbandonmentBudget.mk 0) (e :: rest) = none :=
  orbgrandAi_zero_steps_cons Y Phi e rest

/-- AR(2) recurrence step at index 20. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 20
      = phi1 * ar2 phi1 phi2 z1 z2 19
        + phi2 * ar2 phi1 phi2 z1 z2 18 :=
  ar2_twenty phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 21. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 21
      = phi1 * ar2 phi1 phi2 z1 z2 20
        + phi2 * ar2 phi1 phi2 z1 z2 19 :=
  ar2_twenty_one phi1 phi2 z1 z2

/-- AR(2) with `phi_1 = 0` at index 2 collapses to `phi_2 * z_1`. -/
example (phi2 z1 z2 : Complex) :
    ar2 0 phi2 z1 z2 2 = phi2 * z1 :=
  ar2_phi1_zero_two phi2 z1 z2

/-- `cov1_lag` at lag `-3`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-3) = sigma.val * rho.val ^ 3 :=
  cov1_lag_neg_three sigma rho

/-- `cov1_lag` at lag `4`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 4 = sigma.val * rho.val ^ 4 :=
  cov1_lag_four sigma rho

/-- `cov2_lag` recurrence at lag 8. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 8
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 7
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 6 :=
  cov2_lag_eight sigma rho1 rho2 beta1 beta2

/-- `LinearIsi.bandwidth` widens by two. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 2) :=
  LinearIsi.bandwidth_succ_succ h

/-- `LinearIsi.bandwidth` widens by any `k`. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (k : Nat)
    (h : ch.bandwidth b) :
    ch.bandwidth (b + k) :=
  LinearIsi.bandwidth_add k h

/-- Identity-channel receive at zero-signal zero-noise is zero. -/
example {n_s : Nat} (noiseCov : CovMatrix n_s) :
    ({ channel := 1, noiseCov := noiseCov } : LinearIsi n_s).receive 0 0
      = 0 :=
  LinearIsi.receive_one_zero_signal_zero_noise noiseCov

/-- Monotonicity of constant-sequence liminf information rate. -/
example {c1 c2 : Real} (h : c1 <= c2) :
    liminfInformationRate (fun _ => c1) <= liminfInformationRate (fun _ => c2) :=
  liminfInformationRate_const_mono h

/-- Eventually-le liminf monotonicity. -/
example {u v : Nat -> Real} (h : ∀ᶠ n in Filter.atTop, u n <= v n)
    (hu : Filter.IsBoundedUnder (· >= ·) Filter.atTop u)
    (hv : Filter.IsCoboundedUnder (· >= ·) Filter.atTop v) :
    liminfInformationRate u <= liminfInformationRate v :=
  liminfInformationRate_le_liminfInformationRate_of_le_eventually h hu hv

/-- Eventually-le limsup monotonicity. -/
example {u v : Nat -> Real} (h : ∀ᶠ n in Filter.atTop, u n <= v n)
    (hu : Filter.IsCoboundedUnder (· <= ·) Filter.atTop u)
    (hv : Filter.IsBoundedUnder (· <= ·) Filter.atTop v) :
    limsupEntropyRate u <= limsupEntropyRate v :=
  limsupEntropyRate_le_limsupEntropyRate_of_le_eventually h hu hv

/-- AR(2) recurrence step at index 22. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 22
      = phi1 * ar2 phi1 phi2 z1 z2 21
        + phi2 * ar2 phi1 phi2 z1 z2 20 :=
  ar2_twenty_two phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 23. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 23
      = phi1 * ar2 phi1 phi2 z1 z2 22
        + phi2 * ar2 phi1 phi2 z1 z2 21 :=
  ar2_twenty_three phi1 phi2 z1 z2

/-- `cov1_lag` at lag `-4`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-4) = sigma.val * rho.val ^ 4 :=
  cov1_lag_neg_four sigma rho

/-- `cov1_lag` at lag `5`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 5 = sigma.val * rho.val ^ 5 :=
  cov1_lag_five sigma rho

/-- `cov2_lag` recurrence at lag 9. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 9
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 8
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 7 :=
  cov2_lag_nine sigma rho1 rho2 beta1 beta2

/-- `cov2_lag` recurrence at lag 10. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 10
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 9
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 8 :=
  cov2_lag_ten sigma rho1 rho2 beta1 beta2

/-- Constant-sequence limsup is monotone in the constant. -/
example {c1 c2 : Real} (h : c1 <= c2) :
    limsupEntropyRate (fun _ => c1) <= limsupEntropyRate (fun _ => c2) :=
  limsupEntropyRate_const_mono h

/-- Constant liminf is bounded by a larger scalar. -/
example {c1 c2 : Real} (h : c1 <= c2) :
    liminfInformationRate (fun _ => c1) <= c2 :=
  liminfInformationRate_const_le_const h

/-- Scalar bounded by a larger constant limsup. -/
example {c1 c2 : Real} (h : c1 <= c2) :
    c1 <= limsupEntropyRate (fun _ => c2) :=
  const_le_limsupEntropyRate_const h

/-- `perturbChannel_zero` alternate-direction form. -/
example {n_s : Nat} (h : ChannelMatrix n_s) : h = perturbChannel h 0 :=
  perturbChannel_zero_eq_self h

/-- Two zero-perturbations collapse to identity. -/
example {n_s : Nat} (h : ChannelMatrix n_s) :
    perturbChannel (perturbChannel h 0) 0 = h :=
  perturbChannel_perturbChannel_zero_zero h

/-- Two zero-perturbations recover the original entry. -/
example {n_s : Nat} (h : ChannelMatrix n_s) (i j : Fin n_s) :
    perturbChannel (perturbChannel h 0) 0 i j = h i j :=
  perturbChannel_perturbChannel_zero_zero_apply h i j

/-- BPSK exceedance is non-negative. -/
example (s s_hat : Bool) : 0 <= bpsk.exceed s s_hat :=
  bpsk_exceed_nonneg s s_hat

/-- QPSK exceedance is non-negative. -/
example (s s_hat : Fin 4) : 0 <= qpsk.exceed s s_hat :=
  qpsk_exceed_nonneg s s_hat

/-- Trivial constellation exceedance is non-negative. -/
example (s s_hat : Unit) : 0 <= trivialConstellation.exceed s s_hat :=
  trivialConstellation_nonneg s s_hat

/-- `LinearIsi.bandwidth` widens by left-additive offset. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (k : Nat)
    (h : ch.bandwidth b) :
    ch.bandwidth (k + b) :=
  LinearIsi.bandwidth_add_left k h

/-- `LinearIsi.bandwidth` widens by three. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 3) :=
  LinearIsi.bandwidth_succ_succ_succ h

/-- `LinearIsi.receive_eq_iff_noise_eq` reversed reading. -/
example {n_s : Nat} (ch : LinearIsi n_s) (X N1 N2 : SymbolVector n_s) :
    N1 = N2 <-> ch.receive X N1 = ch.receive X N2 :=
  LinearIsi.receive_eq_iff_noise_eq_symm ch X N1 N2

/-- AR(2) recurrence step at index 24. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 24
      = phi1 * ar2 phi1 phi2 z1 z2 23
        + phi2 * ar2 phi1 phi2 z1 z2 22 :=
  ar2_twenty_four phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 25. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 25
      = phi1 * ar2 phi1 phi2 z1 z2 24
        + phi2 * ar2 phi1 phi2 z1 z2 23 :=
  ar2_twenty_five phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 26. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 26
      = phi1 * ar2 phi1 phi2 z1 z2 25
        + phi2 * ar2 phi1 phi2 z1 z2 24 :=
  ar2_twenty_six phi1 phi2 z1 z2

/-- `cov1_lag` at lag `-5`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-5) = sigma.val * rho.val ^ 5 :=
  cov1_lag_neg_five sigma rho

/-- `cov1_lag` at lag `6`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 6 = sigma.val * rho.val ^ 6 :=
  cov1_lag_six sigma rho

/-- `cov2_lag` recurrence at lag 11. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 11
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 10
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 9 :=
  cov2_lag_eleven sigma rho1 rho2 beta1 beta2

/-- `perturbChannel` right-identity pointwise. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i j : Fin n_s) :
    perturbChannel (perturbChannel h epsilon) 0 i j
      = perturbChannel h epsilon i j :=
  perturbChannel_perturbChannel_zero_right_apply h epsilon i j

/-- `perturbChannel` left-identity pointwise. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i j : Fin n_s) :
    perturbChannel (perturbChannel h 0) epsilon i j
      = perturbChannel h epsilon i j :=
  perturbChannel_perturbChannel_zero_left_apply h epsilon i j

/-- Factor-zero zeroes the perturbed entry. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i j : Fin n_s} (h_factor : (1 : Complex) + epsilon i j = 0) :
    perturbChannel h epsilon i j = 0 :=
  perturbChannel_factor_zero_apply h epsilon h_factor

/-- `LinearIsi.bandwidth` widens by four. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 4) :=
  LinearIsi.bandwidth_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by offset-plus-one. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (k : Nat)
    (h : ch.bandwidth b) :
    ch.bandwidth (b + k + 1) :=
  LinearIsi.bandwidth_add_succ k h

/-- `LinearIsi.receive_eq_iff_mulVec_eq` reversed reading. -/
example {n_s : Nat} (ch : LinearIsi n_s) (X1 X2 N : SymbolVector n_s) :
    ch.channel.mulVec X1 = ch.channel.mulVec X2
      <-> ch.receive X1 N = ch.receive X2 N :=
  LinearIsi.receive_eq_iff_mulVec_eq_symm ch X1 X2 N

/-- `syndromeZero` at zero/zero. -/
example {n k : Nat} (H : ParityCheck n k) :
    syndromeZero H (0 : Codeword n) (0 : Codeword n) :=
  syndromeZero_zero_zero H

/-- `syndromeZero` symmetric in (Y, N_g). -/
example {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n) :
    syndromeZero H Y N_g <-> syndromeZero H N_g Y :=
  syndromeZero_symm H Y N_g

/-- `syndrome` under XOR-cancel cycle. -/
example {n k : Nat} (H : ParityCheck n k) (Y c : Codeword n) (i : Fin (n - k)) :
    syndrome H Y (Codeword.xor Y c) i = H.matrix.mulVec c i :=
  syndrome_xor_self_noise H Y c i

/-- `orbgrandAi` at empty pattern list (reversed reading). -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget) :
    (none : Option (Codeword n_s))
      = orbgrandAi (b := b) (numCandidates := numCandidates)
          Y Phi budget [] :=
  orbgrandAi_nil_symm Y Phi budget

/-- `orbgrandAi` at zero budget on cons (reversed reading). -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates)) :
    (none : Option (Codeword n_s))
      = orbgrandAi (b := b) (numCandidates := numCandidates)
          Y Phi (AbandonmentBudget.mk 0) (e :: rest) :=
  orbgrandAi_zero_steps_cons_symm Y Phi e rest

/-- `orbgrandAi` with empty codebook on empty pattern list. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (budget : AbandonmentBudget) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) budget [] = none :=
  orbgrandAi_empty_codebook_nil Y budget

/-- `kendallTau` at singleton domain bounded by `1`. -/
example (a b : QueryOrder 1) : kendallTau a b <= 1 :=
  kendallTau_singleton_le_one a b

/-- `kendallTau` at empty domain is constant. -/
example (a b c d : QueryOrder 0) : kendallTau a b = kendallTau c d :=
  kendallTau_empty_eq a b c d

/-- `substitutionPenalty?` body unfold. -/
example {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates) :
    substitutionPenalty? post t
      = (hardDecisionBlock? post).map
          (fun tStar => Real.log (post tStar) - Real.log (post t)) :=
  substitutionPenalty?_eq post t

/-- `substitutionPenalty?` on empty candidate set is `none`. -/
example (post : BlockPosterior 0) (t : Fin 0) :
    substitutionPenalty? post t = none :=
  substitutionPenalty?_empty post t

/-- `orbgrandAi` with empty codebook on non-empty pattern list. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (budget : AbandonmentBudget)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) budget (e :: rest) = none :=
  orbgrandAi_empty_codebook_cons Y budget e rest

/-- AR(2) recurrence step at index 27. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 27
      = phi1 * ar2 phi1 phi2 z1 z2 26
        + phi2 * ar2 phi1 phi2 z1 z2 25 :=
  ar2_twenty_seven phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 28. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 28
      = phi1 * ar2 phi1 phi2 z1 z2 27
        + phi2 * ar2 phi1 phi2 z1 z2 26 :=
  ar2_twenty_eight phi1 phi2 z1 z2

/-- `cov1_lag` at lag `-6`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-6) = sigma.val * rho.val ^ 6 :=
  cov1_lag_neg_six sigma rho

/-- `cov1_lag` at lag `7`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 7 = sigma.val * rho.val ^ 7 :=
  cov1_lag_seven sigma rho

/-- `cov2_lag` recurrence at lag 12. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 12
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 11
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 10 :=
  cov2_lag_twelve sigma rho1 rho2 beta1 beta2

/-- `cov2_lag` recurrence at lag 13. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 13
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 12
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 11 :=
  cov2_lag_thirteen sigma rho1 rho2 beta1 beta2

/-- `LinearIsi.bandwidth` widens by five. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 5) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ h

/-- `BlockSize.mk?` at `1` round-trips. -/
example : BlockSize.mk? 1 = Except.ok ⟨1, Nat.one_pos⟩ :=
  BlockSize.mk?_one

/-- `SignalPower.mk?` at `0` round-trips. -/
example : SignalPower.mk? 0 = Except.ok ⟨0, le_refl 0⟩ :=
  SignalPower.mk?_zero

/-- `SamplingFreq.mk?` at `1` round-trips. -/
example : SamplingFreq.mk? 1 = Except.ok ⟨1, Real.zero_lt_one⟩ :=
  SamplingFreq.mk?_one

/-- AR(2) recurrence step at index 29. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 29
      = phi1 * ar2 phi1 phi2 z1 z2 28
        + phi2 * ar2 phi1 phi2 z1 z2 27 :=
  ar2_twenty_nine phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 30. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 30
      = phi1 * ar2 phi1 phi2 z1 z2 29
        + phi2 * ar2 phi1 phi2 z1 z2 28 :=
  ar2_thirty phi1 phi2 z1 z2

/-- AR(2) with `phi_2 = 0` at index 2 collapses to `phi_1 * z_2`. -/
example (phi1 z1 z2 : Complex) :
    ar2 phi1 0 z1 z2 2 = phi1 * z2 :=
  ar2_phi2_zero_two phi1 z1 z2

/-- `cov1_lag` at lag `-7`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-7) = sigma.val * rho.val ^ 7 :=
  cov1_lag_neg_seven sigma rho

/-- `cov1_lag` at lag `8`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 8 = sigma.val * rho.val ^ 8 :=
  cov1_lag_eight sigma rho

/-- `cov2_lag` recurrence at lag 14. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 14
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 13
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 12 :=
  cov2_lag_fourteen sigma rho1 rho2 beta1 beta2

/-- `perturbChannel_zero` pointwise. -/
example {n_s : Nat} (h : ChannelMatrix n_s) (i j : Fin n_s) :
    perturbChannel h 0 i j = h i j :=
  perturbChannel_zero_apply h i j

/-- `perturbChannel_zero` pointwise reverse-direction. -/
example {n_s : Nat} (h : ChannelMatrix n_s) (i j : Fin n_s) :
    h i j = perturbChannel h 0 i j :=
  perturbChannel_zero_eq_self_apply h i j

/-- `perturbChannel_zero_channel` pointwise. -/
example {n_s : Nat} (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    (i j : Fin n_s) :
    perturbChannel 0 epsilon i j = (0 : ChannelMatrix n_s) i j :=
  perturbChannel_zero_channel_apply epsilon i j

/-- `substitutionPenalty?` is `some` iff `hardDecisionBlock?` is `some`. -/
example {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates) :
    (substitutionPenalty? post t).isSome
      = (hardDecisionBlock? post).isSome :=
  substitutionPenalty?_isSome_iff_hardDecisionBlock?_isSome post t

/-- `substitutionPenalty?` is `none` iff `hardDecisionBlock?` is `none`. -/
example {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates) :
    (substitutionPenalty? post t).isNone
      = (hardDecisionBlock? post).isNone :=
  substitutionPenalty?_isNone_iff_hardDecisionBlock?_isNone post t

/-- `orbgrandAi` at zero budget on empty pattern list. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi (AbandonmentBudget.mk 0) [] = none :=
  orbgrandAi_zero_steps_nil Y Phi

/-- BPSK exceedance non-zero iff symbols differ. -/
example (s s_hat : Bool) : bpsk.exceed s s_hat ≠ 0 ↔ s ≠ s_hat :=
  bpsk_exceed_ne_zero_iff_ne s s_hat

/-- BPSK exceedance non-zero iff exceedance equals one (binary dichotomy). -/
example (s s_hat : Bool) :
    bpsk.exceed s s_hat ≠ 0 ↔ bpsk.exceed s s_hat = 1 :=
  bpsk_exceed_ne_zero_iff_eq_one s s_hat

/-- Trivial constellation exceedance is constant. -/
example (s1 s_hat1 s2 s_hat2 : Unit) :
    trivialConstellation.exceed s1 s_hat1
      = trivialConstellation.exceed s2 s_hat2 :=
  trivialConstellation_exceed_eq s1 s_hat1 s2 s_hat2

/-- Function-level self-syndrome vanishing. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    syndrome H Y Y = fun _ => 0 :=
  syndrome_self_funext H Y

/-- Syndrome XOR-cancel cycle on receiver side. -/
example {n k : Nat} (H : ParityCheck n k) (N_g c : Codeword n)
    (i : Fin (n - k)) :
    syndrome H (Codeword.xor N_g c) N_g i = H.matrix.mulVec c i :=
  syndrome_xor_self_received H N_g c i

/-- `syndromeZero` under noise XOR-cancel cycle is `c` codeword condition. -/
example {n k : Nat} (H : ParityCheck n k) (Y c : Codeword n) :
    syndromeZero H Y (Codeword.xor Y c)
      <-> forall (i : Fin (n - k)), H.matrix.mulVec c i = 0 :=
  syndromeZero_xor_self_noise_iff H Y c

/-- `delayTapMatrix` fifth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 5) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 5 } :=
  delayTapMatrix_fifth_subdiag paths f_s i j h

/-- `delayTapMatrix` sixth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 6) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 6 } :=
  delayTapMatrix_sixth_subdiag paths f_s i j h

/-- `delayTapMatrix` seventh sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 7) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 7 } :=
  delayTapMatrix_seventh_subdiag paths f_s i j h

/-- `perturbChannel` composition diagonal entry. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (ε₁ ε₂ : Matrix (Fin n_s) (Fin n_s) Complex) (i : Fin n_s) :
    perturbChannel (perturbChannel h ε₁) ε₂ i i
      = h i i * ((1 + ε₁ i i) * (1 + ε₂ i i)) :=
  perturbChannel_perturbChannel_apply_diag h ε₁ ε₂ i

/-- `perturbChannel` double-zero diagonal entry. -/
example {n_s : Nat} (h : ChannelMatrix n_s) (i : Fin n_s) :
    perturbChannel (perturbChannel h 0) 0 i i = h i i :=
  perturbChannel_perturbChannel_zero_zero_apply_diag h i

/-- `perturbChannel` right-zero diagonal entry. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i : Fin n_s) :
    perturbChannel (perturbChannel h epsilon) 0 i i
      = perturbChannel h epsilon i i :=
  perturbChannel_perturbChannel_zero_right_apply_diag h epsilon i

/-- `LinearIsi.bandwidth` from zero is universal. -/
example {n_s : Nat} {ch : LinearIsi n_s} (b : Nat)
    (h : ch.bandwidth 0) :
    ch.bandwidth b :=
  LinearIsi.bandwidth_of_zero b h

/-- Zero-channel zero-signal zero-noise receive is zero. -/
example {n_s : Nat} (noiseCov : CovMatrix n_s) :
    ({ channel := 0, noiseCov := noiseCov } : LinearIsi n_s).receive 0 0
      = 0 :=
  LinearIsi.receive_zero_channel_zero_signal_zero_noise noiseCov

/-- Generic zero-signal zero-noise receive is zero. -/
example {n_s : Nat} (ch : LinearIsi n_s) :
    ch.receive 0 0 = 0 :=
  LinearIsi.receive_zero_noise_zero_signal ch

/-- QPSK exceedance non-zero iff symbols differ. -/
example (s s_hat : Fin 4) : qpsk.exceed s s_hat ≠ 0 ↔ s ≠ s_hat :=
  qpsk_exceed_ne_zero_iff_ne s s_hat

/-- QPSK exceedance non-zero iff exceedance equals one. -/
example (s s_hat : Fin 4) :
    qpsk.exceed s s_hat ≠ 0 ↔ qpsk.exceed s s_hat = 1 :=
  qpsk_exceed_ne_zero_iff_eq_one s s_hat

/-- Eventually-le-constant transfers to liminf. -/
example {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, u n <= c)
    (hu : Filter.IsBoundedUnder (· >= ·) Filter.atTop u)
    (hv : Filter.IsCoboundedUnder (· >= ·) Filter.atTop
            (fun _ : Nat => c)) :
    liminfInformationRate u <= c :=
  liminfInformationRate_le_const_of_le_eventually h hu hv

/-- Eventually-ge-constant transfers to limsup. -/
example {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, c <= u n)
    (hc : Filter.IsCoboundedUnder (· <= ·) Filter.atTop
            (fun _ : Nat => c))
    (hu : Filter.IsBoundedUnder (· <= ·) Filter.atTop u) :
    c <= limsupEntropyRate u :=
  const_le_limsupEntropyRate_of_le_eventually h hc hu

/-- Constant liminf bounded by larger constant limsup. -/
example {c1 c2 : Real} (h : c1 <= c2) :
    liminfInformationRate (fun _ => c1) <= limsupEntropyRate (fun _ => c2) :=
  liminfInformationRate_const_le_limsupEntropyRate_const_mono h

/-- `entropyRate1_eq` symmetric form. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (n_s : Nat) :
    Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
      + (1 - (1 : Real) / (n_s : Real))
          * Real.log (1 - rho.val ^ 2)
      = entropyRate1 sigma rho n_s :=
  entropyRate1_eq_symm sigma rho n_s

/-- `entropyRate1_block_eq` symmetric form. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
      + (1 - (1 : Real) / (b.toNat : Real))
          * Real.log (1 - rho.val ^ 2)
      = entropyRate1_block sigma rho b :=
  entropyRate1_block_eq_symm sigma rho b

/-- `entropyRate2_eq` symmetric form. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (n_s : Nat) :
    (1 / 2 : Real)
        * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
      + (1 / (2 * (n_s : Real)))
          * Real.log
              (- (rho2.val - 1) ^ (n_s - 2)
                  * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (n_s - 2)
                / (rho1.val ^ 2 - 1) ^ (n_s - 3))
      = entropyRate2 sigma rho1 rho2 n_s :=
  entropyRate2_eq_symm sigma rho1 rho2 n_s

/-- Bucket uniqueness symmetric form. -/
example {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat} {e : Fin n -> Bool}
    (h1 : landslideBucket pi w1 e) (h2 : landslideBucket pi w2 e) :
    w2 = w1 :=
  landslideBucket_unique_symm pi h1 h2

/-- All-true pattern in its own bucket. -/
example {n : Nat} (pi : ReliabilityRank n) :
    landslideBucket pi (logisticWeight pi (fun _ : Fin n => true))
      (fun _ : Fin n => true) :=
  landslideBucket_const_true pi

/-- Bucket characterisation of the all-false pattern. -/
example {n : Nat} (pi : ReliabilityRank n) (w : Nat) :
    landslideBucket pi w (fun _ : Fin n => false) <-> w = 0 :=
  landslideBucket_const_false_iff pi w

/-- Reverse complement bler equation. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool)
    (h_meas :
      MeasurableSet
        {N : Section00.RealSymbolVector n_s | decode N = true}) :
    Section00.bler sigma (fun N => !decode N)
      = 1 - Section00.bler sigma decode :=
  Section00.bler_compl_eq_one_sub_bler sigma decode h_meas

/-- Disjunctive decoder dominates left. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma decode1
      ≤ Section00.bler sigma (fun N => decode1 N || decode2 N) :=
  Section00.bler_le_bler_or_left sigma decode1 decode2

/-- Disjunctive decoder dominates right. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma decode2
      ≤ Section00.bler sigma (fun N => decode1 N || decode2 N) :=
  Section00.bler_le_bler_or_right sigma decode1 decode2

/-- `bler` XOR-decoder bounded by OR-decoder. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (decode1 N) (decode2 N))
      ≤ Section00.bler sigma (fun N => decode1 N || decode2 N) :=
  Section00.bler_xor_le_bler_or sigma decode1 decode2

/-- `bler` AND-decoder bounded by OR-decoder. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode1 N && decode2 N)
      ≤ Section00.bler sigma (fun N => decode1 N || decode2 N) :=
  Section00.bler_and_le_bler_or sigma decode1 decode2

/-- `bler` `xor (!d1) d2 = xor d1 (!d2)` BLER. -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (!d1 N) (d2 N))
      = Section00.bler sigma (fun N => xor (d1 N) (!d2 N)) :=
  Section00.bler_not_xor_eq_xor_not sigma d1 d2

/-- `landslideBucket` definitional unfold. -/
example {n : Nat} (pi : ReliabilityRank n) (w : Nat) (e : Fin n -> Bool) :
    landslideBucket pi w e <-> logisticWeight pi e = w :=
  landslideBucket_iff pi w e

/-- `landslideBucket` const-true biconditional. -/
example {n : Nat} (pi : ReliabilityRank n) (w : Nat) :
    landslideBucket pi w (fun _ : Fin n => true)
      <-> w = logisticWeight pi (fun _ : Fin n => true) :=
  landslideBucket_const_true_iff pi w

/-- `landslideBucket` zero bucket via rank permutation. -/
example {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    landslideBucket pi 0 e <-> forall i, e (pi.perm i) = false :=
  landslideBucket_zero_iff_all_false_at_perm pi e

/-- `syndrome` XOR-cancel cycle on noise side, function-level. -/
example {n k : Nat} (H : ParityCheck n k) (Y c : Codeword n) :
    syndrome H Y (Codeword.xor Y c) = fun i => H.matrix.mulVec c i :=
  syndrome_xor_self_noise_funext H Y c

/-- `syndrome` XOR-cancel cycle on receiver side, function-level. -/
example {n k : Nat} (H : ParityCheck n k) (N_g c : Codeword n) :
    syndrome H (Codeword.xor N_g c) N_g = fun i => H.matrix.mulVec c i :=
  syndrome_xor_self_received_funext H N_g c

/-- `syndromeZero` under receiver XOR-cancel cycle. -/
example {n k : Nat} (H : ParityCheck n k) (N_g c : Codeword n) :
    syndromeZero H (Codeword.xor N_g c) N_g
      <-> forall (i : Fin (n - k)), H.matrix.mulVec c i = 0 :=
  syndromeZero_xor_self_received_iff H N_g c

/-- `entropyRate1_at_block_eq_log_form` symmetric form. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
      + (1 - (1 : Real) / (b.toNat : Real))
          * Real.log (1 - rho.val ^ 2)
      = entropyRate1 sigma rho b.toNat :=
  entropyRate1_at_block_eq_log_form_symm sigma rho b

/-- `entropyRate1_block` direct chain to log form. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    entropyRate1_block sigma rho b
      = Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
        + (1 - (1 : Real) / (b.toNat : Real))
            * Real.log (1 - rho.val ^ 2) :=
  entropyRate1_block_at_block_eq_log_form sigma rho b

/-- AR(2) recurrence step at index 31. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 31
      = phi1 * ar2 phi1 phi2 z1 z2 30
        + phi2 * ar2 phi1 phi2 z1 z2 29 :=
  ar2_thirty_one phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 32. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 32
      = phi1 * ar2 phi1 phi2 z1 z2 31
        + phi2 * ar2 phi1 phi2 z1 z2 30 :=
  ar2_thirty_two phi1 phi2 z1 z2

/-- AR(2) Fibonacci shape boundary at index 2. -/
example (z1 z2 : Complex) :
    ar2 1 1 z1 z2 2 = z2 + z1 :=
  ar2_phi1_one_phi2_one_two z1 z2

/-- AR(2) recurrence step at index 33. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 33
      = phi1 * ar2 phi1 phi2 z1 z2 32
        + phi2 * ar2 phi1 phi2 z1 z2 31 :=
  ar2_thirty_three phi1 phi2 z1 z2

/-- AR(2) phi1=0 boundary at index 3. -/
example (phi2 z1 z2 : Complex) :
    ar2 0 phi2 z1 z2 3 = phi2 * z2 :=
  ar2_phi1_zero_three phi2 z1 z2

/-- AR(2) phi2=0 boundary at index 3. -/
example (phi1 z1 z2 : Complex) :
    ar2 phi1 0 z1 z2 3 = phi1 * (phi1 * z2) :=
  ar2_phi2_zero_three phi1 z1 z2

/-- `cov1_lag` at lag `-8`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-8) = sigma.val * rho.val ^ 8 :=
  cov1_lag_neg_eight sigma rho

/-- `cov1_lag` at lag `9`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 9 = sigma.val * rho.val ^ 9 :=
  cov1_lag_nine sigma rho

/-- `cov2_lag` recurrence at lag 15. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 15
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 14
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 13 :=
  cov2_lag_fifteen sigma rho1 rho2 beta1 beta2

/-- `rfView` bandwidth widens to 8. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 8 :=
  rfView_bandwidth_eight rowTaps sigma

/-- `rfView` bandwidth widens to 9. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 9 :=
  rfView_bandwidth_nine rowTaps sigma

/-- `rfView` bandwidth widens by any additive offset. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower)
    (k : Nat) :
    (rfView n_s rowTaps sigma).bandwidth (6 + k) :=
  rfView_bandwidth_add rowTaps sigma k

/-- `dicode` bandwidth widens to 3. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 3 :=
  dicode_bandwidth_three sigma rho

/-- `dicode_channel` first sub-diagonal entry is `-rho`. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s) (h : i.val = j.val + 1) :
    (dicode n_s sigma rho).channel i j = -(rho.val : Complex) :=
  dicode_channel_subdiag sigma rho i j h

/-- `dicode_channel` off-diagonal entry is zero. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (i j : Fin n_s)
    (h1 : i.val ≠ j.val) (h2 : i.val ≠ j.val + 1) :
    (dicode n_s sigma rho).channel i j = (0 : Complex) :=
  dicode_channel_off sigma rho i j h1 h2

/-- `orbgrandAi` empty codebook at zero budget. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 0) patterns = none :=
  orbgrandAi_empty_codebook_zero_budget Y patterns

/-- `orbgrandAi` nil bridges to `orbgrandAiLoop` nil. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
        Y Phi budget []
      = orbgrandAiLoop (b := b) (numCandidates := numCandidates)
          Y Phi budget.toNat [] :=
  orbgrandAi_nil_eq_orbgrandAiLoop_nil Y Phi budget

/-- `substitutionPenalty?` raw-`argmax` unfold. -/
example {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates) :
    substitutionPenalty? post t
      = ((List.finRange numCandidates).argmax post).map
          (fun tStar => Real.log (post tStar) - Real.log (post t)) :=
  substitutionPenalty?_eq_argmax_map post t

/-- AR(2) recurrence step at index 34. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 34
      = phi1 * ar2 phi1 phi2 z1 z2 33
        + phi2 * ar2 phi1 phi2 z1 z2 32 :=
  ar2_thirty_four phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 35. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 35
      = phi1 * ar2 phi1 phi2 z1 z2 34
        + phi2 * ar2 phi1 phi2 z1 z2 33 :=
  ar2_thirty_five phi1 phi2 z1 z2

/-- AR(2) Fibonacci shape boundary at index 3. -/
example (z1 z2 : Complex) :
    ar2 1 1 z1 z2 3 = ar2 1 1 z1 z2 2 + z2 :=
  ar2_phi1_one_phi2_one_three z1 z2

/-- `cov1_lag` at lag `-9`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-9) = sigma.val * rho.val ^ 9 :=
  cov1_lag_neg_nine sigma rho

/-- `cov1_lag` at lag `10`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 10 = sigma.val * rho.val ^ 10 :=
  cov1_lag_ten sigma rho

/-- `cov2_lag` recurrence at lag 16. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 16
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 15
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 14 :=
  cov2_lag_sixteen sigma rho1 rho2 beta1 beta2

/-- `rfView` bandwidth widens to 10. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 10 :=
  rfView_bandwidth_ten rowTaps sigma

/-- `rfView` bandwidth widens to 11. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 11 :=
  rfView_bandwidth_eleven rowTaps sigma

/-- `rfView` bandwidth widens to 12. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 12 :=
  rfView_bandwidth_twelve rowTaps sigma

/-- AR(2) recurrence step at index 36. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 36
      = phi1 * ar2 phi1 phi2 z1 z2 35
        + phi2 * ar2 phi1 phi2 z1 z2 34 :=
  ar2_thirty_six phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 37. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 37
      = phi1 * ar2 phi1 phi2 z1 z2 36
        + phi2 * ar2 phi1 phi2 z1 z2 35 :=
  ar2_thirty_seven phi1 phi2 z1 z2

/-- AR(2) Fibonacci shape boundary at index 4. -/
example (z1 z2 : Complex) :
    ar2 1 1 z1 z2 4 = ar2 1 1 z1 z2 3 + ar2 1 1 z1 z2 2 :=
  ar2_phi1_one_phi2_one_four z1 z2

/-- `cov1_lag` at lag `-10`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-10) = sigma.val * rho.val ^ 10 :=
  cov1_lag_neg_ten sigma rho

/-- `cov1_lag` at lag `11`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 11 = sigma.val * rho.val ^ 11 :=
  cov1_lag_eleven sigma rho

/-- `cov2_lag` recurrence at lag 17. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 17
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 16
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 15 :=
  cov2_lag_seventeen sigma rho1 rho2 beta1 beta2

/-- `dicode` bandwidth widens to 4. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 4 :=
  dicode_bandwidth_four sigma rho

/-- `dicode` bandwidth widens to 5. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 5 :=
  dicode_bandwidth_five sigma rho

/-- `dicode` bandwidth widens by any additive offset. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (k : Nat) :
    (dicode n_s sigma rho).bandwidth (1 + k) :=
  dicode_bandwidth_add sigma rho k

/-- `LinearIsi.bandwidth` widens by two chained additive offsets. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (k m : Nat)
    (h : ch.bandwidth b) :
    ch.bandwidth (b + k + m) :=
  LinearIsi.bandwidth_add_add k m h

/-- `LinearIsi.bandwidth` widens by one then by an offset. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (k : Nat)
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 1 + k) :=
  LinearIsi.bandwidth_succ_add k h

/-- `LinearIsi.bandwidth_of_zero` plus successor. -/
example {n_s : Nat} {ch : LinearIsi n_s} (b : Nat)
    (h : ch.bandwidth 0) :
    ch.bandwidth (b + 1) :=
  LinearIsi.bandwidth_of_zero_succ b h

/-- BPSK diagonal at `true`. -/
example : bpsk.exceed true true = 0 :=
  bpsk_exceed_true_true

/-- BPSK diagonal at `false`. -/
example : bpsk.exceed false false = 0 :=
  bpsk_exceed_false_false

/-- Trivial-constellation diagonal vanishes. -/
example (s : Unit) : trivialConstellation.exceed s s = 0 :=
  trivialConstellation_exceed_self s

/-- AR(2) recurrence step at index 38. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 38
      = phi1 * ar2 phi1 phi2 z1 z2 37
        + phi2 * ar2 phi1 phi2 z1 z2 36 :=
  ar2_thirty_eight phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 39. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 39
      = phi1 * ar2 phi1 phi2 z1 z2 38
        + phi2 * ar2 phi1 phi2 z1 z2 37 :=
  ar2_thirty_nine phi1 phi2 z1 z2

/-- AR(2) phi1=0 boundary at index 4. -/
example (phi2 z1 z2 : Complex) :
    ar2 0 phi2 z1 z2 4 = phi2 * (phi2 * z1) :=
  ar2_phi1_zero_four phi2 z1 z2

/-- `cov1_lag` at lag `-11`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-11) = sigma.val * rho.val ^ 11 :=
  cov1_lag_neg_eleven sigma rho

/-- `cov1_lag` at lag `12`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 12 = sigma.val * rho.val ^ 12 :=
  cov1_lag_twelve sigma rho

/-- `cov2_lag` recurrence at lag 18. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 18
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 17
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 16 :=
  cov2_lag_eighteen sigma rho1 rho2 beta1 beta2

/-- `rfView` bandwidth widens to 13. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 13 :=
  rfView_bandwidth_thirteen rowTaps sigma

/-- `rfView` bandwidth widens to 14. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 14 :=
  rfView_bandwidth_fourteen rowTaps sigma

/-- `rfView` bandwidth widens to 15. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 15 :=
  rfView_bandwidth_fifteen rowTaps sigma

/-- `dicode` bandwidth widens to 6. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 6 :=
  dicode_bandwidth_six sigma rho

/-- `dicode` bandwidth widens to 7. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 7 :=
  dicode_bandwidth_seven sigma rho

/-- `dicode` bandwidth widens to 8. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 8 :=
  dicode_bandwidth_eight sigma rho

/-- `syndrome H Y 0` function-extensional form. -/
example {n k : Nat} (H : ParityCheck n k) (Y : Codeword n) :
    syndrome H Y 0 = fun i => H.matrix.mulVec Y i :=
  syndrome_zero_noise_funext H Y

/-- `syndrome H 0 N_g` function-extensional form. -/
example {n k : Nat} (H : ParityCheck n k) (N_g : Codeword n) :
    syndrome H 0 N_g = fun i => H.matrix.mulVec N_g i :=
  syndrome_zero_received_funext H N_g

/-- `syndrome` symmetry function-extensional form. -/
example {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n) :
    syndrome H Y N_g = syndrome H N_g Y :=
  syndrome_comm_funext H Y N_g

/-- AR(2) recurrence step at index 40. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 40
      = phi1 * ar2 phi1 phi2 z1 z2 39
        + phi2 * ar2 phi1 phi2 z1 z2 38 :=
  ar2_forty phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 41. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 41
      = phi1 * ar2 phi1 phi2 z1 z2 40
        + phi2 * ar2 phi1 phi2 z1 z2 39 :=
  ar2_forty_one phi1 phi2 z1 z2

/-- AR(2) phi2=0 boundary at index 4. -/
example (phi1 z1 z2 : Complex) :
    ar2 phi1 0 z1 z2 4 = phi1 * (phi1 * (phi1 * z2)) :=
  ar2_phi2_zero_four phi1 z1 z2

/-- `cov1_lag` at lag `-12`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-12) = sigma.val * rho.val ^ 12 :=
  cov1_lag_neg_twelve sigma rho

/-- `cov1_lag` at lag `13`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 13 = sigma.val * rho.val ^ 13 :=
  cov1_lag_thirteen sigma rho

/-- `cov1_lag` at lag `-13`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-13) = sigma.val * rho.val ^ 13 :=
  cov1_lag_neg_thirteen sigma rho

/-- `cov1_lag` at lag `14`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 14 = sigma.val * rho.val ^ 14 :=
  cov1_lag_fourteen sigma rho

/-- `cov2_lag` recurrence at lag 19. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 19
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 18
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 17 :=
  cov2_lag_nineteen sigma rho1 rho2 beta1 beta2

/-- `cov2_lag` recurrence at lag 20. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 20
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 19
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 18 :=
  cov2_lag_twenty sigma rho1 rho2 beta1 beta2

/-- `rfView` bandwidth widens to 16. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 16 :=
  rfView_bandwidth_sixteen rowTaps sigma

/-- `rfView` bandwidth widens to 17. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 17 :=
  rfView_bandwidth_seventeen rowTaps sigma

/-- `rfView` bandwidth widens to 18. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 18 :=
  rfView_bandwidth_eighteen rowTaps sigma

/-- `dicode` bandwidth widens to 9. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 9 :=
  dicode_bandwidth_nine sigma rho

/-- `dicode` bandwidth widens to 10. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 10 :=
  dicode_bandwidth_ten sigma rho

/-- `dicode` bandwidth widens from `5` by any additive offset. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient)
    (k : Nat) :
    (dicode n_s sigma rho).bandwidth (5 + k) :=
  dicode_bandwidth_five_add sigma rho k

/-- `syndrome H 0 0` function-extensional form. -/
example {n k : Nat} (H : ParityCheck n k) :
    syndrome H (0 : Codeword n) (0 : Codeword n) = fun _ => 0 :=
  syndrome_zero_zero_funext H

/-- `syndromeZero` at zero/zero via self-acceptance. -/
example {n k : Nat} (H : ParityCheck n k) :
    syndromeZero H (0 : Codeword n) (0 : Codeword n) :=
  syndromeZero_self_of_zero H

/-- `delayTapMatrix` eighth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 8) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 8 } :=
  delayTapMatrix_eighth_subdiag paths f_s i j h

/-- `delayTapMatrix` ninth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 9) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 9 } :=
  delayTapMatrix_ninth_subdiag paths f_s i j h

/-- `delayTapMatrix` tenth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 10) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 10 } :=
  delayTapMatrix_tenth_subdiag paths f_s i j h

/-- `delayTapMatrix` eleventh sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 11) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 11 } :=
  delayTapMatrix_eleventh_subdiag paths f_s i j h

/-- `delayTapMatrix` twelfth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 12) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 12 } :=
  delayTapMatrix_twelfth_subdiag paths f_s i j h

/-- `delayTapMatrix` thirteenth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 13) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 13 } :=
  delayTapMatrix_thirteenth_subdiag paths f_s i j h

/-- `delayTapMatrix` fourteenth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 14) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 14 } :=
  delayTapMatrix_fourteenth_subdiag paths f_s i j h

/-- `delayTapMatrix` fifteenth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 15) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 15 } :=
  delayTapMatrix_fifteenth_subdiag paths f_s i j h

/-- `delayTapMatrix` sixteenth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 16) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 16 } :=
  delayTapMatrix_sixteenth_subdiag paths f_s i j h

/-- `delayTapMatrix` seventeenth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 17) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 17 } :=
  delayTapMatrix_seventeenth_subdiag paths f_s i j h

/-- `delayTapMatrix` eighteenth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 18) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 18 } :=
  delayTapMatrix_eighteenth_subdiag paths f_s i j h

/-- `delayTapMatrix` nineteenth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 19) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 19 } :=
  delayTapMatrix_nineteenth_subdiag paths f_s i j h

/-- `delayTapMatrix` twentieth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 20) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 20 } :=
  delayTapMatrix_twentieth_subdiag paths f_s i j h

/-- `delayTapMatrix` twenty-first sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 21) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 21 } :=
  delayTapMatrix_twenty_first_subdiag paths f_s i j h

/-- `delayTapMatrix` twenty-second sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 22) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 22 } :=
  delayTapMatrix_twenty_second_subdiag paths f_s i j h

/-- `delayTapMatrix` twenty-third sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 23) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 23 } :=
  delayTapMatrix_twenty_third_subdiag paths f_s i j h

/-- `delayTapMatrix` twenty-fourth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 24) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 24 } :=
  delayTapMatrix_twenty_fourth_subdiag paths f_s i j h

/-- `delayTapMatrix` twenty-fifth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 25) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 25 } :=
  delayTapMatrix_twenty_fifth_subdiag paths f_s i j h

/-- `delayTapMatrix` twenty-sixth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 26) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 26 } :=
  delayTapMatrix_twenty_sixth_subdiag paths f_s i j h

/-- `delayTapMatrix` twenty-seventh sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 27) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 27 } :=
  delayTapMatrix_twenty_seventh_subdiag paths f_s i j h

/-- `delayTapMatrix` twenty-eighth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 28) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 28 } :=
  delayTapMatrix_twenty_eighth_subdiag paths f_s i j h

/-- `delayTapMatrix` twenty-ninth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 29) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 29 } :=
  delayTapMatrix_twenty_ninth_subdiag paths f_s i j h

/-- `delayTapMatrix` thirtieth sub-diagonal. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (h : i.val = j.val + 30) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 30 } :=
  delayTapMatrix_thirtieth_subdiag paths f_s i j h

/-- `dicode` bandwidth widens to 11. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 11 :=
  dicode_bandwidth_eleven sigma rho

/-- `dicode` bandwidth widens to 12. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 12 :=
  dicode_bandwidth_twelve sigma rho

/-- `dicode` bandwidth widens to 13. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 13 :=
  dicode_bandwidth_thirteen sigma rho

/-- `dicode` bandwidth widens to 14. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 14 :=
  dicode_bandwidth_fourteen sigma rho

/-- `dicode` bandwidth widens to 15. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 15 :=
  dicode_bandwidth_fifteen sigma rho

/-- `dicode` bandwidth widens to 16. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 16 :=
  dicode_bandwidth_sixteen sigma rho

/-- `dicode` bandwidth widens to 17. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 17 :=
  dicode_bandwidth_seventeen sigma rho

/-- `dicode` bandwidth widens to 18. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 18 :=
  dicode_bandwidth_eighteen sigma rho

/-- `dicode` bandwidth widens to 19. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 19 :=
  dicode_bandwidth_nineteen sigma rho

/-- `dicode` bandwidth widens to 20. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 20 :=
  dicode_bandwidth_twenty sigma rho

/-- `dicode` bandwidth widens to 21. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 21 :=
  dicode_bandwidth_twenty_one sigma rho

/-- `dicode` bandwidth widens to 22. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 22 :=
  dicode_bandwidth_twenty_two sigma rho

/-- `dicode` bandwidth widens to 23. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 23 :=
  dicode_bandwidth_twenty_three sigma rho

/-- `dicode` bandwidth widens to 24. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 24 :=
  dicode_bandwidth_twenty_four sigma rho

/-- `dicode` bandwidth widens to 25. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 25 :=
  dicode_bandwidth_twenty_five sigma rho

/-- `dicode` bandwidth widens to 26. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 26 :=
  dicode_bandwidth_twenty_six sigma rho

/-- `dicode` bandwidth widens to 27. -/
example {n_s : Nat} (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (dicode n_s sigma rho).bandwidth 27 :=
  dicode_bandwidth_twenty_seven sigma rho

/-- `rfView` bandwidth widens to 19. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 19 :=
  rfView_bandwidth_nineteen rowTaps sigma

/-- `rfView` bandwidth widens to 20. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 20 :=
  rfView_bandwidth_twenty rowTaps sigma

/-- `rfView` bandwidth widens to 21. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 21 :=
  rfView_bandwidth_twenty_one rowTaps sigma

/-- `rfView` bandwidth widens to 22. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 22 :=
  rfView_bandwidth_twenty_two rowTaps sigma

/-- `rfView` bandwidth widens to 23. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 23 :=
  rfView_bandwidth_twenty_three rowTaps sigma

/-- `rfView` bandwidth widens to 24. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 24 :=
  rfView_bandwidth_twenty_four rowTaps sigma

/-- `rfView` bandwidth widens to 25. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 25 :=
  rfView_bandwidth_twenty_five rowTaps sigma

/-- `rfView` bandwidth widens to 26. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 26 :=
  rfView_bandwidth_twenty_six rowTaps sigma

/-- `rfView` bandwidth widens to 27. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 27 :=
  rfView_bandwidth_twenty_seven rowTaps sigma

/-- `rfView` bandwidth widens to 28. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 28 :=
  rfView_bandwidth_twenty_eight rowTaps sigma

/-- `rfView` bandwidth widens to 29. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 29 :=
  rfView_bandwidth_twenty_nine rowTaps sigma

/-- `rfView` bandwidth widens to 30. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 30 :=
  rfView_bandwidth_thirty rowTaps sigma

/-- `rfView` bandwidth widens to 31. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 31 :=
  rfView_bandwidth_thirty_one rowTaps sigma

/-- `rfView` bandwidth widens to 32. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 32 :=
  rfView_bandwidth_thirty_two rowTaps sigma

/-- `rfView` bandwidth widens to 33. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 33 :=
  rfView_bandwidth_thirty_three rowTaps sigma

/-- `rfView` bandwidth widens to 34. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 34 :=
  rfView_bandwidth_thirty_four rowTaps sigma

/-- `rfView` bandwidth widens to 35. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).bandwidth 35 :=
  rfView_bandwidth_thirty_five rowTaps sigma

/-- `LinearIsi.bandwidth` widens by six. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 6) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by seven. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 7) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by eight. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 8) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by nine. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 9) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by ten. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 10) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by eleven. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 11) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by twelve. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 12) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by thirteen. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 13) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by fourteen. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 14) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by fifteen. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 15) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by sixteen. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 16) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by seventeen. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 17) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by eighteen. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 18) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by nineteen. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 19) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by twenty. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 20) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by twenty-one. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 21) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `LinearIsi.bandwidth` widens by twenty-two. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat} (h : ch.bandwidth b) :
    ch.bandwidth (b + 22) :=
  LinearIsi.bandwidth_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ_succ h

/-- `BlockSize.mk?` round-trips through `2`. -/
example : BlockSize.mk? 2 = Except.ok ⟨2, Nat.succ_pos 1⟩ :=
  BlockSize.mk?_two

/-- `CodewordLength.mk?` round-trips through `2`. -/
example : CodewordLength.mk? 2 = Except.ok ⟨2, Nat.succ_pos 1⟩ :=
  CodewordLength.mk?_two

/-- `SamplingFreq.mk?` round-trips through `2`. -/
example : SamplingFreq.mk? 2 = Except.ok ⟨2, zero_lt_two⟩ :=
  SamplingFreq.mk?_two

/-- `BlockSize.mk?` round-trips through `3`. -/
example : BlockSize.mk? 3 = Except.ok ⟨3, Nat.succ_pos 2⟩ :=
  BlockSize.mk?_three

/-- `CodewordLength.mk?` round-trips through `3`. -/
example : CodewordLength.mk? 3 = Except.ok ⟨3, Nat.succ_pos 2⟩ :=
  CodewordLength.mk?_three

/-- `SamplingFreq.mk?` round-trips through `3`. -/
example : SamplingFreq.mk? 3 = Except.ok ⟨3, zero_lt_three⟩ :=
  SamplingFreq.mk?_three

/-- `BlockSize.mk?` round-trips through `4`. -/
example : BlockSize.mk? 4 = Except.ok ⟨4, Nat.succ_pos 3⟩ :=
  BlockSize.mk?_four

/-- `CodewordLength.mk?` round-trips through `4`. -/
example : CodewordLength.mk? 4 = Except.ok ⟨4, Nat.succ_pos 3⟩ :=
  CodewordLength.mk?_four

/-- `SamplingFreq.mk?` round-trips through `4`. -/
example : SamplingFreq.mk? 4 = Except.ok ⟨4, zero_lt_four⟩ :=
  SamplingFreq.mk?_four

/-- `BlockSize.mk?` round-trips through `5`. -/
example : BlockSize.mk? 5 = Except.ok ⟨5, Nat.succ_pos 4⟩ :=
  BlockSize.mk?_five

/-- `CodewordLength.mk?` round-trips through `5`. -/
example : CodewordLength.mk? 5 = Except.ok ⟨5, Nat.succ_pos 4⟩ :=
  CodewordLength.mk?_five

/-- `SamplingFreq.mk?` round-trips through `5`. -/
example : SamplingFreq.mk? 5 = Except.ok ⟨5, Nat.ofNat_pos⟩ :=
  SamplingFreq.mk?_five

/-- `BlockSize.mk?` round-trips through `6`. -/
example : BlockSize.mk? 6 = Except.ok ⟨6, Nat.succ_pos 5⟩ :=
  BlockSize.mk?_six

/-- `CodewordLength.mk?` round-trips through `6`. -/
example : CodewordLength.mk? 6 = Except.ok ⟨6, Nat.succ_pos 5⟩ :=
  CodewordLength.mk?_six

/-- `SamplingFreq.mk?` round-trips through `6`. -/
example : SamplingFreq.mk? 6 = Except.ok ⟨6, Nat.ofNat_pos⟩ :=
  SamplingFreq.mk?_six

/-- `BlockSize.mk?` round-trips through `7`. -/
example : BlockSize.mk? 7 = Except.ok ⟨7, Nat.succ_pos 6⟩ :=
  BlockSize.mk?_seven

/-- `CodewordLength.mk?` round-trips through `7`. -/
example : CodewordLength.mk? 7 = Except.ok ⟨7, Nat.succ_pos 6⟩ :=
  CodewordLength.mk?_seven

/-- `cov1_lag` at lag `-14`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-14) = sigma.val * rho.val ^ 14 :=
  cov1_lag_neg_fourteen sigma rho

/-- `cov1_lag` at lag `15`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 15 = sigma.val * rho.val ^ 15 :=
  cov1_lag_fifteen sigma rho

/-- `cov1_lag` at lag `-15`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-15) = sigma.val * rho.val ^ 15 :=
  cov1_lag_neg_fifteen sigma rho

/-- `cov1_lag` at lag `16`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 16 = sigma.val * rho.val ^ 16 :=
  cov1_lag_sixteen sigma rho

/-- `cov1_lag` at lag `-16`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-16) = sigma.val * rho.val ^ 16 :=
  cov1_lag_neg_sixteen sigma rho

/-- `cov1_lag` at lag `17`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 17 = sigma.val * rho.val ^ 17 :=
  cov1_lag_seventeen sigma rho

/-- `cov1_lag` at lag `-17`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-17) = sigma.val * rho.val ^ 17 :=
  cov1_lag_neg_seventeen sigma rho

/-- `cov1_lag` at lag `18`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 18 = sigma.val * rho.val ^ 18 :=
  cov1_lag_eighteen sigma rho

/-- `cov1_lag` at lag `-18`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-18) = sigma.val * rho.val ^ 18 :=
  cov1_lag_neg_eighteen sigma rho

/-- `cov1_lag` at lag `19`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 19 = sigma.val * rho.val ^ 19 :=
  cov1_lag_nineteen sigma rho

/-- `cov1_lag` at lag `-19`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-19) = sigma.val * rho.val ^ 19 :=
  cov1_lag_neg_nineteen sigma rho

/-- `cov1_lag` at lag `20`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 20 = sigma.val * rho.val ^ 20 :=
  cov1_lag_twenty sigma rho

/-- `cov1_lag` at lag `-20`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-20) = sigma.val * rho.val ^ 20 :=
  cov1_lag_neg_twenty sigma rho

/-- `cov1_lag` at lag `21`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 21 = sigma.val * rho.val ^ 21 :=
  cov1_lag_twenty_one sigma rho

/-- `cov1_lag` at lag `-21`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-21) = sigma.val * rho.val ^ 21 :=
  cov1_lag_neg_twenty_one sigma rho

/-- `cov1_lag` at lag `22`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 22 = sigma.val * rho.val ^ 22 :=
  cov1_lag_twenty_two sigma rho

/-- `cov1_lag` at lag `-22`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho (-22) = sigma.val * rho.val ^ 22 :=
  cov1_lag_neg_twenty_two sigma rho

/-- `entropyRate2` at the boundary block size `n_s = 4`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 4
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((4 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 2
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 2
                  / (rho1.val ^ 2 - 1) ^ 1) :=
  entropyRate2_at_four_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 5`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 5
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((5 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 3
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 3
                  / (rho1.val ^ 2 - 1) ^ 2) :=
  entropyRate2_at_five_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 6`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 6
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((6 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 4
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 4
                  / (rho1.val ^ 2 - 1) ^ 3) :=
  entropyRate2_at_six_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 7`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 7
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((7 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 5
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 5
                  / (rho1.val ^ 2 - 1) ^ 4) :=
  entropyRate2_at_seven_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 8`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 8
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((8 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 6
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 6
                  / (rho1.val ^ 2 - 1) ^ 5) :=
  entropyRate2_at_eight_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 9`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 9
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((9 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 7
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 7
                  / (rho1.val ^ 2 - 1) ^ 6) :=
  entropyRate2_at_nine_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 10`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 10
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((10 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 8
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 8
                  / (rho1.val ^ 2 - 1) ^ 7) :=
  entropyRate2_at_ten_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 11`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 11
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((11 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 9
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 9
                  / (rho1.val ^ 2 - 1) ^ 8) :=
  entropyRate2_at_eleven_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 12`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 12
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((12 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 10
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 10
                  / (rho1.val ^ 2 - 1) ^ 9) :=
  entropyRate2_at_twelve_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 13`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 13
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((13 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 11
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 11
                  / (rho1.val ^ 2 - 1) ^ 10) :=
  entropyRate2_at_thirteen_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 14`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 14
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((14 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 12
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 12
                  / (rho1.val ^ 2 - 1) ^ 11) :=
  entropyRate2_at_fourteen_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 15`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 15
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((15 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 13
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 13
                  / (rho1.val ^ 2 - 1) ^ 12) :=
  entropyRate2_at_fifteen_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 16`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 16
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((16 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 14
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 14
                  / (rho1.val ^ 2 - 1) ^ 13) :=
  entropyRate2_at_sixteen_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 17`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 17
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((17 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 15
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 15
                  / (rho1.val ^ 2 - 1) ^ 14) :=
  entropyRate2_at_seventeen_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 18`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 18
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((18 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 16
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 16
                  / (rho1.val ^ 2 - 1) ^ 15) :=
  entropyRate2_at_eighteen_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 19`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 19
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((19 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 17
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 17
                  / (rho1.val ^ 2 - 1) ^ 16) :=
  entropyRate2_at_nineteen_eq_log_form sigma rho1 rho2

/-- `entropyRate2` at the block size `n_s = 20`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    entropyRate2 sigma rho1 rho2 20
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * ((20 : Nat) : Real)))
            * Real.log
                (- (rho2.val - 1) ^ 18
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ 18
                  / (rho1.val ^ 2 - 1) ^ 17) :=
  entropyRate2_at_twenty_eq_log_form sigma rho1 rho2

/-- `limsupEntropyRate` collapses on eventually-constant sequences. -/
example {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, u n = c) :
    limsupEntropyRate u = c :=
  limsupEntropyRate_eq_const_of_eventually_const h

/-- `liminfInformationRate` collapses on eventually-constant sequences. -/
example {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, u n = c) :
    liminfInformationRate u = c :=
  liminfInformationRate_eq_const_of_eventually_const h

/-- `liminf` and `limsup` coincide on eventually-constant sequences. -/
example {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, u n = c) :
    liminfInformationRate u = limsupEntropyRate u :=
  liminfInformationRate_eq_limsupEntropyRate_of_eventually_const h

/-- Cross-sequence collapse at a shared eventual constant. -/
example {u v : Nat -> Real} {c : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n = c)
    (hv : ∀ᶠ n in Filter.atTop, v n = c) :
    liminfInformationRate u = limsupEntropyRate v :=
  liminfInformationRate_eq_limsupEntropyRate_of_eventually_const_pair hu hv

/-- Cross-sequence inequality at a monotone eventual constant pair. -/
example {u v : Nat -> Real} {c1 c2 : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n = c1)
    (hv : ∀ᶠ n in Filter.atTop, v n = c2)
    (h : c1 <= c2) :
    liminfInformationRate u <= limsupEntropyRate v :=
  liminfInformationRate_le_limsupEntropyRate_of_eventually_const_mono hu hv h

/-- Reverse cross-sequence inequality at a monotone eventual constant pair. -/
example {u v : Nat -> Real} {c1 c2 : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n = c1)
    (hv : ∀ᶠ n in Filter.atTop, v n = c2)
    (h : c2 <= c1) :
    limsupEntropyRate v <= liminfInformationRate u :=
  limsupEntropyRate_le_liminfInformationRate_of_eventually_const_mono hu hv h

/-- Cross-sequence inequality with a one-sided eventual upper bound on `u`. -/
example {u v : Nat -> Real} {c : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n <= c)
    (hub : Filter.IsBoundedUnder (· >= ·) Filter.atTop u)
    (hcb : Filter.IsCoboundedUnder (· >= ·) Filter.atTop
            (fun _ : Nat => c))
    (hv : ∀ᶠ n in Filter.atTop, v n = c) :
    liminfInformationRate u <= limsupEntropyRate v :=
  liminfInformationRate_le_limsupEntropyRate_of_eventually_le_const_eq
    hu hub hcb hv

/-- Cross-sequence inequality with a one-sided eventual lower bound on `v`. -/
example {u v : Nat -> Real} {c : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n = c)
    (hv : ∀ᶠ n in Filter.atTop, c <= v n)
    (hcb : Filter.IsCoboundedUnder (· <= ·) Filter.atTop
            (fun _ : Nat => c))
    (hvb : Filter.IsBoundedUnder (· <= ·) Filter.atTop v) :
    liminfInformationRate u <= limsupEntropyRate v :=
  liminfInformationRate_le_limsupEntropyRate_of_eventually_eq_const_le
    hu hv hcb hvb

/-- Scalar lower bound from eventually-constant lim-inf. -/
example {u : Nat -> Real} {c1 c2 : Real}
    (h : c1 <= c2)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    c1 <= liminfInformationRate u :=
  const_le_liminfInformationRate_of_eventually_const h hu

/-- Scalar upper bound from eventually-constant lim-sup. -/
example {u : Nat -> Real} {c1 c2 : Real}
    (h : c2 <= c1)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    limsupEntropyRate u <= c1 :=
  limsupEntropyRate_le_const_of_eventually_const h hu

/-- Eventual upper bound transfers to lim-sup. -/
example {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, u n <= c)
    (hu : Filter.IsCoboundedUnder (· <= ·) Filter.atTop u)
    (hv : Filter.IsBoundedUnder (· <= ·) Filter.atTop
            (fun _ : Nat => c)) :
    limsupEntropyRate u <= c :=
  limsupEntropyRate_le_const_of_le_eventually h hu hv

/-- Scalar lower bound from eventually-constant lim-sup. -/
example {u : Nat -> Real} {c1 c2 : Real}
    (h : c1 <= c2)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    c1 <= limsupEntropyRate u :=
  const_le_limsupEntropyRate_of_eventually_const h hu

/-- Scalar upper bound from eventually-constant lim-inf. -/
example {u : Nat -> Real} {c1 c2 : Real}
    (h : c2 <= c1)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    liminfInformationRate u <= c1 :=
  liminfInformationRate_le_const_of_eventually_const h hu

/-- Strict scalar upper bound from eventually-constant lim-inf. -/
example {u : Nat -> Real} {c1 c2 : Real}
    (h : c2 < c1)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    liminfInformationRate u < c1 :=
  liminfInformationRate_lt_const_of_eventually_const h hu

/-- Strict scalar upper bound from eventually-constant lim-sup. -/
example {u : Nat -> Real} {c1 c2 : Real}
    (h : c2 < c1)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    limsupEntropyRate u < c1 :=
  limsupEntropyRate_lt_const_of_eventually_const h hu

/-- Strict scalar lower bound from eventually-constant lim-inf. -/
example {u : Nat -> Real} {c1 c2 : Real}
    (h : c1 < c2)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    c1 < liminfInformationRate u :=
  const_lt_liminfInformationRate_of_eventually_const h hu

/-- Strict scalar lower bound from eventually-constant lim-sup. -/
example {u : Nat -> Real} {c1 c2 : Real}
    (h : c1 < c2)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    c1 < limsupEntropyRate u :=
  const_lt_limsupEntropyRate_of_eventually_const h hu

/-- QPSK off-diagonal at `(3, 0)`. -/
example : qpsk.exceed 3 0 = 1 := qpsk_exceed_three_zero

/-- QPSK off-diagonal at `(3, 1)`. -/
example : qpsk.exceed 3 1 = 1 := qpsk_exceed_three_one

/-- QPSK off-diagonal at `(3, 2)`. -/
example : qpsk.exceed 3 2 = 1 := qpsk_exceed_three_two

/-- QPSK exceedance is `0` exactly on agreement. -/
example (s s_hat : Fin 4) :
    qpsk.exceed s s_hat = 0 ↔ s = s_hat :=
  qpsk_exceed_eq_zero_iff_eq s s_hat

/-- QPSK exceedance is strictly positive exactly on disagreement. -/
example (s s_hat : Fin 4) :
    0 < qpsk.exceed s s_hat ↔ s ≠ s_hat :=
  qpsk_exceed_pos_iff_ne s s_hat

/-- QPSK exceedance is strictly positive iff non-zero. -/
example (s s_hat : Fin 4) :
    0 < qpsk.exceed s s_hat ↔ qpsk.exceed s s_hat ≠ 0 :=
  qpsk_exceed_pos_iff_ne_zero s s_hat

/-- QPSK off-diagonal at `(2, 0)`. -/
example : qpsk.exceed 2 0 = 1 := qpsk_exceed_two_zero

/-- QPSK off-diagonal at `(2, 1)`. -/
example : qpsk.exceed 2 1 = 1 := qpsk_exceed_two_one

/-- QPSK off-diagonal at `(1, 3)`. -/
example : qpsk.exceed 1 3 = 1 := qpsk_exceed_one_three

/-- QPSK exceedance at `(3, 1)` is strictly positive. -/
example : 0 < qpsk.exceed 3 1 := qpsk_exceed_three_one_pos

/-- QPSK exceedance at `(3, 2)` is strictly positive. -/
example : 0 < qpsk.exceed 3 2 := qpsk_exceed_three_two_pos

/-- QPSK exceedance at `(2, 0)` is strictly positive. -/
example : 0 < qpsk.exceed 2 0 := qpsk_exceed_two_zero_pos

/-- QPSK exceedance at `(2, 1)` is strictly positive. -/
example : 0 < qpsk.exceed 2 1 := qpsk_exceed_two_one_pos

/-- QPSK exceedance at `(0, 2)` is strictly positive. -/
example : 0 < qpsk.exceed 0 2 := qpsk_exceed_zero_two_pos

/-- QPSK exceedance at `(1, 2)` is strictly positive. -/
example : 0 < qpsk.exceed 1 2 := qpsk_exceed_one_two_pos

/-- QPSK exceedance at `(1, 0)` is strictly positive. -/
example : 0 < qpsk.exceed 1 0 := qpsk_exceed_one_zero_pos

/-- Codeword XOR outer-right/inner-left involution. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor (Codeword.xor a b) a = b :=
  Codeword.xor_xor_self_left a b

/-- Pointwise outer-right/inner-left codeword XOR involution. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) a i = b i :=
  Codeword.xor_xor_self_left_apply a b i

/-- Pointwise four-argument XOR associativity. -/
example {n : Nat} (a b c d : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor (Codeword.xor a b) c) d i
      = Codeword.xor a (Codeword.xor b (Codeword.xor c d)) i :=
  Codeword.xor_assoc4_apply a b c d i

/-- Pointwise self-negation in `ZMod 2`. -/
example {n : Nat} (a : Codeword n) (i : Fin n) :
    (-a) i = a i :=
  Codeword.neg_eq_self_apply a i

/-- XOR with negation equals XOR (ZMod 2). -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor a (-b) = Codeword.xor a b :=
  Codeword.xor_neg_eq_xor a b

/-- Pointwise XOR-with-negation equals XOR. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a (-b) i = Codeword.xor a b i :=
  Codeword.xor_neg_eq_xor_apply a b i

/-- XOR with negation on the left equals XOR. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor (-a) b = Codeword.xor a b :=
  Codeword.neg_xor_eq_xor a b

/-- Pointwise XOR-with-negation on the left equals XOR. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (-a) b i = Codeword.xor a b i :=
  Codeword.neg_xor_eq_xor_apply a b i

/-- Double-negation XOR equals XOR. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor (-a) (-b) = Codeword.xor a b :=
  Codeword.neg_xor_neg_eq_xor a b

/-- Pointwise double-negation XOR equals XOR. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (-a) (-b) i = Codeword.xor a b i :=
  Codeword.neg_xor_neg_eq_xor_apply a b i

/-- XOR with own negation vanishes. -/
example {n : Nat} (a : Codeword n) :
    Codeword.xor a (-a) = 0 :=
  Codeword.xor_neg_self a

/-- Left-negation XOR with self vanishes. -/
example {n : Nat} (a : Codeword n) :
    Codeword.xor (-a) a = 0 :=
  Codeword.neg_xor_self a

/-- Pointwise XOR with own negation vanishes. -/
example {n : Nat} (a : Codeword n) (i : Fin n) :
    Codeword.xor a (-a) i = 0 :=
  Codeword.xor_neg_self_apply a i

/-- Pointwise left-negation XOR with self vanishes. -/
example {n : Nat} (a : Codeword n) (i : Fin n) :
    Codeword.xor (-a) a i = 0 :=
  Codeword.neg_xor_self_apply a i

/-- Negation swap across XOR. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor a (-b) = Codeword.xor (-a) b :=
  Codeword.xor_neg_eq_neg_xor a b

/-- Pointwise negation swap across XOR. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a (-b) i = Codeword.xor (-a) b i :=
  Codeword.xor_neg_eq_neg_xor_apply a b i

/-- Double-negation self-XOR vanishes. -/
example {n : Nat} (a : Codeword n) :
    Codeword.xor (-a) (-a) = 0 :=
  Codeword.neg_xor_neg_self a

/-- `landslideBucket` conjunction collapses to index equation. -/
example {n : Nat} (pi : ReliabilityRank n) (w1 w2 : Nat)
    (e : Fin n -> Bool) :
    landslideBucket pi w1 e /\ landslideBucket pi w2 e
      <-> w1 = w2 /\ landslideBucket pi w1 e :=
  landslideBucket_and_iff pi w1 w2 e

/-- `landslideBucket` conjunction, right-anchored form. -/
example {n : Nat} (pi : ReliabilityRank n) (w1 w2 : Nat)
    (e : Fin n -> Bool) :
    landslideBucket pi w1 e /\ landslideBucket pi w2 e
      <-> w1 = w2 /\ landslideBucket pi w2 e :=
  landslideBucket_and_iff_right pi w1 w2 e

/-- `landslideBucket` mutual exclusion at distinct indices. -/
example {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat}
    {e : Fin n -> Bool} (h_ne : w1 ≠ w2) :
    ¬ (landslideBucket pi w1 e /\ landslideBucket pi w2 e) :=
  landslideBucket_disjoint_of_ne pi h_ne

/-- `landslideBucket` mutual exclusion at strictly-less indices. -/
example {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat}
    {e : Fin n -> Bool} (h_lt : w1 < w2) :
    ¬ (landslideBucket pi w1 e /\ landslideBucket pi w2 e) :=
  landslideBucket_disjoint_of_lt pi h_lt

/-- `landslideBucket` mutual exclusion at strictly-greater indices. -/
example {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat}
    {e : Fin n -> Bool} (h_gt : w1 > w2) :
    ¬ (landslideBucket pi w1 e /\ landslideBucket pi w2 e) :=
  landslideBucket_disjoint_of_gt pi h_gt

/-- `landslideBucket` non-membership from a witness and distinct index. -/
example {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat}
    {e : Fin n -> Bool} (h1 : landslideBucket pi w1 e) (h_ne : w1 ≠ w2) :
    ¬ landslideBucket pi w2 e :=
  landslideBucket_not_of_mem_of_ne pi h1 h_ne

/-- `landslideBucket` non-membership from a witness and strictly-smaller index. -/
example {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat}
    {e : Fin n -> Bool} (h1 : landslideBucket pi w1 e) (h_lt : w1 < w2) :
    ¬ landslideBucket pi w2 e :=
  landslideBucket_not_of_mem_of_lt pi h1 h_lt

/-- `landslideBucket` non-membership from a witness and strictly-larger index. -/
example {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat}
    {e : Fin n -> Bool} (h1 : landslideBucket pi w1 e) (h_gt : w1 > w2) :
    ¬ landslideBucket pi w2 e :=
  landslideBucket_not_of_mem_of_gt pi h1 h_gt

/-- `landslideBucket` non-membership at the immediate successor index. -/
example {n : Nat} (pi : ReliabilityRank n) {w : Nat}
    {e : Fin n -> Bool} (h1 : landslideBucket pi w e) :
    ¬ landslideBucket pi (w + 1) e :=
  landslideBucket_not_of_mem_succ_self pi h1

/-- `landslideBucket` non-membership at the immediate predecessor index. -/
example {n : Nat} (pi : ReliabilityRank n) {w : Nat}
    {e : Fin n -> Bool} (h1 : landslideBucket pi (w + 1) e) :
    ¬ landslideBucket pi w e :=
  landslideBucket_not_of_mem_pred_self pi h1

/-- `landslideBucket` conjunction-form disjointness at the immediate successor. -/
example {n : Nat} (pi : ReliabilityRank n) {w : Nat} {e : Fin n -> Bool} :
    ¬ (landslideBucket pi w e /\ landslideBucket pi (w + 1) e) :=
  landslideBucket_disjoint_succ_self pi

/-- `landslideBucket` conjunction-form disjointness at the immediate predecessor. -/
example {n : Nat} (pi : ReliabilityRank n) {w : Nat} {e : Fin n -> Bool} :
    ¬ (landslideBucket pi (w + 1) e /\ landslideBucket pi w e) :=
  landslideBucket_disjoint_pred_self pi

/-- `landslideBucket` non-membership two indices past the witness. -/
example {n : Nat} (pi : ReliabilityRank n) {w : Nat}
    {e : Fin n -> Bool} (h1 : landslideBucket pi w e) :
    ¬ landslideBucket pi (w + 2) e :=
  landslideBucket_not_of_mem_succ_succ_self pi h1

/-- `landslideBucket` non-membership two indices before the witness. -/
example {n : Nat} (pi : ReliabilityRank n) {w : Nat}
    {e : Fin n -> Bool} (h1 : landslideBucket pi (w + 2) e) :
    ¬ landslideBucket pi w e :=
  landslideBucket_not_of_mem_pred_pred_self pi h1

/-- `landslideBucket` two-step conjunction-form disjointness. -/
example {n : Nat} (pi : ReliabilityRank n) {w : Nat} {e : Fin n -> Bool} :
    ¬ (landslideBucket pi w e /\ landslideBucket pi (w + 2) e) :=
  landslideBucket_disjoint_succ_succ_self pi

/-- `landslideBucket` two-step conjunction-form disjointness, swapped order. -/
example {n : Nat} (pi : ReliabilityRank n) {w : Nat} {e : Fin n -> Bool} :
    ¬ (landslideBucket pi (w + 2) e /\ landslideBucket pi w e) :=
  landslideBucket_disjoint_pred_pred_self pi

/-- `landslideBucket` non-membership three indices past the witness. -/
example {n : Nat} (pi : ReliabilityRank n) {w : Nat}
    {e : Fin n -> Bool} (h1 : landslideBucket pi w e) :
    ¬ landslideBucket pi (w + 3) e :=
  landslideBucket_not_of_mem_succ_succ_succ_self pi h1

/-- Vacuous codebook with empty pattern list at unit budget. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 1)
      ([] : List (Fin (n_s / b) -> Fin numCandidates)) = none :=
  orbgrandAi_empty_codebook_nil_mk_one Y

/-- Vacuous codebook with empty pattern list at budget 2. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 2)
      ([] : List (Fin (n_s / b) -> Fin numCandidates)) = none :=
  orbgrandAi_empty_codebook_nil_mk_two Y

/-- Vacuous codebook returns `none` at budget `3`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 3) patterns = none :=
  orbgrandAi_empty_codebook_mk_three Y patterns

/-- Vacuous codebook with empty pattern list at budget 3. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 3)
      ([] : List (Fin (n_s / b) -> Fin numCandidates)) = none :=
  orbgrandAi_empty_codebook_nil_mk_three Y

/-- Vacuous codebook returns `none` at budget `4`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 4) patterns = none :=
  orbgrandAi_empty_codebook_mk_four Y patterns

/-- Vacuous codebook with empty pattern list at budget 4. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 4)
      ([] : List (Fin (n_s / b) -> Fin numCandidates)) = none :=
  orbgrandAi_empty_codebook_nil_mk_four Y

/-- Vacuous codebook returns `none` at budget `5`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 5) patterns = none :=
  orbgrandAi_empty_codebook_mk_five Y patterns

/-- Vacuous codebook with empty pattern list at budget 5. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 5)
      ([] : List (Fin (n_s / b) -> Fin numCandidates)) = none :=
  orbgrandAi_empty_codebook_nil_mk_five Y

/-- Vacuous codebook returns `none` at budget `6`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 6) patterns = none :=
  orbgrandAi_empty_codebook_mk_six Y patterns

/-- Vacuous codebook with empty pattern list at budget 6. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 6)
      ([] : List (Fin (n_s / b) -> Fin numCandidates)) = none :=
  orbgrandAi_empty_codebook_nil_mk_six Y

/-- Vacuous codebook returns `none` at budget `7`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 7) patterns = none :=
  orbgrandAi_empty_codebook_mk_seven Y patterns

/-- Vacuous codebook with empty pattern list at budget 7. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 7)
      ([] : List (Fin (n_s / b) -> Fin numCandidates)) = none :=
  orbgrandAi_empty_codebook_nil_mk_seven Y

/-- Vacuous codebook returns `none` at budget `8`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 8) patterns = none :=
  orbgrandAi_empty_codebook_mk_eight Y patterns

/-- Vacuous codebook with empty pattern list at budget 8. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 8)
      ([] : List (Fin (n_s / b) -> Fin numCandidates)) = none :=
  orbgrandAi_empty_codebook_nil_mk_eight Y

/-- Vacuous codebook returns `none` at budget `9`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 9) patterns = none :=
  orbgrandAi_empty_codebook_mk_nine Y patterns

/-- Vacuous codebook with empty pattern list at budget 9. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 9)
      ([] : List (Fin (n_s / b) -> Fin numCandidates)) = none :=
  orbgrandAi_empty_codebook_nil_mk_nine Y

/-- Vacuous codebook returns `none` at budget `10`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 10) patterns = none :=
  orbgrandAi_empty_codebook_mk_ten Y patterns

/-- AR(2) recurrence step at index 49. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 49
      = phi1 * ar2 phi1 phi2 z1 z2 48
        + phi2 * ar2 phi1 phi2 z1 z2 47 :=
  ar2_forty_nine phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 50. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 50
      = phi1 * ar2 phi1 phi2 z1 z2 49
        + phi2 * ar2 phi1 phi2 z1 z2 48 :=
  ar2_fifty phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 51. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 51
      = phi1 * ar2 phi1 phi2 z1 z2 50
        + phi2 * ar2 phi1 phi2 z1 z2 49 :=
  ar2_fifty_one phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 52. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 52
      = phi1 * ar2 phi1 phi2 z1 z2 51
        + phi2 * ar2 phi1 phi2 z1 z2 50 :=
  ar2_fifty_two phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 53. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 53
      = phi1 * ar2 phi1 phi2 z1 z2 52
        + phi2 * ar2 phi1 phi2 z1 z2 51 :=
  ar2_fifty_three phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 54. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 54
      = phi1 * ar2 phi1 phi2 z1 z2 53
        + phi2 * ar2 phi1 phi2 z1 z2 52 :=
  ar2_fifty_four phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 55. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 55
      = phi1 * ar2 phi1 phi2 z1 z2 54
        + phi2 * ar2 phi1 phi2 z1 z2 53 :=
  ar2_fifty_five phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 56. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 56
      = phi1 * ar2 phi1 phi2 z1 z2 55
        + phi2 * ar2 phi1 phi2 z1 z2 54 :=
  ar2_fifty_six phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 57. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 57
      = phi1 * ar2 phi1 phi2 z1 z2 56
        + phi2 * ar2 phi1 phi2 z1 z2 55 :=
  ar2_fifty_seven phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 58. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 58
      = phi1 * ar2 phi1 phi2 z1 z2 57
        + phi2 * ar2 phi1 phi2 z1 z2 56 :=
  ar2_fifty_eight phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 59. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 59
      = phi1 * ar2 phi1 phi2 z1 z2 58
        + phi2 * ar2 phi1 phi2 z1 z2 57 :=
  ar2_fifty_nine phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 60. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 60
      = phi1 * ar2 phi1 phi2 z1 z2 59
        + phi2 * ar2 phi1 phi2 z1 z2 58 :=
  ar2_sixty phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 61. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 61
      = phi1 * ar2 phi1 phi2 z1 z2 60
        + phi2 * ar2 phi1 phi2 z1 z2 59 :=
  ar2_sixty_one phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 62. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 62
      = phi1 * ar2 phi1 phi2 z1 z2 61
        + phi2 * ar2 phi1 phi2 z1 z2 60 :=
  ar2_sixty_two phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 63. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 63
      = phi1 * ar2 phi1 phi2 z1 z2 62
        + phi2 * ar2 phi1 phi2 z1 z2 61 :=
  ar2_sixty_three phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 64. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 64
      = phi1 * ar2 phi1 phi2 z1 z2 63
        + phi2 * ar2 phi1 phi2 z1 z2 62 :=
  ar2_sixty_four phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 65. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 65
      = phi1 * ar2 phi1 phi2 z1 z2 64
        + phi2 * ar2 phi1 phi2 z1 z2 63 :=
  ar2_sixty_five phi1 phi2 z1 z2

/-- `kendallTau` triangle inequality, right-symmetrized form. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns) :
    kendallTau a c ≤ kendallTau a b + kendallTau c b :=
  kendallTau_triangle_right_symm a b c

/-- `kendallTau` triangle inequality, left-symmetrized form. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns) :
    kendallTau a c ≤ kendallTau b a + kendallTau b c :=
  kendallTau_triangle_left_symm a b c

/-- `kendallTau` triangle inequality, both-symmetrized form. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns) :
    kendallTau a c ≤ kendallTau b a + kendallTau c b :=
  kendallTau_triangle_both_symm a b c

/-- `kendallTau` zero-distance is symmetric. -/
example {numPatterns : Nat} (a b : QueryOrder numPatterns)
    (h : kendallTau a b = 0) :
    kendallTau b a = 0 :=
  kendallTau_eq_zero_symm a b h

/-- `kendallTau` zero-distance iff (symmetric form). -/
example {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    kendallTau a b = 0 ↔ kendallTau b a = 0 :=
  kendallTau_eq_zero_iff_symm a b

/-- `kendallTau` non-zero-distance iff (symmetric form). -/
example {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    kendallTau a b ≠ 0 ↔ kendallTau b a ≠ 0 :=
  kendallTau_ne_zero_iff_symm a b

/-- `kendallTau` zero left-distance squeeze. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns)
    (hab : kendallTau a b = 0) :
    kendallTau a c <= kendallTau b c :=
  kendallTau_le_of_eq_zero_left a b c hab

/-- `kendallTau` zero right-distance squeeze. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns)
    (hbc : kendallTau b c = 0) :
    kendallTau a c <= kendallTau a b :=
  kendallTau_le_of_eq_zero_right a b c hbc

/-- `kendallTau` zero left-distance forces equality of right-distances. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns)
    (hab : kendallTau a b = 0) :
    kendallTau a c = kendallTau b c :=
  kendallTau_eq_of_eq_zero_left a b c hab

/-- `kendallTau` zero right-distance forces equality of left-distances. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns)
    (hbc : kendallTau b c = 0) :
    kendallTau a c = kendallTau a b :=
  kendallTau_eq_of_eq_zero_right a b c hbc

/-- `kendallTau` zero left-distance forces equality of left-anchored distances. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns)
    (hab : kendallTau a b = 0) :
    kendallTau c a = kendallTau c b :=
  kendallTau_eq_of_eq_zero_symm a b c hab

/-- `kendallTau` zero right-distance forces equality of right-anchored distances. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns)
    (hbc : kendallTau b c = 0) :
    kendallTau c a = kendallTau b a :=
  kendallTau_eq_of_eq_zero_symm_right a b c hbc

/-- `kendallTau` strict upper bound propagates across a zero left-distance. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns) {n : Nat}
    (hab : kendallTau a b = 0) (hac : kendallTau a c < n) :
    kendallTau b c < n :=
  kendallTau_lt_of_lt_of_eq_zero_left a b c hab hac

/-- `kendallTau` strict upper bound propagates across a zero right-distance. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns) {n : Nat}
    (hbc : kendallTau b c = 0) (hab : kendallTau a b < n) :
    kendallTau a c < n :=
  kendallTau_lt_of_lt_of_eq_zero_right a b c hbc hab

/-- `kendallTau` iff form of strict-inequality propagation via zero left-distance. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns) {n : Nat}
    (hab : kendallTau a b = 0) :
    kendallTau a c < n ↔ kendallTau b c < n :=
  kendallTau_lt_iff_lt_of_eq_zero_left a b c hab

/-- `kendallTau` iff form of strict-inequality propagation via zero right-distance. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns) {n : Nat}
    (hbc : kendallTau b c = 0) :
    kendallTau a b < n ↔ kendallTau a c < n :=
  kendallTau_lt_iff_lt_of_eq_zero_right a b c hbc

/-- `kendallTau` iff form of weak-inequality propagation via zero left-distance. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns) {n : Nat}
    (hab : kendallTau a b = 0) :
    kendallTau a c <= n ↔ kendallTau b c <= n :=
  kendallTau_le_iff_le_of_eq_zero_left a b c hab

/-- Zero channel survives double perturbation. -/
example {n_s : Nat} (ε₁ ε₂ : Matrix (Fin n_s) (Fin n_s) Complex) :
    perturbChannel (perturbChannel 0 ε₁) ε₂ = 0 :=
  perturbChannel_perturbChannel_zero_channel ε₁ ε₂

/-- Pointwise double-perturbation of the zero channel. -/
example {n_s : Nat} (ε₁ ε₂ : Matrix (Fin n_s) (Fin n_s) Complex)
    (i j : Fin n_s) :
    perturbChannel (perturbChannel 0 ε₁) ε₂ i j
      = (0 : ChannelMatrix n_s) i j :=
  perturbChannel_perturbChannel_zero_channel_apply ε₁ ε₂ i j

/-- Diagonal entry under double zero-channel perturbation. -/
example {n_s : Nat} (ε₁ ε₂ : Matrix (Fin n_s) (Fin n_s) Complex)
    (i : Fin n_s) :
    perturbChannel (perturbChannel 0 ε₁) ε₂ i i
      = (0 : ChannelMatrix n_s) i i :=
  perturbChannel_perturbChannel_zero_channel_apply_diag ε₁ ε₂ i

/-- Diagonal reverse-direction zero perturbation. -/
example {n_s : Nat} (h : ChannelMatrix n_s) (i : Fin n_s) :
    h i i = perturbChannel h 0 i i :=
  perturbChannel_zero_eq_self_apply_diag h i

/-- Diagonal zero characterisation. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i : Fin n_s) :
    perturbChannel h epsilon i i = 0
      <-> h i i = 0 ∨ 1 + epsilon i i = 0 :=
  perturbChannel_eq_zero_iff_diag h epsilon i

/-- Diagonal pointwise identity at zero perturbation. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i : Fin n_s} (h_eps : epsilon i i = 0) :
    perturbChannel h epsilon i i = h i i :=
  perturbChannel_eps_zero_apply_diag h epsilon h_eps

/-- Diagonal factor-zero zeroes the entry. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i : Fin n_s} (h_factor : (1 : Complex) + epsilon i i = 0) :
    perturbChannel h epsilon i i = 0 :=
  perturbChannel_factor_zero_apply_diag h epsilon h_factor

/-- Diagonal pure cancellation: `epsilon i i = -1` zeroes the diagonal entry. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i : Fin n_s} (h_eps : epsilon i i = -1) :
    perturbChannel h epsilon i i = 0 :=
  perturbChannel_neg_one_attenuation_eq_zero_apply_diag h epsilon h_eps

/-- Diagonal pointwise zero preservation under perturbation. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i : Fin n_s} (hzero : h i i = 0) :
    perturbChannel h epsilon i i = 0 :=
  perturbChannel_zero_entry_diag h epsilon hzero

/-- Diagonal reverse-direction zero-zero composition. -/
example {n_s : Nat} (h : ChannelMatrix n_s) (i : Fin n_s) :
    h i i = perturbChannel (perturbChannel h 0) 0 i i :=
  perturbChannel_perturbChannel_zero_zero_eq_self_apply_diag h i

/-- Diagonal reverse-direction zero-channel under perturbation. -/
example {n_s : Nat} (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    (i : Fin n_s) :
    (0 : ChannelMatrix n_s) i i = perturbChannel 0 epsilon i i :=
  perturbChannel_zero_channel_eq_self_apply_diag epsilon i

/-- Pointwise reverse-direction zero-zero composition. -/
example {n_s : Nat} (h : ChannelMatrix n_s) (i j : Fin n_s) :
    h i j = perturbChannel (perturbChannel h 0) 0 i j :=
  perturbChannel_perturbChannel_zero_zero_eq_self_apply h i j

/-- Matrix-level reverse-direction zero-zero composition. -/
example {n_s : Nat} (h : ChannelMatrix n_s) :
    h = perturbChannel (perturbChannel h 0) 0 :=
  perturbChannel_perturbChannel_zero_zero_eq_self h

/-- Pointwise zero-channel under zero perturbation. -/
example {n_s : Nat} (i j : Fin n_s) :
    perturbChannel (0 : ChannelMatrix n_s) 0 i j
      = (0 : ChannelMatrix n_s) i j :=
  perturbChannel_zero_channel_zero_apply i j

/-- Diagonal specialisation: both channel and perturbation zero. -/
example {n_s : Nat} (i : Fin n_s) :
    perturbChannel (0 : ChannelMatrix n_s) 0 i i
      = (0 : ChannelMatrix n_s) i i :=
  perturbChannel_zero_channel_zero_apply_diag i

/-- Matrix-level zero-channel under zero perturbation. -/
example {n_s : Nat} :
    perturbChannel (0 : ChannelMatrix n_s) 0 = 0 :=
  perturbChannel_zero_channel_zero

/-- Matrix-level reverse form: zero matrix equals doubly-zero-perturbed channel. -/
example {n_s : Nat} :
    (0 : ChannelMatrix n_s) = perturbChannel (0 : ChannelMatrix n_s) 0 :=
  perturbChannel_zero_channel_zero_eq_self

/-- AR(2) recurrence step at index 42. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 42
      = phi1 * ar2 phi1 phi2 z1 z2 41
        + phi2 * ar2 phi1 phi2 z1 z2 40 :=
  ar2_forty_two phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 43. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 43
      = phi1 * ar2 phi1 phi2 z1 z2 42
        + phi2 * ar2 phi1 phi2 z1 z2 41 :=
  ar2_forty_three phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 44. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 44
      = phi1 * ar2 phi1 phi2 z1 z2 43
        + phi2 * ar2 phi1 phi2 z1 z2 42 :=
  ar2_forty_four phi1 phi2 z1 z2

/-- BPSK off-diagonal at `(true, false)`. -/
example : bpsk.exceed true false = 1 :=
  bpsk_exceed_true_false

/-- BPSK off-diagonal at `(false, true)`. -/
example : bpsk.exceed false true = 1 :=
  bpsk_exceed_false_true

/-- Diagonal zero perturbation. -/
example {n_s : Nat} (h : ChannelMatrix n_s) (i : Fin n_s) :
    perturbChannel h 0 i i = h i i :=
  perturbChannel_zero_apply_diag h i

/-- Diagonal zero channel under perturbation. -/
example {n_s : Nat} (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    (i : Fin n_s) :
    perturbChannel 0 epsilon i i = (0 : ChannelMatrix n_s) i i :=
  perturbChannel_zero_channel_apply_diag epsilon i

/-- Diagonal left-identity of composed perturbation. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i : Fin n_s) :
    perturbChannel (perturbChannel h 0) epsilon i i
      = perturbChannel h epsilon i i :=
  perturbChannel_perturbChannel_zero_left_apply_diag h epsilon i

/-- Forward direction of `substitutionPenalty?` definedness bridge. -/
example {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates)
    (h : (hardDecisionBlock? post).isSome = true) :
    (substitutionPenalty? post t).isSome = true :=
  substitutionPenalty?_isSome_of_hardDecisionBlock?_isSome post t h

/-- Forward direction of `substitutionPenalty?` undefinedness bridge. -/
example {numCandidates : Nat} (post : BlockPosterior numCandidates)
    (t : Fin numCandidates)
    (h : (hardDecisionBlock? post).isNone = true) :
    (substitutionPenalty? post t).isNone = true :=
  substitutionPenalty?_isNone_of_hardDecisionBlock?_isNone post t h

/-- `orbgrandAi` empty codebook at unit budget. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 1) patterns = none :=
  orbgrandAi_empty_codebook_mk_one Y patterns

/-- Vacuous codebook returns `none` at budget `2`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 2) patterns = none :=
  orbgrandAi_empty_codebook_mk_two Y patterns

/-- Vacuous codebook with empty pattern list at zero budget. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y (fun _ => false) (AbandonmentBudget.mk 0)
      ([] : List (Fin (n_s / b) -> Fin numCandidates)) = none :=
  orbgrandAi_empty_codebook_nil_zero_budget Y

/-- QPSK diagonal at index 0. -/
example : qpsk.exceed 0 0 = 0 := qpsk_exceed_zero_zero

/-- QPSK diagonal at index 1. -/
example : qpsk.exceed 1 1 = 0 := qpsk_exceed_one_one

/-- QPSK diagonal at index 2. -/
example : qpsk.exceed 2 2 = 0 := qpsk_exceed_two_two

/-- `kendallTau` self-additive bound. -/
example {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    kendallTau a b <= kendallTau a b + kendallTau b b :=
  kendallTau_le_self_add a b

/-- `kendallTau` empty domain bounded by 1. -/
example (a b : QueryOrder 0) : kendallTau a b <= 1 :=
  kendallTau_empty_le_one a b

/-- `landslideBucket` weight congruence. -/
example {n : Nat} (pi : ReliabilityRank n) {w1 w2 : Nat} (e : Fin n -> Bool)
    (h : w1 = w2) :
    landslideBucket pi w1 e <-> landslideBucket pi w2 e :=
  landslideBucket_weight_congr pi e h

/-- `landslideBucket` transports across equal-weight patterns. -/
example {n : Nat} (pi : ReliabilityRank n) {w : Nat} {e1 e2 : Fin n -> Bool}
    (h1 : landslideBucket pi w e1)
    (h_eq : logisticWeight pi e1 = logisticWeight pi e2) :
    landslideBucket pi w e2 :=
  landslideBucket_transport pi h1 h_eq

/-- Constant-false sits in bucket zero via perm characterisation. -/
example {n : Nat} (pi : ReliabilityRank n) :
    landslideBucket pi 0 (fun _ : Fin n => false) :=
  landslideBucket_zero_const_false_alt pi

/-- `Codeword.xor` identity iff left argument is zero. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = b <-> a = 0 :=
  Codeword.xor_self_eq_iff_right a b

/-- `Codeword.xor` four-argument associativity. -/
example {n : Nat} (a b c d : Codeword n) :
    Codeword.xor (Codeword.xor (Codeword.xor a b) c) d
      = Codeword.xor a (Codeword.xor b (Codeword.xor c d)) :=
  Codeword.xor_assoc4 a b c d

/-- Paired self-XOR vanishes. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor (Codeword.xor a a) (Codeword.xor b b) = 0 :=
  Codeword.xor_self_xor_self a b

/-- `entropyRate1_block` closed-form symmetric. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    Real.log (2 * Real.exp 1 * Real.pi * sigma.val)
      + (1 - (1 : Real) / (b.toNat : Real))
          * Real.log (1 - rho.val ^ 2)
      = entropyRate1_block sigma rho b :=
  entropyRate1_block_at_block_eq_log_form_symm sigma rho b

/-- `entropyRate2` at block size, closed form. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (b : BlockSize) :
    entropyRate2 sigma rho1 rho2 b.toNat
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * (b.toNat : Real)))
            * Real.log
                (- (rho2.val - 1) ^ (b.toNat - 2)
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (b.toNat - 2)
                  / (rho1.val ^ 2 - 1) ^ (b.toNat - 3)) :=
  entropyRate2_at_block_eq_log_form sigma rho1 rho2 b

/-- `entropyRate2` at block size, symmetric closed form. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (b : BlockSize) :
    (1 / 2 : Real)
        * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
      + (1 / (2 * (b.toNat : Real)))
          * Real.log
              (- (rho2.val - 1) ^ (b.toNat - 2)
                  * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (b.toNat - 2)
                / (rho1.val ^ 2 - 1) ^ (b.toNat - 3))
      = entropyRate2 sigma rho1 rho2 b.toNat :=
  entropyRate2_at_block_eq_log_form_symm sigma rho1 rho2 b

/-- QPSK diagonal at index 3. -/
example : qpsk.exceed 3 3 = 0 := qpsk_exceed_three_three

/-- QPSK off-diagonal at `(1, 0)`. -/
example : qpsk.exceed 1 0 = 1 := qpsk_exceed_one_zero

/-- QPSK off-diagonal at `(0, 2)`. -/
example : qpsk.exceed 0 2 = 1 := qpsk_exceed_zero_two

/-- QPSK off-diagonal at `(1, 2)`. -/
example : qpsk.exceed 1 2 = 1 := qpsk_exceed_one_two

/-- QPSK off-diagonal at `(2, 3)`. -/
example : qpsk.exceed 2 3 = 1 := qpsk_exceed_two_three

/-- AR(2) recurrence step at index 45. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 45
      = phi1 * ar2 phi1 phi2 z1 z2 44
        + phi2 * ar2 phi1 phi2 z1 z2 43 :=
  ar2_forty_five phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 46. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 46
      = phi1 * ar2 phi1 phi2 z1 z2 45
        + phi2 * ar2 phi1 phi2 z1 z2 44 :=
  ar2_forty_six phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 47. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 47
      = phi1 * ar2 phi1 phi2 z1 z2 46
        + phi2 * ar2 phi1 phi2 z1 z2 45 :=
  ar2_forty_seven phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 48. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 48
      = phi1 * ar2 phi1 phi2 z1 z2 47
        + phi2 * ar2 phi1 phi2 z1 z2 46 :=
  ar2_forty_eight phi1 phi2 z1 z2

/-- AR(2) phi1=0 boundary at index 5. -/
example (phi2 z1 z2 : Complex) :
    ar2 0 phi2 z1 z2 5 = phi2 * (phi2 * z2) :=
  ar2_phi1_zero_five phi2 z1 z2

/-- AR(2) phi2=0 boundary at index 5. -/
example (phi1 z1 z2 : Complex) :
    ar2 phi1 0 z1 z2 5 = phi1 * (phi1 * (phi1 * (phi1 * z2))) :=
  ar2_phi2_zero_five phi1 z1 z2

/-- `kendallTau` zero-distance is transitive. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns)
    (hab : kendallTau a b = 0) (hbc : kendallTau b c = 0) :
    kendallTau a c = 0 :=
  kendallTau_eq_zero_trans a b c hab hbc

/-- `Codeword.xor` of two zero codewords is zero. -/
example {n : Nat} :
    Codeword.xor (0 : Codeword n) (0 : Codeword n) = 0 :=
  Codeword.zero_xor_zero

/-- Pointwise paired self-XOR vanishes. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a a) (Codeword.xor b b) i = 0 :=
  Codeword.xor_self_xor_self_apply a b i

/-- `Codeword.xor a b = 0 ↔ a = b` (reversed form). -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = 0 <-> a = b :=
  Codeword.xor_eq_zero_iff_eq a b

/-- `QueryOrder.positionOf` on the empty list is `0`. -/
example {numPatterns : Nat} (x : Fin numPatterns) :
    QueryOrder.positionOf x ([] : QueryOrder numPatterns) = 0 :=
  QueryOrder.positionOf_nil x

/-- `kendallTau` on `QueryOrder 1` is `0` for any pair. -/
example (a b : QueryOrder 1) : kendallTau a b = 0 :=
  kendallTau_singleton a b

/-- `LinearIsi.tap?` reduces to `some` in the in-range branch. -/
example {n_s : Nat} (ch : LinearIsi n_s) (k' j : Fin n_s)
    (h : j.val <= k'.val) :
    ch.tap? k' j
      = some (ch.channel k'
          ⟨k'.val - j.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k'.isLt⟩) :=
  LinearIsi.tap?_of_le ch k' j h

/-- `LinearIsi.tap?` returns `none` in the out-of-range branch. -/
example {n_s : Nat} (ch : LinearIsi n_s) (k' j : Fin n_s)
    (h : ¬ j.val <= k'.val) :
    ch.tap? k' j = none :=
  LinearIsi.tap?_of_not_le ch k' j h

/-- `LinearIsi.bandwidth` widens by one. -/
example {n_s : Nat} {ch : LinearIsi n_s} {b : Nat}
    (h : ch.bandwidth b) :
    ch.bandwidth (b + 1) :=
  LinearIsi.bandwidth_succ h

/-- `perturbChannel` right-identity of composition. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) :
    perturbChannel (perturbChannel h epsilon) 0 = perturbChannel h epsilon :=
  perturbChannel_perturbChannel_zero_right h epsilon

/-- `perturbChannel` left-identity of composition. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) :
    perturbChannel (perturbChannel h 0) epsilon = perturbChannel h epsilon :=
  perturbChannel_perturbChannel_zero_left h epsilon

/-- `Section00.bler` of XOR-true on right equals `1 - bler decode`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool)
    (h_meas :
      MeasurableSet
        {N : Section00.RealSymbolVector n_s | decode N = true}) :
    Section00.bler sigma (fun N => xor (decode N) true)
      = 1 - Section00.bler sigma decode :=
  Section00.bler_xor_true_right_eq_one_sub sigma decode h_meas

/-- Section VI.B AR(2) approximation-error statement: the per-pulse
    `normSq <= delta^2` implication shape (`delta in [0, 1)`) is well-formed
    and reducible to `True`, locking the quantifier order and bound form. -/
example (n_s : Nat) (rowTaps : Fin n_s -> RFViewTaps)
    (h : forall (z : Fin 6 -> Complex),
        exists (delta : Real),
          0 <= delta /\ delta < 1 /\
          forall (j' : Fin 6),
            let (phi1, phi2) := ar2LeastSquaresFit z
            Complex.normSq (z j' -
              ar2 phi1 phi2 (z (0 : Fin 6)) (z (1 : Fin 6)) j'.val)
              <= delta * delta) :
    True :=
  ar2_approximation_error_statement n_s rowTaps h

/-- AR(2) closed form at index 3. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 3
      = phi1 * (phi1 * z2 + phi2 * z1) + phi2 * z2 :=
  ar2_three phi1 phi2 z1 z2

/-- AR(2) closed form at index 4. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 4
      = phi1 * (phi1 * (phi1 * z2 + phi2 * z1) + phi2 * z2)
        + phi2 * (phi1 * z2 + phi2 * z1) :=
  ar2_four phi1 phi2 z1 z2

/-- AR(2) recurrence step at index 5. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 5
      = phi1 * ar2 phi1 phi2 z1 z2 4
        + phi2 * ar2 phi1 phi2 z1 z2 3 :=
  ar2_five phi1 phi2 z1 z2

/-- AR(2) at index 0: initial condition `z1`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 0 = z1 :=
  ar2_zero phi1 phi2 z1 z2

/-- AR(2) at index 1: initial condition `z2`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 1 = z2 :=
  ar2_one phi1 phi2 z1 z2

/-- AR(2) recurrence at index `n + 2`. -/
example (phi1 phi2 z1 z2 : Complex) (n : Nat) :
    ar2 phi1 phi2 z1 z2 (n + 2)
      = phi1 * ar2 phi1 phi2 z1 z2 (n + 1)
        + phi2 * ar2 phi1 phi2 z1 z2 n :=
  ar2_succ_succ phi1 phi2 z1 z2 n

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

/-- Imperfect-CSI perturbation preserves bandwidth at width `b`. -/
example {n_s : Nat} {h : ChannelMatrix n_s}
    {epsilon : Matrix (Fin n_s) (Fin n_s) Complex} {b : Nat}
    (hb : forall (i j : Fin n_s), j.val + b < i.val -> h i j = 0)
    (i j : Fin n_s) (hij : j.val + b < i.val) :
    perturbChannel h epsilon i j = 0 :=
  perturbChannel_bandwidth_of_bandwidth hb i j hij

/-- BPSK is a concrete `Constellation Bool`. -/
example : Constellation Bool := bpsk

/-- BPSK exceedance is 0 on agreement. -/
example (s : Bool) : bpsk.exceed s s = 0 :=
  bpsk_exceed_self s

/-- BPSK exceedance is 1 on disagreement. -/
example {s s_hat : Bool} (h : s ≠ s_hat) : bpsk.exceed s s_hat = 1 :=
  bpsk_exceed_diff h

/-- Generic exceedance vanishes on the diagonal. -/
example {chi : Type} (cs : Constellation chi) (s : chi) :
    cs.exceed s s = 0 :=
  cs.exceed_self s

/-- Generic diagonal exceedances are all equal (both sides are 0). -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s = cs.exceed s_hat s_hat :=
  cs.exceed_self_eq_exceed_self s s_hat

/-- Generic diagonal exceedance is non-negative. -/
example {chi : Type} (cs : Constellation chi) (s : chi) :
    0 <= cs.exceed s s :=
  cs.exceed_self_nonneg s

/-- Generic symbol inequality implies non-zero exceedance. -/
example {chi : Type} (cs : Constellation chi) {s s_hat : chi}
    (h : s ≠ s_hat) :
    cs.exceed s s_hat ≠ 0 :=
  cs.exceed_ne_of_ne h

/-- Zero exceedance implies symbol equality. -/
example {chi : Type} (cs : Constellation chi) {s s_hat : chi}
    (h : cs.exceed s s_hat = 0) :
    s = s_hat :=
  cs.eq_of_exceed_zero h

/-- Symbol equality implies zero exceedance. -/
example {chi : Type} (cs : Constellation chi) {s s_hat : chi}
    (h : s = s_hat) :
    cs.exceed s s_hat = 0 :=
  cs.exceed_zero_of_eq h

/-- Diagonal exceedance lower-bounds any exceedance from `s`. -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s <= cs.exceed s s_hat :=
  cs.exceed_self_le_exceed s s_hat

/-- Diagonal exceedance at `s_hat` lower-bounds any exceedance landing at `s_hat`. -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s_hat s_hat <= cs.exceed s s_hat :=
  cs.exceed_self_le_exceed_right s s_hat

/-- Exceedance is nonzero iff symbols differ. -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s_hat ≠ 0 <-> s ≠ s_hat :=
  cs.exceed_ne_zero_iff_ne s s_hat

/-- Exceedance is strictly positive iff symbols differ. -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    0 < cs.exceed s s_hat <-> s ≠ s_hat :=
  cs.exceed_pos_iff_ne s s_hat

/-- Symbol inequality implies strictly positive exceedance. -/
example {chi : Type} (cs : Constellation chi) {s s_hat : chi}
    (h : s ≠ s_hat) :
    0 < cs.exceed s s_hat :=
  cs.exceed_pos_of_ne h

/-- Two-argument congruence for `exceed` under separate symbol equalities. -/
example {chi : Type} (cs : Constellation chi) {s s' s_hat s_hat' : chi}
    (h_s : s = s') (h_hat : s_hat = s_hat') :
    cs.exceed s s_hat = cs.exceed s' s_hat' :=
  cs.exceed_eq_of_eq h_s h_hat

/-- Exceedance dichotomy: either zero (agreement) or strictly positive (disagreement). -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s_hat = 0 \/ 0 < cs.exceed s s_hat :=
  cs.exceed_zero_or_pos s s_hat

/-- Nonzero exceedance is strictly positive. -/
example {chi : Type} (cs : Constellation chi) {s s_hat : chi}
    (h : cs.exceed s s_hat ≠ 0) :
    0 < cs.exceed s s_hat :=
  cs.exceed_pos_of_ne_zero h

/-- Exceedance is strictly positive iff nonzero. -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    0 < cs.exceed s s_hat <-> cs.exceed s s_hat ≠ 0 :=
  cs.exceed_pos_iff_ne_zero s s_hat

/-- `orbgrandEnumeration n w` exactly enumerates length-`n` patterns of bit-weight `w`;
    the public-facing wrapper around `landslide_correct`. -/
example (n w : Nat) (e : Fin n -> Bool) :
    e ∈ orbgrandEnumeration n w <-> bitWeight e = w :=
  orbgrandEnumeration_correct n w e

/-- `landslide n w` exactly enumerates length-`n` patterns of bit-weight `w`. -/
example (n w : Nat) (e : Fin n -> Bool) :
    e ∈ landslide n w <-> bitWeight e = w :=
  landslide_correct n w e

/-- Length-0 base case: landslide membership iff bit-weight equality. -/
example (e : Fin 0 -> Bool) (w : Nat) :
    e ∈ landslide 0 w <-> bitWeight e = w :=
  landslide_zero_iff e w

/-- Inductive step: membership in a `landslideExtend`-mapped list iff
    top bit matches and the restriction is in the list. -/
example {n : Nat} (list : List (Fin n -> Bool)) (b : Bool)
    (e : Fin (n + 1) -> Bool) :
    e ∈ list.map (landslideExtend b) <->
      e (Fin.last n) = b /\ (e ∘ Fin.castSucc) ∈ list :=
  mem_map_extend_iff list b e

/-- Every pattern is in its own bit-weight bucket. -/
example {n : Nat} (e : Fin n -> Bool) :
    e ∈ landslide n (bitWeight e) :=
  landslide_self_mem e

/-- `bitWeight` is bounded above by the rank-sum over `Fin n`. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight e ≤ Finset.univ.sum (fun i : Fin n => i.val + 1) :=
  bitWeight_le_sum e

/-- A pattern's bucket is uniquely determined. -/
example {n w1 w2 : Nat} {e : Fin n -> Bool}
    (h1 : e ∈ landslide n w1) (h2 : e ∈ landslide n w2) :
    w1 = w2 :=
  landslide_unique_bucket h1 h2

/-- The bit-weight is zero iff all bits are false. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight e = 0 <-> forall i, e i = false :=
  bitWeight_zero_iff_all_false e

/-- Empty pattern has bit-weight zero (vacuous sum over `Fin 0`). -/
example : bitWeight (Fin.elim0 : Fin 0 -> Bool) = 0 :=
  bitWeight_elim0

/-- The constant-false pattern has bit-weight zero. -/
example {n : Nat} : bitWeight (fun _ : Fin n => false) = 0 :=
  bitWeight_const_false

/-- Empty pattern has logistic weight zero under any reliability rank. -/
example {pi : ReliabilityRank 0} :
    logisticWeight pi Fin.elim0 = 0 :=
  logisticWeight_elim0

/-- `landslide 0 0` is exactly the singleton list containing the empty pattern. -/
example : landslide 0 0 = [Fin.elim0] :=
  landslide_zero_zero

/-- Concrete three-level evaluation: `landslide 3 2` is a singleton with the
    `withTop` branch firing at depth 1 (weight `2 - 2 = 0`) and the outer and
    innermost `withTop`s both suppressed. -/
example : landslide 3 2
    = [landslideExtend false
        (landslideExtend true (landslideExtend false Fin.elim0))] := rfl

/-- `landslide 3 3` is the two-element bucket where both `withTop` and
    `withoutTop` halves are non-empty: top bit alone (weight 3) plus bits 0+1
    set together (1 + 2 = 3).  Locks the `withTop ++ withoutTop` concat order
    with both halves non-empty (more-bits-set-at-top first). -/
example : landslide 3 3
    = [landslideExtend true
        (landslideExtend false (landslideExtend false Fin.elim0)),
       landslideExtend false
        (landslideExtend true (landslideExtend true Fin.elim0))] := rfl

/-- `landslide 0 (w + 1)` is empty: no length-0 patterns of positive weight. -/
example (w : Nat) : landslide 0 (w + 1) = [] :=
  landslide_zero_succ w

/-- Every pattern is in its own logistic-weight bucket. -/
example {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    landslideBucket pi (logisticWeight pi e) e :=
  landslideBucket_self pi e

/-- `landslideBucket pi w e` definitionally unfolds to `logisticWeight pi e = w`. -/
example {n : Nat} (pi : ReliabilityRank n) (w : Nat) (e : Fin n -> Bool) :
    landslideBucket pi w e = (logisticWeight pi e = w) := rfl

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

/-- Codeword XOR transposition (left-arg move): `a xor b = c ↔ b = a xor c`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor a b = c <-> b = Codeword.xor a c :=
  Codeword.xor_eq_iff_left_eq_xor a b c

/-- Codeword XOR transposition: `a xor b = c ↔ a = c xor b`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor a b = c <-> a = Codeword.xor c b :=
  Codeword.xor_eq_iff_eq_xor a b c

/-- `landslideExtend b` is injective in its restriction argument. -/
example {n : Nat} (b : Bool) {e1 e2 : Fin n -> Bool}
    (h : landslideExtend b e1 = landslideExtend b e2) : e1 = e2 :=
  landslideExtend_inj b h

/-- `landslideExtend` injectivity at the top bit (with fixed restriction). -/
example {n : Nat} (e : Fin n -> Bool) {b1 b2 : Bool}
    (h : landslideExtend b1 e = landslideExtend b2 e) : b1 = b2 :=
  landslideExtend_inj_top e h

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

/-- BPSK exceedance equals `1` exactly on disagreement. -/
example (s s_hat : Bool) : bpsk.exceed s s_hat = 1 ↔ s ≠ s_hat :=
  bpsk_exceed_eq_one_iff s s_hat

/-- QPSK exceedance equals `1` exactly on disagreement. -/
example (s s_hat : Fin 4) : qpsk.exceed s s_hat = 1 ↔ s ≠ s_hat :=
  qpsk_exceed_eq_one_iff s s_hat

/-- Generic exceedance: vanishes iff symbols agree (re-exposed iff). -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s_hat = 0 ↔ s = s_hat :=
  cs.exceed_eq_zero_iff_eq s s_hat

/-- Generic positive exceedance is non-zero. -/
example {chi : Type} (cs : Constellation chi) {s s_hat : chi}
    (h : 0 < cs.exceed s s_hat) :
    cs.exceed s s_hat ≠ 0 :=
  cs.exceed_ne_zero_of_pos h

/-- Trivial constellation exceedance is bounded by `1`. -/
example (s s_hat : Unit) : trivialConstellation.exceed s s_hat <= 1 :=
  trivialConstellation_le_one s s_hat

/-- Section IV symbol-level BLER equivalence statement (probabilistic form): every
    pair of `Bool`-valued failure-indicator decoders on `RealSymbolVector n_s`
    has matching `Section00.bler` at every noise power, locking the equivalence
    equation shape pending the concrete ORBGRAND-AI variant wire-up. -/
example {chi : Type} (cs : Constellation chi) (n_s : Nat)
    (h : forall (bitDecoder symbolDecoder : Section00.RealSymbolVector n_s -> Bool)
        (sigma : NoisePower),
      Section00.bler sigma bitDecoder
        = Section00.bler sigma symbolDecoder) :
    True :=
  symbol_level_bler_equivalence_statement cs n_s h

/-- `RealSymbolVector n_s` abbreviates `EuclideanSpace ℝ (Fin n_s)`, the
    real-valued symbol-vector type the noise model lives on. -/
example (n_s : Nat) :
    Section00.RealSymbolVector n_s = EuclideanSpace ℝ (Fin n_s) := rfl

/-- `noiseMeasure` definitional unfold: `multivariateGaussian 0 (sigma * I)`. -/
example (n_s : Nat) (sigma : NoisePower) :
    Section00.noiseMeasure n_s sigma
      = ProbabilityTheory.multivariateGaussian
          (0 : Section00.RealSymbolVector n_s)
          (Matrix.diagonal (fun _ : Fin n_s => sigma.val)) := rfl

/-- `bler` definitional unfold: the noise measure of the decoder-failure set,
    taken `toReal`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma decode
      = (Section00.noiseMeasure n_s sigma { N | decode N = true }).toReal := rfl

/-- `Section00.bler` is non-negative for every decoder and noise power. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    0 ≤ Section00.bler sigma decode :=
  Section00.bler_nonneg sigma decode

/-- `Section00.bler` is at most one for every decoder and noise power,
    completing the `0 ≤ bler ≤ 1` sandwich on the new probability layer. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma decode ≤ 1 :=
  Section00.bler_le_one sigma decode

/-- `Section00.bler` on the always-true (saturating) decoder evaluates to `1`. -/
example {n_s : Nat} (sigma : NoisePower) :
    Section00.bler sigma (fun _ : Section00.RealSymbolVector n_s => true) = 1 :=
  Section00.bler_const_true sigma

/-- `Section00.bler` on the always-false (non-failing) decoder evaluates to `0`. -/
example {n_s : Nat} (sigma : NoisePower) :
    Section00.bler sigma (fun _ : Section00.RealSymbolVector n_s => false) = 0 :=
  Section00.bler_const_false sigma

/-- `Section00.bler` is monotone in decoder set inclusion: if `decode1`'s
    failures are a subset of `decode2`'s, then `bler decode1 ≤ bler decode2`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool)
    (h : forall N, decode1 N = true -> decode2 N = true) :
    Section00.bler sigma decode1 ≤ Section00.bler sigma decode2 :=
  Section00.bler_monotone sigma decode1 decode2 h

/-- `Section00.bler` is invariant under pointwise-equal decoders. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool)
    (h : forall N, decode1 N = decode2 N) :
    Section00.bler sigma decode1 = Section00.bler sigma decode2 :=
  Section00.bler_pointwise_eq sigma decode1 decode2 h

/-- `Section00.bler` complement relation: under measurability of the failure
    set, `bler decode + bler !decode = 1`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool)
    (h_meas : MeasurableSet
      {N : Section00.RealSymbolVector n_s | decode N = true}) :
    Section00.bler sigma decode + Section00.bler sigma (fun N => !decode N) = 1 :=
  Section00.bler_compl_eq sigma decode h_meas

/-- `Section00.bler decode = 1 - bler !decode` corollary form. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool)
    (h_meas : MeasurableSet
      {N : Section00.RealSymbolVector n_s | decode N = true}) :
    Section00.bler sigma decode
      = 1 - Section00.bler sigma (fun N => !decode N) :=
  Section00.bler_eq_one_sub_compl sigma decode h_meas

/-- `Section00.bler` subadditivity under `||`: BLER of the disjunctive
    decoder is at most the sum of individual BLERs.  No measurability
    hypothesis needed. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode1 N || decode2 N)
      ≤ Section00.bler sigma decode1 + Section00.bler sigma decode2 :=
  Section00.bler_or_le sigma decode1 decode2

/-- `Section00.bler` monotonicity under `&&` (left): BLER of the conjunctive
    decoder is at most the BLER of the left component. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode1 N && decode2 N)
      ≤ Section00.bler sigma decode1 :=
  Section00.bler_and_le_left sigma decode1 decode2

/-- `Section00.bler` monotonicity under `&&` (right): dual of `bler_and_le_left`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode1 N && decode2 N)
      ≤ Section00.bler sigma decode2 :=
  Section00.bler_and_le_right sigma decode1 decode2

/-- `Section00.bler` double-negation invariance: `!!decode` has the same BLER as `decode`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => !!decode N) = Section00.bler sigma decode :=
  Section00.bler_double_neg sigma decode

/-- `Section00.bler` of XOR vanishes when the two decoders agree pointwise. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool)
    (h : forall N, decode1 N = decode2 N) :
    Section00.bler sigma (fun N => xor (decode1 N) (decode2 N)) = 0 :=
  Section00.bler_xor_eq_zero_of_pointwise_eq sigma decode1 decode2 h

/-- `Section00.bler` XOR sub-additivity: the symmetric-difference BLER
    is at most the sum of individual BLERs. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (decode1 N) (decode2 N))
      ≤ Section00.bler sigma decode1 + Section00.bler sigma decode2 :=
  Section00.bler_xor_le sigma decode1 decode2

/-- `Section00.bler` OR commutativity. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode1 N || decode2 N)
      = Section00.bler sigma (fun N => decode2 N || decode1 N) :=
  Section00.bler_or_comm sigma decode1 decode2

/-- `Section00.bler` AND commutativity. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode1 N && decode2 N)
      = Section00.bler sigma (fun N => decode2 N && decode1 N) :=
  Section00.bler_and_comm sigma decode1 decode2

/-- `Section00.bler` OR idempotence: `decode || decode` has the same BLER as `decode`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode N || decode N) = Section00.bler sigma decode :=
  Section00.bler_or_idem sigma decode

/-- `Section00.bler` AND idempotence: `decode && decode` has the same BLER as `decode`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode N && decode N) = Section00.bler sigma decode :=
  Section00.bler_and_idem sigma decode

/-- `Section00.bler` OR associativity. -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => (d1 N || d2 N) || d3 N)
      = Section00.bler sigma (fun N => d1 N || (d2 N || d3 N)) :=
  Section00.bler_or_assoc sigma d1 d2 d3

/-- `Section00.bler` AND associativity. -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => (d1 N && d2 N) && d3 N)
      = Section00.bler sigma (fun N => d1 N && (d2 N && d3 N)) :=
  Section00.bler_and_assoc sigma d1 d2 d3

/-- `Section00.bler` XOR commutativity. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode1 decode2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (decode1 N) (decode2 N))
      = Section00.bler sigma (fun N => xor (decode2 N) (decode1 N)) :=
  Section00.bler_xor_comm sigma decode1 decode2

/-- `Section00.bler` XOR associativity. -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (xor (d1 N) (d2 N)) (d3 N))
      = Section00.bler sigma (fun N => xor (d1 N) (xor (d2 N) (d3 N))) :=
  Section00.bler_xor_assoc sigma d1 d2 d3

/-- `Section00.bler` excluded-middle: `decode || !decode` is total failure (`bler = 1`). -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode N || !decode N) = 1 :=
  Section00.bler_or_not_self sigma decode

/-- `Section00.bler` non-contradiction: `decode && !decode` never fails (`bler = 0`). -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode N && !decode N) = 0 :=
  Section00.bler_and_not_self sigma decode

/-- `Section00.bler` OR-true annihilation: `decode || true = true` so `bler = 1`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode N || true) = 1 :=
  Section00.bler_or_true sigma decode

/-- `Section00.bler` AND-false annihilation: `decode && false = false` so `bler = 0`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode N && false) = 0 :=
  Section00.bler_and_false sigma decode

/-- `Section00.bler` OR-false identity (right). -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode N || false) = Section00.bler sigma decode :=
  Section00.bler_or_false sigma decode

/-- `Section00.bler` AND-true identity (right). -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => decode N && true) = Section00.bler sigma decode :=
  Section00.bler_and_true sigma decode

/-- `Section00.bler` OR-false identity (left). -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => false || decode N) = Section00.bler sigma decode :=
  Section00.bler_false_or sigma decode

/-- `Section00.bler` AND-true identity (left). -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => true && decode N) = Section00.bler sigma decode :=
  Section00.bler_true_and sigma decode

/-- `Section00.bler` OR-true annihilation (left): `true || decode = true` so `bler = 1`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => true || decode N) = 1 :=
  Section00.bler_true_or sigma decode

/-- `Section00.bler` AND-false annihilation (left): `false && decode = false` so `bler = 0`. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => false && decode N) = 0 :=
  Section00.bler_false_and sigma decode

/-- `Section00.bler` of `xor decode decode` vanishes. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (decode N) (decode N)) = 0 :=
  Section00.bler_xor_self sigma decode

/-- `Section00.bler` of `xor decode false` is identity (right). -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (decode N) false) = Section00.bler sigma decode :=
  Section00.bler_xor_false_right sigma decode

/-- `Section00.bler` of `xor false decode` is identity (left). -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor false (decode N)) = Section00.bler sigma decode :=
  Section00.bler_false_xor sigma decode

/-- `Section00.bler` DeMorgan: `!(d1 || d2)` has the same BLER as `!d1 && !d2`. -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => !(d1 N || d2 N))
      = Section00.bler sigma (fun N => !d1 N && !d2 N) :=
  Section00.bler_not_or sigma d1 d2

/-- `Section00.bler` DeMorgan over `&&`: dual of `bler_not_or`. -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => !(d1 N && d2 N))
      = Section00.bler sigma (fun N => !d1 N || !d2 N) :=
  Section00.bler_not_and sigma d1 d2

/-- `Section00.bler` XOR-true on the right is negation. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (decode N) true)
      = Section00.bler sigma (fun N => !decode N) :=
  Section00.bler_xor_true_right sigma decode

/-- `Section00.bler` XOR-true on the left is negation. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor true (decode N))
      = Section00.bler sigma (fun N => !decode N) :=
  Section00.bler_true_xor sigma decode

/-- `Section00.bler` XOR-of-NOT-with-self is total failure (`bler = 1`). -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (!decode N) (decode N)) = 1 :=
  Section00.bler_not_xor_self sigma decode

/-- `Section00.bler` XOR-with-NOT-of-self is total failure (`bler = 1`). -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (decode N) (!decode N)) = 1 :=
  Section00.bler_xor_not_self sigma decode

/-- `Section00.bler` NOT-XOR identity: `xor (!d1) d2 = !(xor d1 d2)`. -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (!d1 N) (d2 N))
      = Section00.bler sigma (fun N => !(xor (d1 N) (d2 N))) :=
  Section00.bler_not_xor sigma d1 d2

/-- `Section00.bler` XOR-NOT identity: `xor d1 (!d2) = !(xor d1 d2)`. -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (d1 N) (!d2 N))
      = Section00.bler sigma (fun N => !(xor (d1 N) (d2 N))) :=
  Section00.bler_xor_not sigma d1 d2

/-- `Section00.bler` double-NOT under XOR cancels: `xor (!d1) (!d2) = xor d1 d2`. -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => xor (!d1 N) (!d2 N))
      = Section00.bler sigma (fun N => xor (d1 N) (d2 N)) :=
  Section00.bler_not_xor_not sigma d1 d2

/-- `Section00.bler` `&&`-over-`||` distributivity (left). -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => d1 N && (d2 N || d3 N))
      = Section00.bler sigma (fun N => (d1 N && d2 N) || (d1 N && d3 N)) :=
  Section00.bler_and_or_distrib_left sigma d1 d2 d3

/-- `Section00.bler` `&&`-over-`||` distributivity (right). -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => (d1 N || d2 N) && d3 N)
      = Section00.bler sigma (fun N => (d1 N && d3 N) || (d2 N && d3 N)) :=
  Section00.bler_and_or_distrib_right sigma d1 d2 d3

/-- `Section00.bler` `||`-over-`&&` distributivity (left). -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => d1 N || (d2 N && d3 N))
      = Section00.bler sigma (fun N => (d1 N || d2 N) && (d1 N || d3 N)) :=
  Section00.bler_or_and_distrib_left sigma d1 d2 d3

/-- `Section00.bler` `||`-over-`&&` distributivity (right). -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 d3 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => (d1 N && d2 N) || d3 N)
      = Section00.bler sigma (fun N => (d1 N || d3 N) && (d2 N || d3 N)) :=
  Section00.bler_or_and_distrib_right sigma d1 d2 d3

/-- `Section00.bler` absorption: `a || (a && b)` collapses to `a`. -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => d1 N || (d1 N && d2 N))
      = Section00.bler sigma d1 :=
  Section00.bler_or_and_absorb sigma d1 d2

/-- `Section00.bler` absorption: `a && (a || b)` collapses to `a`. -/
example {n_s : Nat} (sigma : NoisePower)
    (d1 d2 : Section00.RealSymbolVector n_s -> Bool) :
    Section00.bler sigma (fun N => d1 N && (d1 N || d2 N))
      = Section00.bler sigma d1 :=
  Section00.bler_and_or_absorb sigma d1 d2

/-- `regressorMatrix4x2` body unfold: at `(i, j)` returns `z (i.val + j.val)`
    with the `Fin 6` bound witnessed by `i.val + j.val < 4 + 1 < 6`. -/
example (z : Fin 6 -> Complex) (i : Fin 4) (j : Fin 2) :
    regressorMatrix4x2 z i j
      = z ⟨i.val + j.val,
           Nat.lt_succ_of_lt
             (Nat.add_lt_add_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt))⟩ := rfl

/-- `regressorMatrix4x2` at concrete `(0, 0)` returns `z 0`. -/
example (z : Fin 6 -> Complex) :
    regressorMatrix4x2 z 0 0 = z 0 := rfl

/-- `regressorMatrix4x2` at concrete `(3, 1)` returns `z 4` (last entry). -/
example (z : Fin 6 -> Complex) :
    regressorMatrix4x2 z 3 1 = z 4 := rfl

/-- `regressorTarget4` body unfold: at `i` returns `z (i.val + 2)`. -/
example (z : Fin 6 -> Complex) (i : Fin 4) :
    regressorTarget4 z i
      = z ⟨i.val + 2, Nat.add_lt_add_right i.isLt 2⟩ := rfl

/-- `regressorTarget4` at `0` returns `z 2`. -/
example (z : Fin 6 -> Complex) :
    regressorTarget4 z 0 = z 2 := rfl

/-- `regressorTarget4` at `3` returns `z 5` (last entry). -/
example (z : Fin 6 -> Complex) :
    regressorTarget4 z 3 = z 5 := rfl

/-- Zero channel stays zero under any perturbation. -/
example {n_s : Nat} (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) :
    perturbChannel 0 epsilon = 0 :=
  perturbChannel_zero_channel epsilon

/-- `NMSE.mk?` on a non-negative real lands in `ok`. -/
example (v : Real) (h : 0 <= v) :
    NMSE.mk? v = Except.ok ⟨v, h⟩ := dif_pos h

/-- `NMSE.mk?` on a negative real lands in `error` with `negativeVariance v`. -/
example (v : Real) (h : ¬ 0 <= v) :
    NMSE.mk? v = Except.error (ChannelError.negativeVariance v) := dif_neg h

/-- `NMSE.val` projection through anonymous constructor returns the supplied real. -/
example (v : Real) (h : 0 <= v) :
    ({ val := v, nonneg := h } : NMSE).val = v := rfl

/-- `NMSE.nonneg` projection through anonymous constructor returns the supplied
    non-negativity proof; pairing with `val` pins the field order. -/
example (v : Real) (h : 0 <= v) :
    ({ val := v, nonneg := h } : NMSE).nonneg = h := rfl

/-- `CorrelationCoefficient.nonneg` projection through anonymous constructor
    returns the supplied non-negativity proof.  Three-field carrier
    (`val`, `nonneg`, `le_one`); pairs with `le_one` projection to pin order. -/
example (v : Real) (h0 : 0 <= v) (h1 : v <= 1) :
    ({ val := v, nonneg := h0, le_one := h1 } : CorrelationCoefficient).nonneg
      = h0 := rfl

/-- `CorrelationCoefficient.le_one` projection through anonymous constructor
    returns the supplied upper-bound proof; catches a silent swap of
    `nonneg` and `le_one`. -/
example (v : Real) (h0 : 0 <= v) (h1 : v <= 1) :
    ({ val := v, nonneg := h0, le_one := h1 } : CorrelationCoefficient).le_one
      = h1 := rfl

/-- `NoisePower.val` projection through anonymous constructor. -/
example (v : Real) (h : 0 <= v) :
    ({ val := v, nonneg := h } : NoisePower).val = v := rfl

/-- `NoisePower.nonneg` projection through anonymous constructor. -/
example (v : Real) (h : 0 <= v) :
    ({ val := v, nonneg := h } : NoisePower).nonneg = h := rfl

/-- `SignalPower.val` projection through anonymous constructor. -/
example (v : Real) (h : 0 <= v) :
    ({ val := v, nonneg := h } : SignalPower).val = v := rfl

/-- `SamplingFreq.val` projection through anonymous constructor. -/
example (v : Real) (h : 0 < v) :
    ({ val := v, pos := h } : SamplingFreq).val = v := rfl

/-- `BlockSize.toNat` projection through anonymous constructor. -/
example (n : Nat) (h : 0 < n) :
    ({ toNat := n, pos := h } : BlockSize).toNat = n := rfl

/-- `AbandonmentBudget.toNat` projection through anonymous constructor. -/
example (n : Nat) :
    ({ toNat := n } : AbandonmentBudget).toNat = n := rfl

/-- `Ar2Coefficient.val` projection through anonymous constructor. -/
example (v : Real) : ({ val := v } : Ar2Coefficient).val = v := rfl

/-- `ConstellationSize.toNat` projection through anonymous constructor. -/
example (n : Nat) (h : 0 < n) :
    ({ toNat := n, pos := h } : ConstellationSize).toNat = n := rfl

/-- `CodewordLength.toNat` projection through anonymous constructor. -/
example (n : Nat) (h : 0 < n) :
    ({ toNat := n, pos := h } : CodewordLength).toNat = n := rfl

/-- `BitsPerSymbol.toNat` projection through anonymous constructor. -/
example (n : Nat) (h : 0 < n) :
    ({ toNat := n, pos := h } : BitsPerSymbol).toNat = n := rfl

/-- Concrete BPSK eval: `exceed true false = 1` (closed Bool values reduce). -/
example : bpsk.exceed true false = 1 := rfl

/-- Concrete QPSK eval: `exceed 0 1 = 1` (closed `Fin 4` values reduce
    through `Fin.decEq`). -/
example : qpsk.exceed (0 : Fin 4) (1 : Fin 4) = 1 := rfl

/-- `landslide 2 1` is the singleton with bit 0 set, bit 1 unset. -/
example : landslide 2 1
    = [landslideExtend false (landslideExtend true Fin.elim0)] := rfl

/-- `landslide 4 1` is the four-deep singleton: bit 0 set, all higher bits unset. -/
example : landslide 4 1
    = [landslideExtend false
        (landslideExtend false
          (landslideExtend false (landslideExtend true Fin.elim0)))] := rfl

/-- `syndrome` definitional unfold: `H * (Y xor N_g)` as a function. -/
example {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n) :
    syndrome H Y N_g = H.matrix.mulVec (Codeword.xor Y N_g) := rfl

/-- `syndromeZero` definitional unfold: every row of `syndrome` vanishes. -/
example {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n) :
    syndromeZero H Y N_g
      = forall (i : Fin (n - k)), syndrome H Y N_g i = 0 := rfl

/-- `bitWeight` definitional unfold: `Finset.univ.sum` of position-weighted bits. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight e = Finset.univ.sum fun i : Fin n => if e i then i.val + 1 else 0 := rfl

/-- `logisticWeight` definitional unfold: sum of rank-weighted bits under `pi.perm`. -/
example {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    logisticWeight pi e
      = Finset.univ.sum fun i : Fin n =>
          if e (pi.perm i) then i.val + 1 else 0 := rfl

/-- `landslideExtend b e` is exactly `Fin.lastCases b e`. -/
example {n : Nat} (b : Bool) (e : Fin n -> Bool) :
    landslideExtend b e = Fin.lastCases b e := rfl

/-- `cov1_lag` definitional unfold: `sigma * rho^|i|`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (i : Int) :
    cov1_lag sigma rho i = sigma.val * (rho.val ^ i.natAbs) := rfl

/-- `orbgrandAi` is exactly `orbgrandAiLoop` at the budget `budget.toNat`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates) Y Phi budget patterns
      = orbgrandAiLoop Y Phi budget.toNat patterns := rfl

/-- `dicodeMatrix` definitional unfold: nested-if `1` / `-rho` / `0` body. -/
example {n_s : Nat} (rho : CorrelationCoefficient) (i j : Fin n_s) :
    dicodeMatrix n_s rho i j
      = (if i.val = j.val then (1 : Complex)
         else if i.val = j.val + 1 then -(rho.val : Complex)
         else (0 : Complex)) := rfl

/-- `perturbChannel` definitional unfold: pointwise `h * (1 + epsilon)`. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i j : Fin n_s) :
    perturbChannel h epsilon i j = h i j * (1 + epsilon i j) := rfl

/-- `dicode` definitional unfold: a `LinearIsi` with `dicodeMatrix` channel
    and `gaussMarkovCov` noise covariance. -/
example (n_s : Nat) (sigma : NoisePower) (rho : CorrelationCoefficient) :
    dicode n_s sigma rho
      = { channel := dicodeMatrix n_s rho,
          noiseCov := gaussMarkovCov n_s sigma rho } := rfl

/-- `LinearIsi.receive` definitional unfold: pointwise `ch.channel * X + N`. -/
example {n_s : Nat} (ch : LinearIsi n_s) (X N : SymbolVector n_s) (k : Fin n_s) :
    ch.receive X N k = ch.channel.mulVec X k + N k := rfl

/-- `BlockPosterior numCandidates` abbreviates `Fin numCandidates -> Real`. -/
example (numCandidates : Nat) :
    BlockPosterior numCandidates = (Fin numCandidates -> Real) := rfl

/-- `SymbolVector n_s` abbreviates `Fin n_s -> Complex`. -/
example (n_s : Nat) : SymbolVector n_s = (Fin n_s -> Complex) := rfl

/-- `ChannelMatrix n_s` abbreviates `Matrix (Fin n_s) (Fin n_s) Complex`. -/
example (n_s : Nat) :
    ChannelMatrix n_s = Matrix (Fin n_s) (Fin n_s) Complex := rfl

/-- `CovMatrix n_s` abbreviates `Matrix (Fin n_s) (Fin n_s) Complex`; same
    carrier as `ChannelMatrix` but used for noise auto-covariance. -/
example (n_s : Nat) :
    CovMatrix n_s = Matrix (Fin n_s) (Fin n_s) Complex := rfl

/-- `CodebookMembership n` abbreviates `Codeword n -> Bool`. -/
example (n : Nat) : CodebookMembership n = (Codeword n -> Bool) := rfl

/-- `Codeword n` abbreviates `Fin n -> ZMod 2`. -/
example (n : Nat) : Codeword n = (Fin n -> ZMod 2) := rfl

/-- `BitReliability n` abbreviates `Fin n -> Real`. -/
example (n : Nat) : BitReliability n = (Fin n -> Real) := rfl

/-- `QueryOrder numPatterns` abbreviates `List (Fin numPatterns)`. -/
example (numPatterns : Nat) :
    QueryOrder numPatterns = List (Fin numPatterns) := rfl

/-- `LinearIsi.channel` projection through anonymous constructor. -/
example {n_s : Nat} (h : ChannelMatrix n_s) (C : CovMatrix n_s) :
    ({ channel := h, noiseCov := C } : LinearIsi n_s).channel = h := rfl

/-- `LinearIsi.noiseCov` projection through anonymous constructor;
    pairing with `channel` pins the field order. -/
example {n_s : Nat} (h : ChannelMatrix n_s) (C : CovMatrix n_s) :
    ({ channel := h, noiseCov := C } : LinearIsi n_s).noiseCov = C := rfl

/-- `ParityCheck.matrix` projection through anonymous constructor. -/
example {n k : Nat} (M : Matrix (Fin (n - k)) (Fin n) (ZMod 2)) (h : k <= n) :
    ({ matrix := M, kLeN := h } : ParityCheck n k).matrix = M := rfl

/-- `ParityCheck.kLeN` projection through anonymous constructor;
    pairing with `matrix` pins the field order. -/
example {n k : Nat} (M : Matrix (Fin (n - k)) (Fin n) (ZMod 2)) (h : k <= n) :
    ({ matrix := M, kLeN := h } : ParityCheck n k).kLeN = h := rfl

/-- `RFViewTaps.tap1` projection through anonymous constructor. -/
example (t1 t2 t3 t4 t5 t6 : Complex) :
    ({ tap1 := t1, tap2 := t2, tap3 := t3,
       tap4 := t4, tap5 := t5, tap6 := t6 } : RFViewTaps).tap1 = t1 := rfl

/-- `RFViewTaps.tap6` projection through anonymous constructor;
    paired with `tap1` lock pins the six-field carrier order at the extremes. -/
example (t1 t2 t3 t4 t5 t6 : Complex) :
    ({ tap1 := t1, tap2 := t2, tap3 := t3,
       tap4 := t4, tap5 := t5, tap6 := t6 } : RFViewTaps).tap6 = t6 := rfl

/-- `RFViewTaps.tap?` at index 7 falls into the catch-all `none` branch. -/
example (t : RFViewTaps) : t.tap? 7 = none := rfl

/-- `RFViewTaps.tap?` at index 3 returns `some t.tap3` (pattern-match body). -/
example (t : RFViewTaps) : t.tap? 3 = some t.tap3 := rfl

/-- `ChannelError.nonPositive` constructor reduces with a concrete tag. -/
example : (ChannelError.nonPositive "BlockSize" : ChannelError)
    = ChannelError.nonPositive "BlockSize" := rfl

/-- `ChannelError.negativeVariance` carries the offending real verbatim. -/
example (v : Real) : (ChannelError.negativeVariance v : ChannelError)
    = ChannelError.negativeVariance v := rfl

/-- `ReliabilityRank.perm` projection through anonymous constructor. -/
example {n : Nat} (p : Fin n -> Fin n)
    (hb : Function.Bijective p)
    (hm : forall (rel : BitReliability n) (i j : Fin n),
      i.val <= j.val -> rel (p i) <= rel (p j)) :
    ({ perm := p, bijective := hb, monotone := hm } : ReliabilityRank n).perm
      = p := rfl

/-- `bpsk.exceed` is the `if s = s_hat then 0 else 1` body verbatim
    (structure-projection rfl-lock on the `exceed` field). -/
example :
    bpsk.exceed = fun s s_hat => if s = s_hat then (0 : Real) else 1 := rfl

/-- `cov2DetFormula` definitional unfold: zeta-reduces the `let r1`, `let r2`,
    `let sigmaSq` bindings to expose the closed-form expression. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (n_s : Nat) :
    cov2DetFormula sigma rho1 rho2 n_s
      = - ((rho2.val - 1) ^ (n_s - 2)
            * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (n_s - 2)
            * (sigma.val ^ 2) ^ n_s
          / (rho1.val ^ 2 - 1) ^ (n_s - 3)) := rfl

/-- `qpsk.exceed` field unfold: `if s = s_hat then 0 else 1`. -/
example :
    qpsk.exceed = fun s s_hat => if s = s_hat then (0 : Real) else 1 := rfl

/-- `ChannelError.dimensionMismatch` carries expected/got pair verbatim. -/
example (expected got : Nat) :
    (ChannelError.dimensionMismatch expected got : ChannelError)
      = ChannelError.dimensionMismatch expected got := rfl

/-- Concrete `AbandonmentBudget` literal `{ toNat := 42 }` projects to `42`. -/
example : ({ toNat := 42 } : AbandonmentBudget).toNat = 42 := rfl

/-- BPSK exceedance is non-negative (projection of `Constellation.exceed_nonneg`
    at `bpsk`). -/
example (s s_hat : Bool) : (0 : Real) <= bpsk.exceed s s_hat :=
  bpsk.exceed_nonneg s s_hat

/-- `ChannelError.correlationOutOfRange` carries the offending real verbatim. -/
example (v : Real) :
    (ChannelError.correlationOutOfRange v : ChannelError)
      = ChannelError.correlationOutOfRange v := rfl

/-- QPSK exceedance on distinct `Fin 4` values `(1, 3)` reduces to `1`. -/
example : qpsk.exceed (1 : Fin 4) (3 : Fin 4) = 1 := rfl

/-- QPSK exceedance on the diagonal at `(2, 2)` reduces to `0`. -/
example : qpsk.exceed (2 : Fin 4) (2 : Fin 4) = 0 := rfl

/-- `gaussMarkov2` at size 4 on the diagonal `(1, 1)` reduces to `sigma.val`
    via the `cov2_lag` lag-0 base case. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 4 1 1 = sigma.val := rfl

/-- `ar2` base case at index 0 with `z1 = z2 = z` reduces to `z`. -/
example (phi1 phi2 z : Complex) :
    ar2 phi1 phi2 z z 0 = z := rfl

/-- `ChannelError.noPaths` is a nullary constructor. -/
example : (ChannelError.noPaths : ChannelError) = ChannelError.noPaths := rfl

/-- `ChannelError.nonPositiveSamplingFreq` carries the offending real verbatim. -/
example (v : Real) :
    (ChannelError.nonPositiveSamplingFreq v : ChannelError)
      = ChannelError.nonPositiveSamplingFreq v := rfl

/-- QPSK exceedance is non-negative (projection of `Constellation.exceed_nonneg`
    at `qpsk`). -/
example (s s_hat : Fin 4) : (0 : Real) <= qpsk.exceed s s_hat :=
  qpsk.exceed_nonneg s s_hat

/-- QPSK `exceed_zero_iff` projection: exceedance vanishes iff symbols agree. -/
example (s s_hat : Fin 4) :
    qpsk.exceed s s_hat = 0 <-> s = s_hat :=
  qpsk.exceed_zero_iff s s_hat

/-- `landslide 3 1` is the three-deep singleton with bit 0 set
    (`withTop` suppressed at every level). -/
example : landslide 3 1
    = [landslideExtend false
        (landslideExtend false (landslideExtend true Fin.elim0))] := rfl

/-- BPSK `exceed_zero_iff` projection: exceedance vanishes iff symbols agree. -/
example (s s_hat : Bool) :
    bpsk.exceed s s_hat = 0 <-> s = s_hat :=
  bpsk.exceed_zero_iff s s_hat

/-- `landslide 4 0` is the singleton all-false pattern at length 4. -/
example : landslide 4 0
    = [landslideExtend false
        (landslideExtend false
          (landslideExtend false (landslideExtend false Fin.elim0)))] := rfl

/-- `gaussMarkov2` at size 2 and off-diagonal `(0, 1)` reduces to
    `sigma.val * rho1.val` via `cov2_lag` lag-1 base case. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 2 0 1 = sigma.val * rho1.val := rfl

/-- `gaussMarkov2` at size 2 and the diagonal `(0, 0)` reduces to `sigma.val`
    via `cov2_lag` lag-0 base case. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 2 0 0 = sigma.val := rfl

/-- `ar2` with zero coefficients at depth 2 collapses to `0 * z2 + 0 * z1`
    (pre-multiplication-collapse pattern-match unfold). -/
example (z1 z2 : Complex) :
    ar2 0 0 z1 z2 2 = 0 * z2 + 0 * z1 := rfl

/-- `ar2` with `phi1 = 1`, `phi2 = 0` at depth 5 fires the `(n + 2)` pattern
    three times; each `phi2` contribution collapses to `0`. -/
example (z1 z2 : Complex) :
    ar2 1 0 z1 z2 5
      = 1 * (1 * (1 * (1 * z2 + 0 * z1) + 0 * z2) + 0 * (1 * z2 + 0 * z1))
        + 0 * (1 * (1 * z2 + 0 * z1) + 0 * z2) := rfl

/-- `cov2_lag` at lag 7 unfolds via the `(n + 3)` recurrence to a weighted sum
    at lags 6 and 5. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 7
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 6
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 5 := rfl

/-- `cov2_lag` at lag 8 unfolds via the `(n + 3)` recurrence to a weighted sum
    at lags 7 and 6. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 8
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 7
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 6 := rfl

/-- `ar2` at concrete index 7: the `(n + 2)` pattern at `n = 5` unfolds to
    a `(phi1, phi2)`-weighted sum at indices 6 and 5. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 7
      = phi1 * ar2 phi1 phi2 z1 z2 6
        + phi2 * ar2 phi1 phi2 z1 z2 5 := rfl

/-- `cov2_lag` at lag 9 unfolds via the `(n + 3)` recurrence to a weighted sum
    at lags 8 and 7. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 9
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 8
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 7 := rfl

/-- `ar2` at concrete index 8: the `(n + 2)` pattern at `n = 6` unfolds to
    a `(phi1, phi2)`-weighted sum at indices 7 and 6. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 8
      = phi1 * ar2 phi1 phi2 z1 z2 7
        + phi2 * ar2 phi1 phi2 z1 z2 6 := rfl

/-- `landslide 4 2` is the four-deep singleton: bit 1 set, all other bits
    unset.  The two outer `withTop` branches are suppressed; the innermost
    `landslide 2 2` fires its `withTop` branch with weight residue 0. -/
example : landslide 4 2
    = [landslideExtend false
        (landslideExtend false
          (landslideExtend true (landslideExtend false Fin.elim0)))] := rfl

/-- `landslide 4 3` is the two-element bucket: only `withoutTop` fires at the
    outer level, passing the two `landslide 3 3` patterns through
    `landslideExtend false`. -/
example : landslide 4 3
    = [landslideExtend false
        (landslideExtend true
          (landslideExtend false (landslideExtend false Fin.elim0))),
       landslideExtend false
        (landslideExtend false
          (landslideExtend true (landslideExtend true Fin.elim0)))] := rfl

/-- `gaussMarkov2` at size 5 on the diagonal `(3, 3)` reduces to `sigma.val`
    via the `cov2_lag` lag-0 base case. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 5 3 3 = sigma.val := rfl

/-- `cov2_lag` at lag 10 unfolds via the `(n + 3)` recurrence to a weighted sum
    at lags 9 and 8. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 10
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 9
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 8 := rfl

/-- `ar2` at concrete index 9: the `(n + 2)` pattern at `n = 7` unfolds. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 9
      = phi1 * ar2 phi1 phi2 z1 z2 8
        + phi2 * ar2 phi1 phi2 z1 z2 7 := rfl

/-- BPSK exceedance on `(false, true)` is `1`. -/
example : bpsk.exceed false true = 1 := rfl

/-- BPSK exceedance on `(false, false)` is `0`. -/
example : bpsk.exceed false false = 0 := rfl

/-- QPSK exceedance on `(3, 0)` is `1`; complements the existing `(0, 1)`
    direction lock at the reversed Fin pair. -/
example : qpsk.exceed (3 : Fin 4) (0 : Fin 4) = 1 := rfl

/-- `cov2_lag` at lag 3 with concrete `beta1 = 0` fires the `(n + 3)`
    recurrence with the first term collapsed to `0`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta2 : Real) :
    cov2_lag sigma rho1 rho2 0 beta2 3
      = 0 * cov2_lag sigma rho1 rho2 0 beta2 2
        + beta2 * cov2_lag sigma rho1 rho2 0 beta2 1 := rfl

/-- `cov2_lag` at lag 11 unfolds via the `(n + 3)` recurrence to a weighted sum
    at lags 10 and 9. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 11
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 10
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 9 := rfl

/-- `ar2` at concrete index 10: `(n + 2)` pattern at `n = 8`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 10
      = phi1 * ar2 phi1 phi2 z1 z2 9
        + phi2 * ar2 phi1 phi2 z1 z2 8 := rfl

/-- `landslide 5 1` is the five-deep singleton with bit 0 set. -/
example : landslide 5 1
    = [landslideExtend false
        (landslideExtend false
          (landslideExtend false
            (landslideExtend false (landslideExtend true Fin.elim0))))] := rfl

/-- `LinearIsi.causal` unfolds to: every entry strictly above the diagonal vanishes. -/
example {n_s : Nat} (ch : LinearIsi n_s) :
    ch.causal
      = forall (i j : Fin n_s), i.val < j.val -> ch.channel i j = 0 := rfl

/-- `LinearIsi.bandwidth b` unfolds to: every entry below the `b`-th sub-diagonal
    vanishes. -/
example {n_s : Nat} (ch : LinearIsi n_s) (b : Nat) :
    ch.bandwidth b
      = forall (i j : Fin n_s), j.val + b < i.val -> ch.channel i j = 0 := rfl

/-- `CarrierFreq.val` projection through anonymous constructor. -/
example (v : Real) (h : 0 < v) :
    ({ val := v, pos := h } : CarrierFreq).val = v := rfl

/-- `CarrierFreq.pos` projection through anonymous constructor;
    pairs with `val` to pin the two-field carrier order. -/
example (v : Real) (h : 0 < v) :
    ({ val := v, pos := h } : CarrierFreq).pos = h := rfl

/-- `ar2` at concrete index 11: `(n + 2)` pattern at `n = 9`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 11
      = phi1 * ar2 phi1 phi2 z1 z2 10
        + phi2 * ar2 phi1 phi2 z1 z2 9 := rfl

/-- `cov2_lag` at lag 12 unfolds via the `(n + 3)` recurrence to a weighted sum
    at lags 11 and 10. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 12
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 11
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 10 := rfl

/-- `orbgrandEnumeration n w` is exactly `landslide n w` (def unfold). -/
example (n w : Nat) :
    orbgrandEnumeration n w = landslide n w := rfl

/-- `noSymbolConflict` body unfold: the `(i ≠ j -> ... -> True)` implication structure. -/
example {n_s : Nat} {chi : Type} (e : Fin n_s -> Option chi) :
    noSymbolConflict e
      = forall (i j : Fin n_s),
          i ≠ j -> e i ≠ none -> e j ≠ none -> True := rfl

/-- `trivialConstellation.exceed` is the constant-zero function (field projection). -/
example : trivialConstellation.exceed = fun _ _ => (0 : Real) := rfl

/-- `ar2` at concrete index 12: `(n + 2)` pattern at `n = 10`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 12
      = phi1 * ar2 phi1 phi2 z1 z2 11
        + phi2 * ar2 phi1 phi2 z1 z2 10 := rfl

/-- `cov2_lag` at lag 13: `(n + 3)` recurrence step at lags 12 and 11. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 13
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 12
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 11 := rfl

/-- `sinc` body unfold: if-then-else on `x = 0`. -/
example (x : Real) :
    sinc x = if x = 0 then 1 else Real.sin (Real.pi * x) / (Real.pi * x) := rfl

/-- `rfViewMatrix` body unfold: dependent if on `j.val <= i.val`, falling back to
    `(rowTaps i).tap? (i.val - j.val + 1)` lifted through `Option.getD 0`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s) :
    rfViewMatrix n_s rowTaps i j
      = (if j.val <= i.val then
          ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex)
        else
          (0 : Complex)) := rfl

/-- `rfView` body unfold: `LinearIsi` with `rfViewMatrix` channel and white-noise
    covariance `if i = j then sigma else 0`. -/
example (n_s : Nat) (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    rfView n_s rowTaps sigma
      = { channel := rfViewMatrix n_s rowTaps,
          noiseCov := fun i j =>
            if i.val = j.val then (sigma.val : Complex) else (0 : Complex) } := rfl

/-- `DelayTapPath.attenuation` projection through anonymous constructor. -/
example (a : Complex) (tau : Real) :
    ({ attenuation := a, delay := tau } : DelayTapPath).attenuation = a := rfl

/-- `DelayTapPath.delay` projection through anonymous constructor;
    pairs with `attenuation` to pin the two-field carrier order. -/
example (a : Complex) (tau : Real) :
    ({ attenuation := a, delay := tau } : DelayTapPath).delay = tau := rfl

/-- `SymbolIndex.toNat` projection through anonymous constructor. -/
example (n : Nat) : ({ toNat := n } : SymbolIndex).toNat = n := rfl

/-- `SequenceLength.toNat` projection through anonymous constructor. -/
example (n : Nat) : ({ toNat := n } : SequenceLength).toNat = n := rfl

/-- `delayTapMatrix` body unfold: dependent if on `j.val <= i.val`, then
    `delayTapImpulseResponse` at delay `i.val - j.val`, else `0`. -/
example {p : Nat} (n_s : Nat) (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) :
    delayTapMatrix n_s paths f_s i j
      = (if h : j.val <= i.val then
          delayTapImpulseResponse paths f_s { toNat := i.val - j.val }
        else
          (0 : Complex)) := rfl

/-- `delayTapImpulseResponse` body: `Finset.univ.sum` of `attenuation` times
    Complex-coerced `sinc(tau * f_s - k')` over paths. -/
example {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (k' : SymbolIndex) :
    delayTapImpulseResponse paths f_s k'
      = Finset.univ.sum fun d =>
          let path := paths d
          path.attenuation *
            ((sinc (path.delay * f_s.val - (k'.toNat : Real)) : Real) : Complex) := rfl

/-- `RFViewTaps.tap?` at index 1 returns `some t.tap1`. -/
example (t : RFViewTaps) : t.tap? 1 = some t.tap1 := rfl

/-- `RFViewTaps.tap?` at index 2 returns `some t.tap2`. -/
example (t : RFViewTaps) : t.tap? 2 = some t.tap2 := rfl

/-- `RFViewTaps.tap?` at index 6 returns `some t.tap6` (last valid branch). -/
example (t : RFViewTaps) : t.tap? 6 = some t.tap6 := rfl

/-- `ar2` at concrete index 13: `(n + 2)` pattern at `n = 11`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 13
      = phi1 * ar2 phi1 phi2 z1 z2 12
        + phi2 * ar2 phi1 phi2 z1 z2 11 := rfl

/-- `cov2_lag` at lag 14: `(n + 3)` recurrence step at lags 13 and 12. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 14
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 13
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 12 := rfl

/-- `RFViewTaps.tap?` at index 4 returns `some t.tap4`. -/
example (t : RFViewTaps) : t.tap? 4 = some t.tap4 := rfl

/-- `RFViewTaps.tap?` at index 5 returns `some t.tap5`. -/
example (t : RFViewTaps) : t.tap? 5 = some t.tap5 := rfl

/-- `ar2` at concrete index 14: `(n + 2)` pattern at `n = 12`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 14
      = phi1 * ar2 phi1 phi2 z1 z2 13
        + phi2 * ar2 phi1 phi2 z1 z2 12 := rfl

/-- `cov2_lag` at lag 15: `(n + 3)` recurrence step at lags 14 and 13. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 15
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 14
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 13 := rfl

/-- `gaussMarkov2` size 5 off-diagonal `(1, 0)`: ELSE branch with `d = 1`,
    `cov2_lag` lag-1 base case `sigma.val * rho1.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 5 1 0 = sigma.val * rho1.val := rfl

/-- `gaussMarkov2` size 6 diagonal `(5, 5)` reduces to `sigma.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 6 5 5 = sigma.val := rfl

/-- `ar2` with `phi2 = 0` at depth 3: each `phi2` contribution collapses to `0`. -/
example (phi1 z1 z2 : Complex) :
    ar2 phi1 0 z1 z2 3 = phi1 * (phi1 * z2 + 0 * z1) + 0 * z2 := rfl

/-- `ar2` base case at index 0 with `z1 = 0` reduces to `0`. -/
example (phi1 phi2 z2 : Complex) :
    ar2 phi1 phi2 0 z2 0 = 0 := rfl

/-- `cov2_lag` at lag 4: `(n + 3)` recurrence step at lags 3 and 2. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 4
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 3
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 2 := rfl

/-- `cov2_lag` at lag 16: `(n + 3)` recurrence step at lags 15 and 14. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 16
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 15
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 14 := rfl

/-- `ar2` at concrete index 15: `(n + 2)` pattern at `n = 13`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 15
      = phi1 * ar2 phi1 phi2 z1 z2 14
        + phi2 * ar2 phi1 phi2 z1 z2 13 := rfl

/-- `gaussMarkov2` size 4 off-diagonal `(1, 3)`: THEN branch with `d = 2`,
    `cov2_lag` lag-2 base case yields `sigma.val * rho2.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 4 1 3 = sigma.val * rho2.val := rfl

/-- `CorrelationCoefficient.val` projection through anonymous constructor;
    pairs with the existing `.nonneg` / `.le_one` projections to lock all three fields. -/
example (v : Real) (h0 : 0 <= v) (h1 : v <= 1) :
    ({ val := v, nonneg := h0, le_one := h1 } : CorrelationCoefficient).val = v := rfl

/-- `SignalPower.nonneg` projection through anonymous constructor;
    pairs with the existing `.val` projection to pin the two-field carrier order. -/
example (v : Real) (h : 0 <= v) :
    ({ val := v, nonneg := h } : SignalPower).nonneg = h := rfl

/-- `BlockSize.pos` projection through anonymous constructor (pairs with `toNat`). -/
example (n : Nat) (h : 0 < n) :
    ({ toNat := n, pos := h } : BlockSize).pos = h := rfl

/-- `CodewordLength.pos` projection through anonymous constructor (pairs with `toNat`). -/
example (n : Nat) (h : 0 < n) :
    ({ toNat := n, pos := h } : CodewordLength).pos = h := rfl

/-- `BitsPerSymbol.pos` projection through anonymous constructor (pairs with `toNat`). -/
example (n : Nat) (h : 0 < n) :
    ({ toNat := n, pos := h } : BitsPerSymbol).pos = h := rfl

/-- `SamplingFreq.pos` projection through anonymous constructor (pairs with `val`). -/
example (v : Real) (h : 0 < v) :
    ({ val := v, pos := h } : SamplingFreq).pos = h := rfl

/-- `ConstellationSize.pos` projection through anonymous constructor (pairs with `toNat`). -/
example (n : Nat) (h : 0 < n) :
    ({ toNat := n, pos := h } : ConstellationSize).pos = h := rfl

/-- `ReliabilityRank.bijective` projection through anonymous constructor. -/
example {n : Nat} (p : Fin n -> Fin n)
    (hb : Function.Bijective p)
    (hm : forall (rel : BitReliability n) (i j : Fin n),
      i.val <= j.val -> rel (p i) <= rel (p j)) :
    ({ perm := p, bijective := hb, monotone := hm } : ReliabilityRank n).bijective
      = hb := rfl

/-- `ReliabilityRank.monotone` projection through anonymous constructor;
    completes the 3-field carrier projection set. -/
example {n : Nat} (p : Fin n -> Fin n)
    (hb : Function.Bijective p)
    (hm : forall (rel : BitReliability n) (i j : Fin n),
      i.val <= j.val -> rel (p i) <= rel (p j)) :
    ({ perm := p, bijective := hb, monotone := hm } : ReliabilityRank n).monotone
      = hm := rfl

/-- `ar2` at concrete index 16: `(n + 2)` pattern at `n = 14`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 16
      = phi1 * ar2 phi1 phi2 z1 z2 15
        + phi2 * ar2 phi1 phi2 z1 z2 14 := rfl

/-- `cov2_lag` at lag 17: `(n + 3)` recurrence step at lags 16 and 15. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 17
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 16
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 15 := rfl

/-- `gaussMarkov2` size 7 diagonal `(4, 4)` reduces to `sigma.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 7 4 4 = sigma.val := rfl

/-- QPSK exceedance at diagonal `(0, 0)` is `0`. -/
example : qpsk.exceed (0 : Fin 4) (0 : Fin 4) = 0 := rfl

/-- QPSK exceedance at diagonal `(3, 3)` is `0`. -/
example : qpsk.exceed (3 : Fin 4) (3 : Fin 4) = 0 := rfl

/-- `ar2` at concrete index 17: `(n + 2)` pattern at `n = 15`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 17
      = phi1 * ar2 phi1 phi2 z1 z2 16
        + phi2 * ar2 phi1 phi2 z1 z2 15 := rfl

/-- `cov2_lag` at lag 18: `(n + 3)` recurrence step at lags 17 and 16. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 18
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 17
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 16 := rfl

/-- `gaussMarkov2` body zeta-unfold: spells out the let-bound `beta1` / `beta2`
    via if-then-else on `(1 - rho1.val^2) = 0`, returning `cov2_lag` at the
    symmetric `|i.val - j.val|`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (n_s : Nat) :
    gaussMarkov2 sigma rho1 rho2 n_s
      = fun i j =>
          cov2_lag sigma rho1 rho2
            (if (1 - rho1.val ^ 2) = 0 then 0
             else rho1.val * (1 - rho2.val) / (1 - rho1.val ^ 2))
            (if (1 - rho1.val ^ 2) = 0 then 0
             else (rho2.val - rho1.val ^ 2) / (1 - rho1.val ^ 2))
            (if i.val <= j.val then j.val - i.val else i.val - j.val) := rfl

/-- `ar2` at concrete index 18: `(n + 2)` pattern at `n = 16`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 18
      = phi1 * ar2 phi1 phi2 z1 z2 17
        + phi2 * ar2 phi1 phi2 z1 z2 16 := rfl

/-- `cov2_lag` at lag 19: `(n + 3)` recurrence step at lags 18 and 17. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 19
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 18
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 17 := rfl

/-- `landslide 5 2` is the five-deep singleton: bit 1 set, all other bits unset. -/
example : landslide 5 2
    = [landslideExtend false
        (landslideExtend false
          (landslideExtend false
            (landslideExtend true (landslideExtend false Fin.elim0))))] := rfl

/-- `cov2_lag` at lag 3 with concrete `beta2 = 0`: second recurrence term collapses to `0`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 : Real) :
    cov2_lag sigma rho1 rho2 beta1 0 3
      = beta1 * cov2_lag sigma rho1 rho2 beta1 0 2
        + 0 * cov2_lag sigma rho1 rho2 beta1 0 1 := rfl

/-- `ar2` at concrete index 19: `(n + 2)` pattern at `n = 17`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 19
      = phi1 * ar2 phi1 phi2 z1 z2 18
        + phi2 * ar2 phi1 phi2 z1 z2 17 := rfl

/-- `cov2_lag` at lag 20: `(n + 3)` recurrence step at lags 19 and 18. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 20
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 19
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 18 := rfl

/-- `ar2` with `phi1 = 0`, `phi2 = 1` at depth 3: `phi1` contribution collapses. -/
example (z1 z2 : Complex) :
    ar2 0 1 z1 z2 3 = 0 * (0 * z2 + 1 * z1) + 1 * z2 := rfl

/-- `gaussMarkov2` size 6 off-diagonal `(0, 5)`: THEN branch with `d = 5`,
    `cov2_lag` lag-5 recurrence step (`(n + 3)` at `n = 2`) with concrete
    beta1 / beta2 if-then-else expansions. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 6 0 5
      = (if (1 - rho1.val ^ 2) = 0 then 0
         else rho1.val * (1 - rho2.val) / (1 - rho1.val ^ 2))
          * cov2_lag sigma rho1 rho2
              (if (1 - rho1.val ^ 2) = 0 then 0
               else rho1.val * (1 - rho2.val) / (1 - rho1.val ^ 2))
              (if (1 - rho1.val ^ 2) = 0 then 0
               else (rho2.val - rho1.val ^ 2) / (1 - rho1.val ^ 2))
              4
        + (if (1 - rho1.val ^ 2) = 0 then 0
           else (rho2.val - rho1.val ^ 2) / (1 - rho1.val ^ 2))
          * cov2_lag sigma rho1 rho2
              (if (1 - rho1.val ^ 2) = 0 then 0
               else rho1.val * (1 - rho2.val) / (1 - rho1.val ^ 2))
              (if (1 - rho1.val ^ 2) = 0 then 0
               else (rho2.val - rho1.val ^ 2) / (1 - rho1.val ^ 2))
              3 := rfl

/-- `landslide 5 3` is a two-element bucket: outer level suppresses `withTop`
    (`5 > 3`), so the result is `(landslide 4 3).map (landslideExtend false)`. -/
example : landslide 5 3
    = [landslideExtend false
        (landslideExtend false
          (landslideExtend true
            (landslideExtend false (landslideExtend false Fin.elim0)))),
       landslideExtend false
        (landslideExtend false
          (landslideExtend false
            (landslideExtend true (landslideExtend true Fin.elim0))))] := rfl

/-- `ar2` at concrete index 20: `(n + 2)` pattern at `n = 18`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 20
      = phi1 * ar2 phi1 phi2 z1 z2 19
        + phi2 * ar2 phi1 phi2 z1 z2 18 := rfl

/-- `cov2_lag` at lag 21: `(n + 3)` recurrence step at lags 20 and 19. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 21
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 20
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 19 := rfl

/-- `landslide 5 4` is a two-element bucket: outer suppresses `withTop` (`5 > 4`),
    so the result is `(landslide 4 4).map (landslideExtend false)`. -/
example : landslide 5 4
    = [landslideExtend false
        (landslideExtend true
          (landslideExtend false
            (landslideExtend false (landslideExtend false Fin.elim0)))),
       landslideExtend false
        (landslideExtend false
          (landslideExtend true
            (landslideExtend false (landslideExtend true Fin.elim0))))] := rfl

/-- `ar2` at concrete index 21: `(n + 2)` pattern at `n = 19`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 21
      = phi1 * ar2 phi1 phi2 z1 z2 20
        + phi2 * ar2 phi1 phi2 z1 z2 19 := rfl

/-- `cov2_lag` at lag 22: `(n + 3)` recurrence step at lags 21 and 20. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 22
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 21
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 20 := rfl

/-- `gaussMarkov2` size 7 off-diagonal `(6, 0)`: ELSE branch with `d = 6`,
    `cov2_lag` lag-6 `(n + 3)` recurrence (`n = 3`) with concrete beta1 / beta2
    if-then-else expansions; mirrors the size-6 `(0, 5)` THEN-branch lock one
    lag deeper. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 7 6 0
      = (if (1 - rho1.val ^ 2) = 0 then 0
         else rho1.val * (1 - rho2.val) / (1 - rho1.val ^ 2))
          * cov2_lag sigma rho1 rho2
              (if (1 - rho1.val ^ 2) = 0 then 0
               else rho1.val * (1 - rho2.val) / (1 - rho1.val ^ 2))
              (if (1 - rho1.val ^ 2) = 0 then 0
               else (rho2.val - rho1.val ^ 2) / (1 - rho1.val ^ 2))
              5
        + (if (1 - rho1.val ^ 2) = 0 then 0
           else (rho2.val - rho1.val ^ 2) / (1 - rho1.val ^ 2))
          * cov2_lag sigma rho1 rho2
              (if (1 - rho1.val ^ 2) = 0 then 0
               else rho1.val * (1 - rho2.val) / (1 - rho1.val ^ 2))
              (if (1 - rho1.val ^ 2) = 0 then 0
               else (rho2.val - rho1.val ^ 2) / (1 - rho1.val ^ 2))
              4 := rfl

/-- `ar2` with `phi1 = phi2 = 0` at depth 4 collapses every term to `0 * ...`. -/
example (z1 z2 : Complex) :
    ar2 0 0 z1 z2 4
      = 0 * (0 * (0 * z2 + 0 * z1) + 0 * z2)
        + 0 * (0 * z2 + 0 * z1) := rfl

/-- `gaussMarkov2` size 4 off-diagonal `(2, 0)`: ELSE branch with `d = 2`,
    `cov2_lag` lag-2 base case `sigma.val * rho2.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 4 2 0 = sigma.val * rho2.val := rfl

/-- `ar2` at concrete index 22: `(n + 2)` pattern at `n = 20`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 22
      = phi1 * ar2 phi1 phi2 z1 z2 21
        + phi2 * ar2 phi1 phi2 z1 z2 20 := rfl

/-- `cov2_lag` at lag 23: `(n + 3)` recurrence step at lags 22 and 21. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 23
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 22
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 21 := rfl

/-- `gaussMarkov2` size 8 diagonal `(7, 7)` reduces to `sigma.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 8 7 7 = sigma.val := rfl

/-- `gaussMarkov2` size 8 off-diagonal `(7, 6)`: ELSE branch with `d = 1`,
    `cov2_lag` lag-1 base case `sigma.val * rho1.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 8 7 6 = sigma.val * rho1.val := rfl

/-- `landslide 6 0` is the singleton all-false pattern at length 6. -/
example : landslide 6 0
    = [landslideExtend false
        (landslideExtend false
          (landslideExtend false
            (landslideExtend false
              (landslideExtend false (landslideExtend false Fin.elim0)))))] := rfl

/-- `landslide 6 1` is the six-deep singleton with bit 0 set. -/
example : landslide 6 1
    = [landslideExtend false
        (landslideExtend false
          (landslideExtend false
            (landslideExtend false
              (landslideExtend false (landslideExtend true Fin.elim0)))))] := rfl

/-- `landslide 6 6` is the four-element bucket: outer `withTop` fires (`6 <= 6`)
    yielding the singleton top-bit-only pattern; `withoutTop` enumerates the
    three length-5 weight-6 patterns under `landslideExtend false`. -/
example : landslide 6 6
    = [landslideExtend true
        (landslideExtend false
          (landslideExtend false
            (landslideExtend false
              (landslideExtend false (landslideExtend false Fin.elim0))))),
       landslideExtend false
        (landslideExtend true
          (landslideExtend false
            (landslideExtend false
              (landslideExtend false (landslideExtend true Fin.elim0))))),
       landslideExtend false
        (landslideExtend false
          (landslideExtend true
            (landslideExtend false
              (landslideExtend true (landslideExtend false Fin.elim0))))),
       landslideExtend false
        (landslideExtend false
          (landslideExtend false
            (landslideExtend true
              (landslideExtend true (landslideExtend true Fin.elim0)))))] := rfl

/-- `ar2` at concrete index 23: `(n + 2)` pattern at `n = 21`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 23
      = phi1 * ar2 phi1 phi2 z1 z2 22
        + phi2 * ar2 phi1 phi2 z1 z2 21 := rfl

/-- `cov2_lag` at lag 24: `(n + 3)` recurrence step at lags 23 and 22. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 24
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 23
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 22 := rfl

/-- `gaussMarkov2` size 10 diagonal `(5, 5)` reduces to `sigma.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 10 5 5 = sigma.val := rfl

/-- `gaussMarkov2` size 5 off-diagonal `(0, 2)`: THEN branch with `d = 2`,
    `cov2_lag` lag-2 base case `sigma.val * rho2.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 5 0 2 = sigma.val * rho2.val := rfl

/-- `gaussMarkov2` size 5 diagonal `(0, 0)` reduces to `sigma.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 5 0 0 = sigma.val := rfl

/-- `landslide 6 2` is the six-deep singleton with bit 1 set. -/
example : landslide 6 2
    = [landslideExtend false
        (landslideExtend false
          (landslideExtend false
            (landslideExtend false
              (landslideExtend true (landslideExtend false Fin.elim0)))))] := rfl

/-- `ar2` at concrete index 24: `(n + 2)` pattern at `n = 22`. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 24
      = phi1 * ar2 phi1 phi2 z1 z2 23
        + phi2 * ar2 phi1 phi2 z1 z2 22 := rfl

/-- `cov2_lag` at lag 25: `(n + 3)` recurrence step at lags 24 and 23. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 25
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 24
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 23 := rfl

/-- `gaussMarkov2` size 6 diagonal `(0, 0)` reduces to `sigma.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 6 0 0 = sigma.val := rfl

/-- `gaussMarkov2` size 6 off-diagonal `(1, 2)`: THEN branch with `d = 1`,
    `cov2_lag` lag-1 base case `sigma.val * rho1.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 6 1 2 = sigma.val * rho1.val := rfl

/-- `gaussMarkov2` size 7 off-diagonal `(2, 4)`: THEN branch with `d = 2`,
    `cov2_lag` lag-2 base case `sigma.val * rho2.val`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) :
    gaussMarkov2 sigma rho1 rho2 7 2 4 = sigma.val * rho2.val := rfl

/-- Zero perturbation is the identity on the channel. -/
example {n_s : Nat} (h : ChannelMatrix n_s) :
    perturbChannel h 0 = h :=
  perturbChannel_zero h

/-- Section VI.B imperfect-CSI error-floor statement (probabilistic form): positive
    NMSE yields a positive floor on the actual `Section00.bler` for every decoder
    family parameterised by per-SNR noise power. -/
example (nmse : NMSE) (sigma : NoisePower) (rho : CorrelationCoefficient)
    (h : 0 < nmse.val ->
      exists (floor : Real),
        0 < floor /\
        forall {n_s : Nat}
          (decoder : NoisePower -> Section00.RealSymbolVector n_s -> Bool),
          forall (snrSigma : NoisePower), snrSigma.val <= sigma.val ->
            floor <= Section00.bler snrSigma (decoder snrSigma)) :
    True :=
  imperfect_csi_error_floor_statement nmse sigma rho h

/-- Section VI.C query-order stability statement (refactored): Kendall tau
    between the query orders at `rho_real.val` and `rho_real.val + delta_rho`,
    parameterised by an abstract `queryOrder` family, is Lipschitz in
    `|delta_rho|` (for `|delta_rho| <= 0.2`). -/
example (rho_real : CorrelationCoefficient) (numPatterns : Nat)
    (h : forall (queryOrder : Real -> QueryOrder numPatterns),
      exists (K : Real), 0 < K /\
        forall (delta_rho : Real),
          abs delta_rho <= 0.2 ->
            (kendallTau (queryOrder rho_real.val)
                        (queryOrder (rho_real.val + delta_rho)) : Real)
              <= K * abs delta_rho) :
    True :=
  query_order_stability_statement rho_real numPatterns h

/-- `QueryOrder.positionOf` base case: empty list returns 0. -/
example {numPatterns : Nat} (x : Fin numPatterns) :
    QueryOrder.positionOf x ([] : QueryOrder numPatterns) = 0 := rfl

/-- `QueryOrder.positionOf` cons-head match returns 0. -/
example {numPatterns : Nat} (x : Fin numPatterns) (ys : QueryOrder numPatterns) :
    QueryOrder.positionOf x (x :: ys) = 0 := if_pos rfl

/-- `kendallTau` empty/empty is 0 (no `i.val < j.val` pairs in `Fin 0`). -/
example : kendallTau ([] : QueryOrder 0) [] = 0 := rfl

/-- `kendallTau` on `Fin 1` lists is 0 (no `i.val < j.val` pairs in `Fin 1`). -/
example (a b : QueryOrder 1) : kendallTau a b = 0 := rfl

/-- *Non-negativity of `kendallTau`*: the Nat-valued metric is always >= 0. -/
example {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    0 <= kendallTau a b :=
  kendallTau_nonneg a b

/-- *Reflexivity of `kendallTau`*: every list disagrees with itself on zero pairs. -/
example {numPatterns : Nat} (a : QueryOrder numPatterns) :
    kendallTau a a = 0 :=
  kendallTau_self a

/-- `kendallTau` on the same `Fin 2` list `[0, 1]` is 0 (concrete reflexivity). -/
example : kendallTau ([0, 1] : QueryOrder 2) [0, 1] = 0 :=
  kendallTau_self [0, 1]

/-- *Symmetry of `kendallTau`*: order of arguments does not matter. -/
example {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    kendallTau a b = kendallTau b a :=
  kendallTau_symm a b

/-- Concrete symmetry instance on `QueryOrder 2`. -/
example : kendallTau ([0, 1] : QueryOrder 2) ([1, 0] : QueryOrder 2)
        = kendallTau ([1, 0] : QueryOrder 2) [0, 1] :=
  kendallTau_symm [0, 1] [1, 0]

/-- *Per-summand bound on `kendallTau`*: every `(i, j)` summand is at most `1`. -/
example {numPatterns : Nat} (a b : QueryOrder numPatterns)
    (i j : Fin numPatterns) :
    (if i.val < j.val then
        let ai := QueryOrder.positionOf i a
        let aj := QueryOrder.positionOf j a
        let bi := QueryOrder.positionOf i b
        let bj := QueryOrder.positionOf j b
        if decide (ai < aj) = decide (bi < bj) then (0 : Nat) else 1
      else 0) ≤ 1 :=
  kendallTau_summand_le_one a b i j

/-- *Upper bound on `kendallTau`*: at most `numPatterns * numPatterns`. -/
example {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    kendallTau a b ≤ numPatterns * numPatterns :=
  kendallTau_le_sq a b

/-- *Agreement implies zero distance*: if `a` and `b` order every pair
    the same way, their Kendall-tau distance is zero. -/
example {numPatterns : Nat} (a b : QueryOrder numPatterns)
    (h : forall (i j : Fin numPatterns), i.val < j.val ->
      decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
        = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b)) :
    kendallTau a b = 0 :=
  kendallTau_eq_zero_of_agreement a b h

/-- `kendallTau_self` factors through `kendallTau_eq_zero_of_agreement` via
    the trivial `rfl` agreement witness. -/
example {numPatterns : Nat} (a : QueryOrder numPatterns) :
    kendallTau a a = 0 :=
  kendallTau_eq_zero_of_agreement a a (fun _ _ _ => rfl)

/-- *Zero distance implies agreement* (the converse half of the iff): if
    `kendallTau a b = 0`, then every pair `i.val < j.val` is ordered the same way. -/
example {numPatterns : Nat} (a b : QueryOrder numPatterns)
    (h : kendallTau a b = 0)
    (i j : Fin numPatterns) (hij : i.val < j.val) :
    decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
      = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b) :=
  kendallTau_agreement_of_eq_zero a b h i j hij

/-- *Zero-distance characterization (iff)*: `kendallTau a b = 0` iff `a` and `b`
    order every pair `i.val < j.val` the same way.  Both directions packaged. -/
example {numPatterns : Nat} (a b : QueryOrder numPatterns) :
    kendallTau a b = 0 ↔
      forall (i j : Fin numPatterns), i.val < j.val ->
        decide (QueryOrder.positionOf i a < QueryOrder.positionOf j a)
          = decide (QueryOrder.positionOf i b < QueryOrder.positionOf j b) :=
  kendallTau_eq_zero_iff a b

/-- *Triangle inequality on `kendallTau`*: for any three query orders,
    `kendallTau a c ≤ kendallTau a b + kendallTau b c`.  Combined with
    reflexivity and symmetry, `kendallTau` is a metric on `QueryOrder numPatterns`. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns) :
    kendallTau a c ≤ kendallTau a b + kendallTau b c :=
  kendallTau_triangle a b c

/-- Concrete triangle instance on `QueryOrder 2`. -/
example : kendallTau ([0, 1] : QueryOrder 2) ([0, 1] : QueryOrder 2)
        ≤ kendallTau ([0, 1] : QueryOrder 2) [1, 0]
          + kendallTau ([1, 0] : QueryOrder 2) [0, 1] :=
  kendallTau_triangle [0, 1] [1, 0] [0, 1]

/-- `candidateSubstitutes` body unfold: erase `s_hat` from `Finset.univ`,
    `toList`, then `mergeSort` ascending by `cs.exceed s_hat`. -/
example {chi : Type} (cs : Constellation chi) (s_hat : chi) :
    candidateSubstitutes cs s_hat
      = @List.mergeSort chi
          (let _ : DecidableEq chi := cs.decEq
           let _ : Fintype chi := cs.fintype
           ((Finset.univ : Finset chi).erase s_hat).toList)
          (fun s1 s2 =>
            @decide (cs.exceed s_hat s1 ≤ cs.exceed s_hat s2)
              (Classical.propDecidable _)) :=
  candidateSubstitutes_eq cs s_hat

/-- `ar2LeastSquaresFit` body unfold: `((Z^H Z)^{-1} Z^H y)` for `Z = regressorMatrix4x2 z`
    and `y = regressorTarget4 z`, projected onto the two components. -/
example (z : Fin 6 -> Complex) :
    ar2LeastSquaresFit z =
      let Z : Matrix (Fin 4) (Fin 2) Complex := regressorMatrix4x2 z
      let y : Fin 4 -> Complex := regressorTarget4 z
      let ZH := Z.conjTranspose
      let ZHZ : Matrix (Fin 2) (Fin 2) Complex := ZH * Z
      let ZHy : Fin 2 -> Complex := ZH.mulVec y
      let solution : Fin 2 -> Complex := ZHZ⁻¹.mulVec ZHy
      (solution 0, solution 1) :=
  ar2LeastSquaresFit_eq z

/-- `0 ≤ bler ≤ 1` sandwich packaged: the new probability layer's BLER
    always lies in the unit interval, irrespective of decoder choice. -/
example {n_s : Nat} (sigma : NoisePower)
    (decode : Section00.RealSymbolVector n_s -> Bool) :
    0 ≤ Section00.bler sigma decode ∧ Section00.bler sigma decode ≤ 1 :=
  ⟨Section00.bler_nonneg sigma decode, Section00.bler_le_one sigma decode⟩

/-- Concrete `kendallTau` eval on `Fin 1`: the only list `[0]` is its own
    reflexive zero-distance instance. -/
example : kendallTau ([0] : QueryOrder 1) [0] = 0 := rfl

/-- Concrete `kendallTau` eval on `Fin 2`: `[0, 1]` vs `[1, 0]` disagree on
    the single available pair `(0, 1)`, giving distance `1`. -/
example : kendallTau ([0, 1] : QueryOrder 2) [1, 0] = 1 := rfl

/-- Concrete `kendallTau` eval on `Fin 3`: `[0, 1, 2]` is its own reflexive
    zero-distance instance. -/
example : kendallTau ([0, 1, 2] : QueryOrder 3) [0, 1, 2] = 0 := rfl

/-- Concrete `kendallTau` eval on `Fin 3`: reversed-order distance equals the
    number of `i.val < j.val` pairs (which is `3.choose 2 = 3`). -/
example : kendallTau ([0, 1, 2] : QueryOrder 3) [2, 1, 0] = 3 := rfl

/-- Concrete `kendallTau` eval on `Fin 3`: a single adjacent transposition
    flips one pair, giving distance `1`. -/
example : kendallTau ([0, 1, 2] : QueryOrder 3) [1, 0, 2] = 1 := rfl

/-- *`kendallTau` on the empty domain.*  At `numPatterns = 0` the only
    `QueryOrder 0` is `[]`, so the distance is `0` for any input pair. -/
example (a b : QueryOrder 0) : kendallTau a b = 0 :=
  kendallTau_empty a b

/-- Concrete kendallTau eval on Fin 4: identical lists have distance 0. -/
example : kendallTau ([0, 1, 2, 3] : QueryOrder 4) [0, 1, 2, 3] = 0 := rfl

/-- Concrete kendallTau eval on Fin 4: reversal achieves the maximum
    distance equal to `4.choose 2 = 6`. -/
example : kendallTau ([0, 1, 2, 3] : QueryOrder 4) [3, 2, 1, 0] = 6 := rfl

/-- Concrete kendallTau eval on Fin 3: swapping the last two flips one pair. -/
example : kendallTau ([0, 1, 2] : QueryOrder 3) [0, 2, 1] = 1 := rfl

/-- Concrete `QueryOrder.positionOf` eval: position of `2` in `[0, 1, 2]` is `2`. -/
example : QueryOrder.positionOf (2 : Fin 3) [0, 1, 2] = 2 := rfl

/-- Concrete `QueryOrder.positionOf` eval: missing element returns the
    fall-through-on-miss convention (here `2`, matching the list length). -/
example : QueryOrder.positionOf (2 : Fin 3) [0, 1] = 2 := rfl

/-- Concrete `bpsk.exceed_zero_iff` instance at the matching pair `(false, false)`. -/
example : (bpsk.exceed false false = 0) ↔ (false = false) :=
  bpsk.exceed_zero_iff false false

/-- Concrete kendallTau eval on Fin 5: identical lists have distance 0. -/
example : kendallTau ([0, 1, 2, 3, 4] : QueryOrder 5) [0, 1, 2, 3, 4] = 0 := rfl

/-- Concrete kendallTau eval on Fin 5: reversal achieves the maximum
    distance equal to `5.choose 2 = 10`. -/
example : kendallTau ([0, 1, 2, 3, 4] : QueryOrder 5) [4, 3, 2, 1, 0] = 10 := rfl

/-- Concrete `QueryOrder.positionOf` eval: last-element hit returns the trailing index. -/
example : QueryOrder.positionOf (3 : Fin 4) [0, 1, 2, 3] = 3 := rfl

/-- The Section 00 `noiseMeasure` is a Gaussian measure (instance-fired). -/
example (n_s : Nat) (sigma : NoisePower) :
    ProbabilityTheory.IsGaussian (Section00.noiseMeasure n_s sigma) :=
  Section00.noiseMeasure_isGaussian n_s sigma

/-- `noiseMeasure` is a probability measure (chained through `IsGaussian` instance
    via `inferInstance`). -/
example (n_s : Nat) (sigma : NoisePower) :
    MeasureTheory.IsProbabilityMeasure (Section00.noiseMeasure n_s sigma) :=
  inferInstance

/-- Concrete `kendallTau` eval on Fin 3: a cyclic shift `[1, 2, 0]` vs `[0, 1, 2]`
    disagrees on 2 pairs. -/
example : kendallTau ([0, 1, 2] : QueryOrder 3) [1, 2, 0] = 2 := rfl

/-- Full `kendallTau`-as-metric witness: reflexive, symmetric, triangle inequality. -/
example {numPatterns : Nat} (a b c : QueryOrder numPatterns) :
    kendallTau a a = 0 ∧ kendallTau a b = kendallTau b a
      ∧ kendallTau a c ≤ kendallTau a b + kendallTau b c :=
  ⟨kendallTau_self a, kendallTau_symm a b, kendallTau_triangle a b c⟩

/-- Concrete `kendallTau` eval on Fin 4: swapping the middle pair `[0, 2, 1, 3]`
    vs `[0, 1, 2, 3]` flips a single pair, distance = 1. -/
example : kendallTau ([0, 1, 2, 3] : QueryOrder 4) [0, 2, 1, 3] = 1 := rfl

/-- Concrete `kendallTau` eval on Fin 4: two non-overlapping adjacent
    transpositions `[1, 0, 3, 2]` vs `[0, 1, 2, 3]` flip exactly 2 pairs. -/
example : kendallTau ([0, 1, 2, 3] : QueryOrder 4) [1, 0, 3, 2] = 2 := rfl

/-- Concrete `kendallTau` eval on Fin 4: cyclic shift `[1, 2, 3, 0]` flips
    exactly 3 pairs (each pair involving the wrapped-around 0). -/
example : kendallTau ([0, 1, 2, 3] : QueryOrder 4) [1, 2, 3, 0] = 3 := rfl

/-- `QueryOrder.positionOf` at head-miss / second-element-hit on a two-element list. -/
example : QueryOrder.positionOf (1 : Fin 2) [0, 1] = 1 := rfl

/-- `noiseMeasure` satisfies the weaker `IsZeroOrProbabilityMeasure` typeclass
    (via the priority-100 `IsProbabilityMeasure -> IsZeroOrProbabilityMeasure`
    instance), which is what `bler_le_one` consumes through
    `MeasureTheory.measureReal_le_one`. -/
example (n_s : Nat) (sigma : NoisePower) :
    MeasureTheory.IsZeroOrProbabilityMeasure (Section00.noiseMeasure n_s sigma) :=
  inferInstance

/-- `noiseMeasure` is a finite measure (via the
    `IsZeroOrProbabilityMeasure -> IsFiniteMeasure` priority-100 instance). -/
example (n_s : Nat) (sigma : NoisePower) :
    MeasureTheory.IsFiniteMeasure (Section00.noiseMeasure n_s sigma) :=
  inferInstance

/-- `noiseMeasure` has total mass `1` (it is a probability measure). -/
example (n_s : Nat) (sigma : NoisePower) :
    Section00.noiseMeasure n_s sigma Set.univ = 1 :=
  MeasureTheory.measure_univ

/-- Concrete kendallTau eval on Fin 6: identical lists have distance 0. -/
example : kendallTau ([0, 1, 2, 3, 4, 5] : QueryOrder 6) [0, 1, 2, 3, 4, 5] = 0 := rfl

/-- Concrete kendallTau eval on Fin 6: reversal achieves the maximum
    distance equal to `6.choose 2 = 15`. -/
example : kendallTau ([0, 1, 2, 3, 4, 5] : QueryOrder 6) [5, 4, 3, 2, 1, 0] = 15 := rfl

/-- Concrete `QueryOrder.positionOf` eval on Fin 5: hit at index 2. -/
example : QueryOrder.positionOf (2 : Fin 5) [0, 1, 2, 3, 4] = 2 := rfl

/-- Concrete `kendallTau_le_sq` at Fin 4: any pair has distance ≤ `4 * 4 = 16`. -/
example (a b : QueryOrder 4) : kendallTau a b ≤ 16 :=
  kendallTau_le_sq a b

/-- Concrete triangle inequality on Fin 4: the reflexivity sandwich
    `kendallTau a a ≤ kendallTau a b + kendallTau b a` instantiated at
    the reversal pair. -/
example :
    kendallTau ([0, 1, 2, 3] : QueryOrder 4) [0, 1, 2, 3]
      ≤ kendallTau ([0, 1, 2, 3] : QueryOrder 4) [3, 2, 1, 0]
        + kendallTau ([3, 2, 1, 0] : QueryOrder 4) [0, 1, 2, 3] :=
  kendallTau_triangle [0, 1, 2, 3] [3, 2, 1, 0] [0, 1, 2, 3]

/-- `RFViewTaps.tap3` anonymous-constructor projection (interior field). -/
example (t1 t2 t3 t4 t5 t6 : Complex) :
    ({ tap1 := t1, tap2 := t2, tap3 := t3,
       tap4 := t4, tap5 := t5, tap6 := t6 } : RFViewTaps).tap3 = t3 := rfl

/-- `QueryOrder.positionOf` at the head returns 0 (immediate equality match). -/
example : QueryOrder.positionOf (0 : Fin 3) [0, 1, 2] = 0 := rfl

/-- Concrete `kendallTau_le_sq` at Fin 5: any pair has distance ≤ 25. -/
example (a b : QueryOrder 5) : kendallTau a b ≤ 25 :=
  kendallTau_le_sq a b

/-- Concrete `kendallTau_le_sq` at Fin 6: any pair has distance ≤ 36. -/
example (a b : QueryOrder 6) : kendallTau a b ≤ 36 :=
  kendallTau_le_sq a b

/-- `RFViewTaps.tap2` anonymous projection through the explicit constructor. -/
example (t1 t2 t3 t4 t5 t6 : Complex) :
    ({ tap1 := t1, tap2 := t2, tap3 := t3,
       tap4 := t4, tap5 := t5, tap6 := t6 } : RFViewTaps).tap2 = t2 := rfl

/-- `RFViewTaps.tap4` anonymous projection through the explicit constructor. -/
example (t1 t2 t3 t4 t5 t6 : Complex) :
    ({ tap1 := t1, tap2 := t2, tap3 := t3,
       tap4 := t4, tap5 := t5, tap6 := t6 } : RFViewTaps).tap4 = t4 := rfl

/-- `RFViewTaps.tap5` anonymous projection through the explicit constructor. -/
example (t1 t2 t3 t4 t5 t6 : Complex) :
    ({ tap1 := t1, tap2 := t2, tap3 := t3,
       tap4 := t4, tap5 := t5, tap6 := t6 } : RFViewTaps).tap5 = t5 := rfl

/-- Concrete `kendallTau_summand_le_one` instance at Fin 2 with `(i, j) = (0, 1)`. -/
example (a b : QueryOrder 2) :
    (if (0 : Fin 2).val < (1 : Fin 2).val then
        let ai := QueryOrder.positionOf (0 : Fin 2) a
        let aj := QueryOrder.positionOf (1 : Fin 2) a
        let bi := QueryOrder.positionOf (0 : Fin 2) b
        let bj := QueryOrder.positionOf (1 : Fin 2) b
        if decide (ai < aj) = decide (bi < bj) then (0 : Nat) else 1
      else 0) ≤ 1 :=
  kendallTau_summand_le_one a b 0 1

/-- Concrete kendallTau eval on Fin 7: identical lists have distance 0. -/
example : kendallTau ([0, 1, 2, 3, 4, 5, 6] : QueryOrder 7) [0, 1, 2, 3, 4, 5, 6] = 0 := rfl

/-- Concrete `QueryOrder.positionOf` eval at the middle index on Fin 4. -/
example : QueryOrder.positionOf (2 : Fin 4) [0, 1, 2, 3] = 2 := rfl

/-- Concrete `QueryOrder.positionOf` eval at the second index on Fin 4. -/
example : QueryOrder.positionOf (1 : Fin 4) [0, 1, 2, 3] = 1 := rfl

/-- Concrete `kendallTau_le_sq` at Fin 1: any pair has distance ≤ `1 * 1 = 1`. -/
example (a b : QueryOrder 1) : kendallTau a b ≤ 1 :=
  kendallTau_le_sq a b

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

/-- Every length-`(n + 1)` pattern is the `landslideExtend` of its top-bit + restriction. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    landslideExtend (e (Fin.last n)) (e ∘ Fin.castSucc) = e :=
  landslideExtend_split e

/-- `landslideExtend` is a right inverse for `landslideExtend_inv`. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    landslideExtend (landslideExtend_inv e).1 (landslideExtend_inv e).2 = e :=
  landslideExtend_landslideExtend_inv e

/-- The inverse `landslideExtend_inv` is a left inverse. -/
example {n : Nat} (b : Bool) (e : Fin n -> Bool) :
    landslideExtend_inv (landslideExtend b e) = (b, e) :=
  landslideExtend_inv_landslideExtend b e

/-- `landslideExtend_inv` definitional unfold: tuple of top bit and restriction.
    Roundtrip theorems alone would tolerate a component swap; this catches it. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    landslideExtend_inv e = (e (Fin.last n), e ∘ Fin.castSucc) := rfl

/-- Codeword `+`-form equality characterisation. -/
example {n : Nat} (a b : Codeword n) : a + b = 0 <-> a = b :=
  Codeword.add_eq_zero_iff a b

/-- Codeword XOR is identity iff right arg is zero. -/
example {n : Nat} (a b : Codeword n) : Codeword.xor a b = a <-> b = 0 :=
  Codeword.xor_eq_self_iff a b

/-- Trivial constellation symbols are all equal (Subsingleton Unit). -/
example (s s_hat : Unit) : s = s_hat :=
  trivialConstellation_all_eq s s_hat

/-- Trivial constellation exceedance is zero. -/
example (s s_hat : Unit) : trivialConstellation.exceed s s_hat = 0 :=
  trivialConstellation_exceed s s_hat

/-- Restriction never increases bit-weight. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    bitWeight (e ∘ Fin.castSucc) ≤ bitWeight e :=
  bitWeight_castSucc_le e

/-- `landslideExtend true ∘ (·∘ castSucc) = id` iff top bit was already `true`. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    landslideExtend true (e ∘ Fin.castSucc) = e
      <-> e (Fin.last n) = true :=
  landslideExtend_true_castSucc_eq_iff_last_true e

/-- `landslideExtend false ∘ (·∘ castSucc) = id` iff top bit was already `false`. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    landslideExtend false (e ∘ Fin.castSucc) = e
      <-> e (Fin.last n) = false :=
  landslideExtend_false_castSucc_eq_iff_last_false e

/-- Restrict-then-extend by `true`: bit-weight equals original plus complementary cost. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    bitWeight (landslideExtend true (e ∘ Fin.castSucc))
      = bitWeight e + (if e (Fin.last n) then 0 else n + 1) :=
  landslideExtend_true_castSucc_bitWeight e

/-- Restrict-then-extend by `false`: bit-weight equals original minus top-bit cost. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    bitWeight (landslideExtend false (e ∘ Fin.castSucc))
      = bitWeight e - (if e (Fin.last n) then n + 1 else 0) :=
  landslideExtend_false_castSucc_bitWeight e

/-- Restriction strictly decreases bit-weight iff the top bit was true (iff lift). -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    bitWeight (e ∘ Fin.castSucc) < bitWeight e
      <-> e (Fin.last n) = true :=
  bitWeight_castSucc_lt_iff_last_true e

/-- Restriction strict-decreases when top bit was true. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) (h : e (Fin.last n) = true) :
    bitWeight (e ∘ Fin.castSucc) < bitWeight e :=
  bitWeight_castSucc_lt_of_last_true e h

/-- `landslideExtend false` of all-false is all-false (at length `n + 1`). -/
example {n : Nat} :
    landslideExtend false (fun _ : Fin n => false)
      = (fun _ : Fin (n + 1) => false) :=
  landslideExtend_false_const_false

/-- `landslideExtend true` of all-true is all-true (at length `n + 1`). -/
example {n : Nat} :
    landslideExtend true (fun _ : Fin n => true)
      = (fun _ : Fin (n + 1) => true) :=
  landslideExtend_true_const_true

/-- Every length-`(n + 1)` pattern decomposes as an extension. -/
example {n : Nat} (e : Fin (n + 1) -> Bool) :
    ∃ b : Bool, ∃ e' : Fin n -> Bool, e = landslideExtend b e' :=
  landslideExtend_exists e

/-- `entropyRate1` at `n_s = b.toNat` coincides with the block form. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (b : BlockSize) :
    entropyRate1 sigma rho b.toNat = entropyRate1_block sigma rho b :=
  entropyRate1_eq_block sigma rho b

/-- Second-order entropy rate closed-form unfolding. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient) (n_s : Nat) :
    entropyRate2 sigma rho1 rho2 n_s
      = (1 / 2 : Real)
          * Real.log (2 * Real.pi * Real.exp 1 * sigma.val)
        + (1 / (2 * (n_s : Real)))
            * Real.log
                (- (rho2.val - 1) ^ (n_s - 2)
                    * (1 - 2 * rho1.val ^ 2 + rho2.val) ^ (n_s - 2)
                  / (rho1.val ^ 2 - 1) ^ (n_s - 3)) :=
  entropyRate2_eq sigma rho1 rho2 n_s

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

/-- RFView matrix general sub-diagonal via tap lookup: any offset `d`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (d : Nat) (h : i.val = j.val + d) :
    rfViewMatrix n_s rowTaps i j
      = ((rowTaps i).tap? (d + 1)).getD (0 : Complex) :=
  rfViewMatrix_at_subdiag_via_tap rowTaps i j d h

/-- RFView matrix lower-triangular branch: getD-extracted tap. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (h : j.val ≤ i.val) :
    rfViewMatrix n_s rowTaps i j
      = ((rowTaps i).tap? (i.val - j.val + 1)).getD (0 : Complex) :=
  rfViewMatrix_apply_le rowTaps i j h

/-- Dicode matrix diagonal entry is `1`. -/
example {n_s : Nat} (rho : CorrelationCoefficient) (i : Fin n_s) :
    dicodeMatrix n_s rho i i = (1 : Complex) :=
  dicodeMatrix_diag rho i

/-- Dicode matrix sub-diagonal entry is `-rho`. -/
example {n_s : Nat} (rho : CorrelationCoefficient) (i j : Fin n_s)
    (h : i.val = j.val + 1) :
    dicodeMatrix n_s rho i j = -(rho.val : Complex) :=
  dicodeMatrix_subdiag rho i j h

/-- Dicode matrix off-diagonal/off-sub-diagonal entry is `0`. -/
example {n_s : Nat} (rho : CorrelationCoefficient) (i j : Fin n_s)
    (h1 : i.val ≠ j.val) (h2 : i.val ≠ j.val + 1) :
    dicodeMatrix n_s rho i j = (0 : Complex) :=
  dicodeMatrix_off rho i j h1 h2

/-- RFView matrix first sub-diagonal entry is `tap2`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (h : i.val = j.val + 1) :
    rfViewMatrix n_s rowTaps i j = (rowTaps i).tap2 :=
  rfViewMatrix_first_subdiag rowTaps i j h

/-- RFView matrix second sub-diagonal entry is `tap3`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (h : i.val = j.val + 2) :
    rfViewMatrix n_s rowTaps i j = (rowTaps i).tap3 :=
  rfViewMatrix_second_subdiag rowTaps i j h

/-- RFView matrix third sub-diagonal entry is `tap4`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (h : i.val = j.val + 3) :
    rfViewMatrix n_s rowTaps i j = (rowTaps i).tap4 :=
  rfViewMatrix_third_subdiag rowTaps i j h

/-- RFView matrix fourth sub-diagonal entry is `tap5`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (h : i.val = j.val + 4) :
    rfViewMatrix n_s rowTaps i j = (rowTaps i).tap5 :=
  rfViewMatrix_fourth_subdiag rowTaps i j h

/-- RFView matrix fifth sub-diagonal entry is `tap6`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (h : i.val = j.val + 5) :
    rfViewMatrix n_s rowTaps i j = (rowTaps i).tap6 :=
  rfViewMatrix_fifth_subdiag rowTaps i j h

/-- RFView matrix diagonal entry equals tap1. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i : Fin n_s) :
    rfViewMatrix n_s rowTaps i i = (rowTaps i).tap1 :=
  rfViewMatrix_diag rowTaps i

/-- DelayTap matrix entry above diagonal is zero. -/
example {n_s : Nat} {p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i j : Fin n_s) (hij : i.val < j.val) :
    delayTapMatrix n_s paths f_s i j = (0 : Complex) :=
  delayTapMatrix_zero_above_diag paths f_s i j hij

/-- `rfViewMatrix` is strictly lower-triangular (direct entry-level form). -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (hij : i.val < j.val) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  rfViewMatrix_is_lower_triangular rowTaps i j hij

/-- `rfViewMatrix` outside-band (disjunctive): `i < j ∨ j + 6 ≤ i → entry = 0`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (h : i.val < j.val ∨ j.val + 6 <= i.val) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  rfViewMatrix_outside_band rowTaps i j h

/-- `rfViewMatrix` below-6-band (combined): `j + 6 ≤ i → entry = 0`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (h : j.val + 6 ≤ i.val) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  rfViewMatrix_below_6band rowTaps i j h

/-- `rfViewMatrix` out-of-band (strict): `j + 6 < i → entry = 0`. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i j : Fin n_s)
    (hij : j.val + 6 < i.val) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  rfViewMatrix_out_of_band rowTaps i j hij

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

/-- Strict logistic-weight bound: any rank-position false bit gives `<` max. -/
example {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool)
    (h : ∃ i, e (pi.perm i) = false) :
    logisticWeight pi e
      < logisticWeight pi (fun _ : Fin n => true) :=
  logisticWeight_lt_const_true_of_exists_false_at_perm pi e h

/-- Logistic weight equals the max iff every rank-permuted bit is true. -/
example {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    logisticWeight pi e = logisticWeight pi (fun _ : Fin n => true)
      <-> forall i, e (pi.perm i) = true :=
  logisticWeight_eq_const_true_iff_all_true pi e

/-- Logistic-weight strict ordering iff bit-weight strict ordering. -/
example {n : Nat} (pi : ReliabilityRank n) (e1 e2 : Fin n -> Bool) :
    logisticWeight pi e1 < logisticWeight pi e2
      <-> bitWeight (e1 ∘ pi.perm) < bitWeight (e2 ∘ pi.perm) :=
  logisticWeight_lt_iff pi e1 e2

/-- Logistic-weight ordering iff bit-weight ordering under the rank permutation. -/
example {n : Nat} (pi : ReliabilityRank n) (e1 e2 : Fin n -> Bool) :
    logisticWeight pi e1 <= logisticWeight pi e2
      <-> bitWeight (e1 ∘ pi.perm) <= bitWeight (e2 ∘ pi.perm) :=
  logisticWeight_le_iff pi e1 e2

/-- Logistic-weight equality iff bit-weight equality under the rank permutation. -/
example {n : Nat} (pi : ReliabilityRank n) (e1 e2 : Fin n -> Bool) :
    logisticWeight pi e1 = logisticWeight pi e2
      <-> bitWeight (e1 ∘ pi.perm) = bitWeight (e2 ∘ pi.perm) :=
  logisticWeight_eq_iff pi e1 e2

/-- Logistic weight is zero iff every bit at every rank position is false. -/
example {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    logisticWeight pi e = 0 <-> forall i, e (pi.perm i) = false :=
  logisticWeight_zero_iff_all_false_at_perm pi e

/-- Logistic weight equals bit-weight of the rank-permuted pattern. -/
example {n : Nat} (pi : ReliabilityRank n) (e : Fin n -> Bool) :
    logisticWeight pi e = bitWeight (e ∘ pi.perm) :=
  logisticWeight_eq_bitWeight_comp pi e

/-- 2x2 Gauss-Markov covariance: `(0, 0)` entry equals `sigma`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho) 0 0 = (sigma.val : Complex) :=
  gaussMarkovCov_two_00 sigma rho

/-- 2x2 Gauss-Markov covariance: `(1, 1)` entry equals `sigma`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho) 1 1 = (sigma.val : Complex) :=
  gaussMarkovCov_two_11 sigma rho

/-- 2x2 Gauss-Markov covariance: `(0, 1)` entry equals `sigma * rho`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho) 0 1
      = (sigma.val : Complex) * (rho.val : Complex) :=
  gaussMarkovCov_two_01 sigma rho

/-- 2x2 Gauss-Markov covariance: `(1, 0)` entry equals `sigma * rho`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    (gaussMarkovCov 2 sigma rho) 1 0
      = (sigma.val : Complex) * (rho.val : Complex) :=
  gaussMarkovCov_two_10 sigma rho

/-- Gauss-Markov covariance vanishes at zero noise power. -/
example {n_s : Nat} (rho : CorrelationCoefficient) (i j : Fin n_s) :
    (gaussMarkovCov n_s ⟨0, le_refl 0⟩ rho) i j = 0 :=
  gaussMarkovCov_zero_sigma rho i j

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

/-- `rfView.noiseCov` is the full white-noise lambda. -/
example (n_s : Nat) (rowTaps : Fin n_s -> RFViewTaps) (sigma : NoisePower) :
    (rfView n_s rowTaps sigma).noiseCov
      = fun i j =>
          if i.val = j.val then (sigma.val : Complex) else (0 : Complex) :=
  rfView_noiseCov n_s rowTaps sigma

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

/-- `landslideExtend b e` at the new top position returns the inserted bit. -/
example {n : Nat} (b : Bool) (e : Fin n -> Bool) :
    landslideExtend b e (Fin.last n) = b :=
  landslideExtend_last b e

/-- `landslideExtend b e` at a `castSucc` position returns the original bit. -/
example {n : Nat} (b : Bool) (e : Fin n -> Bool) (i : Fin n) :
    landslideExtend b e i.castSucc = e i :=
  landslideExtend_castSucc b e i

/-- `bitWeight` split when the top bit is `false`: same weight as restriction. -/
example {n : Nat} (e : Fin (n + 1) -> Bool)
    (h : e (Fin.last n) = false) :
    bitWeight e = bitWeight (e ∘ Fin.castSucc) :=
  bitWeight_split_false e h

/-- `bitWeight` split when the top bit is `true`: restriction's weight + `(n + 1)`. -/
example {n : Nat} (e : Fin (n + 1) -> Bool)
    (h : e (Fin.last n) = true) :
    bitWeight e = bitWeight (e ∘ Fin.castSucc) + (n + 1) :=
  bitWeight_split_true e h

/-- Extending by `false` leaves the bit-weight unchanged. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight (landslideExtend false e) = bitWeight e :=
  bitWeight_extend_false e

/-- Extending by `true` adds `n + 1` to the bit-weight. -/
example {n : Nat} (e : Fin n -> Bool) :
    bitWeight (landslideExtend true e) = bitWeight e + (n + 1) :=
  bitWeight_extend_true e

/-- `landslide 1 1` has length 1. -/
example : (landslide 1 1).length = 1 := landslide_one_one_length

/-- `landslide 0 0` has length 1 (just the empty pattern). -/
example : (landslide 0 0).length = 1 := landslide_zero_zero_length

/-- `landslide 0 (w + 1)` is empty for all w. -/
example (w : Nat) : (landslide 0 (w + 1)).length = 0 :=
  landslide_zero_succ_length w

/-- `landslide 1 0` is the singleton all-false pattern. -/
example : landslide 1 0 = [landslideExtend false Fin.elim0] :=
  landslide_one_zero

/-- `landslide 1 1` is the singleton bit-0-set pattern. -/
example : landslide 1 1 = [landslideExtend true Fin.elim0] :=
  landslide_one_one

/-- `landslide 2 1` is a singleton: bit 0 set, bit 1 unset. -/
example : landslide 2 1
      = [landslideExtend false (landslideExtend true Fin.elim0)] :=
  landslide_two_one

/-- `landslide 2 2` is a singleton: bit 0 unset, bit 1 set. -/
example : landslide 2 2
      = [landslideExtend true (landslideExtend false Fin.elim0)] :=
  landslide_two_two

/-- `landslide 2 0` is the singleton all-false (twice-extended) pattern. -/
example :
    landslide 2 0
      = [landslideExtend false (landslideExtend false Fin.elim0)] :=
  landslide_two_zero

/-- At length 2, the bucket for weight 4 is empty. -/
example : landslide 2 4 = [] :=
  landslide_two_four_eq_nil

/-- At length 1, the bucket for weight 2 is empty. -/
example : landslide 1 2 = [] :=
  landslide_one_two_eq_nil

/-- All-true at length 3 has bit-weight 6. -/
example : bitWeight (fun _ : Fin 3 => true) = 6 :=
  bitWeight_three_true

/-- All-true at length 2 has bit-weight 3. -/
example : bitWeight (fun _ : Fin 2 => true) = 3 :=
  bitWeight_two_true

/-- All-true at length 1 has bit-weight 1. -/
example : bitWeight (fun _ : Fin 1 => true) = 1 :=
  bitWeight_one_true

/-- Bit-weight of the unique length-0 pattern is zero. -/
example (e : Fin 0 -> Bool) : bitWeight e = 0 :=
  bitWeight_fin_zero e

/-- AR(2) with zero initial conditions stays zero forever. -/
example (phi1 phi2 : Complex) (n : Nat) :
    ar2 phi1 phi2 0 0 n = 0 :=
  ar2_const_zero phi1 phi2 n

/-- AR(2) with both coefficients zero: recurrence vanishes from index 2. -/
example (z1 z2 : Complex) (n : Nat) : ar2 0 0 z1 z2 (n + 2) = 0 :=
  ar2_phi_zero z1 z2 n

/-- AR(2) with `phi_1 = phi_2 = 1` is the Fibonacci recurrence. -/
example (z1 z2 : Complex) (n : Nat) :
    ar2 1 1 z1 z2 (n + 2)
      = ar2 1 1 z1 z2 (n + 1) + ar2 1 1 z1 z2 n :=
  ar2_phi1_one_phi2_one_succ z1 z2 n

/-- `ar2 1 1 z1 z2 4` pre-`one_mul` pattern-match unfolding: four levels of
    `n + 2` reduction.  Locks the raw shape that the algebraic-collapse lemma
    `ar2_phi1_one_phi2_one_succ` (using `one_mul`) cannot capture by `rfl`. -/
example (z1 z2 : Complex) :
    ar2 1 1 z1 z2 4
      = 1 * (1 * (1 * z2 + 1 * z1) + 1 * z2)
        + 1 * (1 * z2 + 1 * z1) := rfl

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

/-- Codeword self-XOR is zero: `a xor a = 0`. -/
example {n : Nat} (a : Codeword n) : Codeword.xor a a = 0 :=
  Codeword.xor_self a

/-- Codeword equation via XOR-zero: `a = b ↔ a xor b = 0`. -/
example {n : Nat} (a b : Codeword n) :
    a = b <-> Codeword.xor a b = 0 :=
  Codeword.eq_iff_xor_eq_zero a b

/-- From `a xor b = 0` deduce `a = b`. -/
example {n : Nat} {a b : Codeword n}
    (h : Codeword.xor a b = 0) : a = b :=
  Codeword.eq_of_xor_eq_zero h

/-- From `a = b` deduce `a xor b = 0`. -/
example {n : Nat} {a b : Codeword n} (h : a = b) :
    Codeword.xor a b = 0 :=
  Codeword.xor_eq_zero_of_eq h

/-- Codeword left-cancellation iff: `a xor b = a xor c ↔ b = c`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor a b = Codeword.xor a c <-> b = c :=
  Codeword.xor_left_eq_iff a b c

/-- Codeword right-cancellation iff: `a xor c = b xor c ↔ a = b`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor a c = Codeword.xor b c <-> a = b :=
  Codeword.xor_right_eq_iff a b c

/-- Codeword subtraction equals XOR: `a - b = a xor b`. -/
example {n : Nat} (a b : Codeword n) :
    a - b = Codeword.xor a b :=
  Codeword.sub_eq_xor a b

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

/-- Perturbed channel is identity when `epsilon i j = 0` (pointwise). -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i j : Fin n_s} (h_eps : epsilon i j = 0) :
    perturbChannel h epsilon i j = h i j :=
  perturbChannel_eps_zero_apply h epsilon h_eps

/-- Perturbed channel vanishes when `epsilon i j = -1` (pure cancellation). -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i j : Fin n_s} (h_eps : epsilon i j = -1) :
    perturbChannel h epsilon i j = 0 :=
  perturbChannel_neg_one_attenuation_eq_zero h epsilon h_eps

/-- Perturbed channel entry is zero iff the underlying entry is zero
    or the `1 + epsilon` factor cancels. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    (i j : Fin n_s) :
    perturbChannel h epsilon i j = 0
      <-> h i j = 0 ∨ 1 + epsilon i j = 0 :=
  perturbChannel_eq_zero_iff h epsilon i j

/-- Syndrome-zero is exactly the codeword condition on `Y xor N` (no preconditions). -/
example {n k : Nat} (H : ParityCheck n k) (Y N : Codeword n) :
    syndromeZero H Y N <->
      forall (i : Fin (n - k)),
        H.matrix.mulVec (Codeword.xor Y N) i = 0 :=
  syndromeZero_iff_xor_codeword H Y N

/-- Syndrome-zero equivalence under a codeword noise candidate. -/
example {n k : Nat} (H : ParityCheck n k) (Y N_g : Codeword n)
    (h : forall i, H.matrix.mulVec N_g i = 0) :
    syndromeZero H Y N_g <->
      forall (i : Fin (n - k)), H.matrix.mulVec Y i = 0 :=
  syndromeZero_iff_received_codeword H Y N_g h

/-- `syndromeZero` is invariant under simultaneous codeword shifts. -/
example {n k : Nat} (H : ParityCheck n k) (Y N c_r c_n : Codeword n)
    (h_cr : forall (i : Fin (n - k)), H.matrix.mulVec c_r i = 0)
    (h_cn : forall (i : Fin (n - k)), H.matrix.mulVec c_n i = 0) :
    syndromeZero H (Codeword.xor Y c_r) (Codeword.xor N c_n)
      <-> syndromeZero H Y N :=
  syndromeZero_xor_codeword_both_iff H Y N c_r c_n h_cr h_cn

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

/-- Pointwise XOR linearity: `H * (a xor b) i = H * a i + H * b i`. -/
example {n k : Nat} (H : ParityCheck n k) (a b : Codeword n)
    (i : Fin (n - k)) :
    H.matrix.mulVec (Codeword.xor a b) i
      = H.matrix.mulVec a i + H.matrix.mulVec b i :=
  Codeword.mulVec_xor_apply H a b i

/-- Parity-check map is XOR-linear: `H * (a xor b) = H * a + H * b`. -/
example {n k : Nat} (H : ParityCheck n k) (a b : Codeword n) :
    H.matrix.mulVec (Codeword.xor a b)
      = H.matrix.mulVec a + H.matrix.mulVec b :=
  Codeword.mulVec_xor H a b

/-- Double-cancellation: `(a xor b) xor c = (a xor d) xor c ↔ b = d`. -/
example {n : Nat} (a b c d : Codeword n) :
    Codeword.xor (Codeword.xor a b) c = Codeword.xor (Codeword.xor a d) c
      <-> b = d :=
  Codeword.xor_xor_eq_xor_xor_iff a b c d

/-- Pairwise XOR equality rearrangement: `a xor b = c xor d ↔ a xor c = b xor d`. -/
example {n : Nat} (a b c d : Codeword n) :
    (Codeword.xor a b = Codeword.xor c d)
      <-> (Codeword.xor a c = Codeword.xor b d) :=
  Codeword.xor_eq_xor_iff_xor_eq_xor a b c d

/-- Pointwise left self-XOR cancellation: `((a xor a) xor b) i = b i`. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a a) b i = b i :=
  Codeword.xor_self_left_eq_apply a b i

/-- Pointwise right self-XOR cancellation: `(a xor (b xor b)) i = a i`. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a (Codeword.xor b b) i = a i :=
  Codeword.xor_self_right_eq_apply a b i

/-- Codeword left self-XOR cancellation: `(a xor a) xor b = b`. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor (Codeword.xor a a) b = b :=
  Codeword.xor_self_left_eq a b

/-- Codeword right self-XOR cancellation: `a xor (b xor b) = a`. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor a (Codeword.xor b b) = a :=
  Codeword.xor_self_right_eq a b

/-- Codeword XOR common-suffix cancellation: `(a xor b) xor (c xor b) = a xor c`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor c b)
      = Codeword.xor a c :=
  Codeword.xor_xor_xor_self_right a b c

/-- Pointwise common-suffix cancellation: `((a xor b) xor (c xor b)) i = (a xor c) i`. -/
example {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor c b) i
      = Codeword.xor a c i :=
  Codeword.xor_xor_xor_self_right_apply a b c i

/-- Pointwise common-prefix cancellation: `((a xor b) xor (a xor c)) i = (b xor c) i`. -/
example {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor a c) i
      = Codeword.xor b c i :=
  Codeword.xor_xor_xor_self_apply a b c i

/-- Codeword XOR common-prefix cancellation: `(a xor b) xor (a xor c) = b xor c`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor a c)
      = Codeword.xor b c :=
  Codeword.xor_xor_xor_self a b c

/-- Pointwise self-XOR vanishes: `(a xor a) i = 0`. -/
example {n : Nat} (a : Codeword n) (i : Fin n) :
    Codeword.xor a a i = 0 :=
  Codeword.xor_self_apply a i

/-- Pointwise XOR with zero on the left: `(0 xor a) i = a i`. -/
example {n : Nat} (a : Codeword n) (i : Fin n) :
    Codeword.xor 0 a i = a i :=
  Codeword.zero_xor_apply a i

/-- Codeword XOR equals add pointwise: `(a xor b) i = (a + b) i`. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a b i = (a + b) i :=
  Codeword.xor_eq_add_apply a b i

/-- Pointwise XOR with zero on the right: `(a xor 0) i = a i`. -/
example {n : Nat} (a : Codeword n) (i : Fin n) :
    Codeword.xor a 0 i = a i :=
  Codeword.xor_zero_apply a i

/-- Pointwise variant-left involution: `(a xor (b xor a)) i = b i`. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a (Codeword.xor b a) i = b i :=
  Codeword.xor_xor_left_apply a b i

/-- Pointwise XOR right cancellation at index `i`. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) b i = a i :=
  Codeword.xor_xor_right_apply a b i

/-- Pointwise XOR involution at index `i`. -/
example {n : Nat} (Y Ng : Codeword n) (i : Fin n) :
    Codeword.xor Y (Codeword.xor Y Ng) i = Ng i :=
  Codeword.xor_xor_self_apply Y Ng i

/-- Pointwise XOR right-commutativity: `(a xor b) xor c i = (a xor c) xor b i`. -/
example {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) c i
      = Codeword.xor (Codeword.xor a c) b i :=
  Codeword.xor_right_comm_apply a b c i

/-- Pointwise XOR left-commutativity: `a xor (b xor c) i = b xor (a xor c) i`. -/
example {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor a (Codeword.xor b c) i
      = Codeword.xor b (Codeword.xor a c) i :=
  Codeword.xor_left_comm_apply a b c i

/-- Pointwise XOR commutativity at index `i`. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a b i = Codeword.xor b a i :=
  Codeword.xor_comm_apply a b i

/-- Pointwise XOR associativity at index `i`. -/
example {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) c i
      = Codeword.xor a (Codeword.xor b c) i :=
  Codeword.xor_assoc_apply a b c i

/-- Pointwise application of double XOR: `((a xor b) xor c) i = a i + b i + c i`. -/
example {n : Nat} (a b c : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) c i = a i + b i + c i :=
  Codeword.xor_xor_apply a b c i

/-- Pointwise application of Codeword `+`: `(a + b) i = a i + b i`. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    (a + b) i = a i + b i :=
  Codeword.add_apply a b i

/-- Codeword equality iff pointwise equality. -/
example {n : Nat} (a b : Codeword n) :
    a = b <-> forall i, a i = b i :=
  Codeword.eq_iff_apply_eq a b

/-- Pointwise `add_zero` on Codeword: `(a + 0) i = a i`. -/
example {n : Nat} (a : Codeword n) (i : Fin n) :
    (a + 0) i = a i :=
  Codeword.add_zero_apply a i

/-- Pointwise `zero_add` on Codeword: `(0 + a) i = a i`. -/
example {n : Nat} (a : Codeword n) (i : Fin n) :
    (0 + a) i = a i :=
  Codeword.zero_add_apply a i

/-- Codeword equals zero iff every bit is zero. -/
example {n : Nat} (a : Codeword n) :
    a = 0 <-> forall i, a i = 0 :=
  Codeword.eq_zero_iff_apply_zero a

/-- Pointwise value of the zero codeword: `(0 : Codeword n) i = 0`. -/
example {n : Nat} (i : Fin n) : (0 : Codeword n) i = 0 :=
  Codeword.zero_apply i

/-- XOR-zero pointwise form: `xor a b = 0 ↔ ∀ i, a i + b i = 0`. -/
example {n : Nat} (a b : Codeword n) :
    Codeword.xor a b = 0 <-> forall i, a i + b i = 0 :=
  Codeword.xor_eq_zero_iff_apply_zero a b

/-- One-XOR equality is pointwise addition: `xor a b = c ↔ ∀ i, a i + b i = c i`. -/
example {n : Nat} (a b c : Codeword n) :
    Codeword.xor a b = c <-> forall i, a i + b i = c i :=
  Codeword.xor_eq_iff_apply_eq a b c

/-- Two-XOR equality is pointwise addition equality. -/
example {n : Nat} (a b c d : Codeword n) :
    Codeword.xor a b = Codeword.xor c d
      <-> forall i, a i + b i = c i + d i :=
  Codeword.xor_eq_iff_apply_eq_apply a b c d

/-- Codeword XOR pointwise application: `(a xor b) i = a i + b i`. -/
example {n : Nat} (a b : Codeword n) (i : Fin n) :
    Codeword.xor a b i = a i + b i :=
  Codeword.xor_apply a b i

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

/-- `CorrelationCoefficient.mk?` round-trip identity through `.val`. -/
example (v : Real) (h0 : 0 <= v) (h1 : v <= 1) :
    (CorrelationCoefficient.mk? v).map (·.val) = Except.ok v :=
  CorrelationCoefficient.mk?_val_eq v h0 h1

/-- `CorrelationCoefficient.mk?` in `[0, 1]` returns `Except.ok`. -/
example (v : Real) (h0 : 0 <= v) (h1 : v <= 1) :
    CorrelationCoefficient.mk? v = Except.ok ⟨v, h0, h1⟩ :=
  CorrelationCoefficient.mk?_of_mem v h0 h1

/-- `CorrelationCoefficient.mk?` on negative input errors. -/
example (v : Real) (h0 : ¬ 0 <= v) :
    CorrelationCoefficient.mk? v
      = Except.error (ChannelError.correlationOutOfRange v) :=
  CorrelationCoefficient.mk?_of_neg v h0

/-- `CorrelationCoefficient.mk?` on input above 1 errors. -/
example (v : Real) (h0 : 0 <= v) (h1 : ¬ v <= 1) :
    CorrelationCoefficient.mk? v
      = Except.error (ChannelError.correlationOutOfRange v) :=
  CorrelationCoefficient.mk?_of_gt_one v h0 h1

/-- `SamplingFreq.mk?` round-trip identity through `.val`. -/
example (v : Real) (h : 0 < v) :
    (SamplingFreq.mk? v).map (·.val) = Except.ok v :=
  SamplingFreq.mk?_val_eq v h

/-- `SamplingFreq.mk?` on strictly positive input returns `Except.ok`. -/
example (v : Real) (h : 0 < v) :
    SamplingFreq.mk? v = Except.ok ⟨v, h⟩ :=
  SamplingFreq.mk?_of_pos v h

/-- `SamplingFreq.mk?` on non-positive input returns `Except.error`. -/
example (v : Real) (h : ¬ 0 < v) :
    SamplingFreq.mk? v
      = Except.error (ChannelError.nonPositiveSamplingFreq v) :=
  SamplingFreq.mk?_of_not_pos v h

/-- `SignalPower.mk?` round-trip identity through `.val`. -/
example (v : Real) (h : 0 <= v) :
    (SignalPower.mk? v).map (·.val) = Except.ok v :=
  SignalPower.mk?_val_eq v h

/-- `SignalPower.mk?` on non-negative input returns `Except.ok`. -/
example (v : Real) (h : 0 <= v) :
    SignalPower.mk? v = Except.ok ⟨v, h⟩ :=
  SignalPower.mk?_of_nonneg v h

/-- `SignalPower.mk?` on negative input returns `Except.error`. -/
example (v : Real) (h : ¬ 0 <= v) :
    SignalPower.mk? v = Except.error (ChannelError.negativeVariance v) :=
  SignalPower.mk?_of_neg v h

/-- `NoisePower.mk?` round-trip identity through `.val`. -/
example (v : Real) (h : 0 <= v) :
    (NoisePower.mk? v).map (·.val) = Except.ok v :=
  NoisePower.mk?_val_eq v h

/-- `NoisePower.mk?` on non-negative input returns `Except.ok`. -/
example (v : Real) (h : 0 <= v) :
    NoisePower.mk? v = Except.ok ⟨v, h⟩ :=
  NoisePower.mk?_of_nonneg v h

/-- `NoisePower.mk?` on negative input returns `Except.error`. -/
example (v : Real) (h : ¬ 0 <= v) :
    NoisePower.mk? v = Except.error (ChannelError.negativeVariance v) :=
  NoisePower.mk?_of_neg v h

/-- `BlockSize.mk?` on a non-positive input returns `Except.error`. -/
example (n : Nat) (h : ¬ 0 < n) :
    BlockSize.mk? n = Except.error (ChannelError.nonPositive "BlockSize") :=
  BlockSize.mk?_of_not_pos n h

/-- Concrete-input evaluation: `BlockSize.mk? 0` reduces by computation to the
    `nonPositive "BlockSize"` error tag. -/
example : BlockSize.mk? 0 = Except.error (ChannelError.nonPositive "BlockSize") := rfl

/-- `BitsPerSymbol.mk?` on a positive input returns `Except.ok`. -/
example (n : Nat) (h : 0 < n) :
    BitsPerSymbol.mk? n = Except.ok ⟨n, h⟩ :=
  BitsPerSymbol.mk?_of_pos n h

/-- `BitsPerSymbol.mk?` on a non-positive input returns `Except.error`. -/
example (n : Nat) (h : ¬ 0 < n) :
    BitsPerSymbol.mk? n
      = Except.error (ChannelError.nonPositive "BitsPerSymbol") :=
  BitsPerSymbol.mk?_of_not_pos n h

/-- `BitsPerSymbol.mk?` round-trip identity through `.toNat`. -/
example (n : Nat) (h : 0 < n) :
    (BitsPerSymbol.mk? n).map (·.toNat) = Except.ok n :=
  BitsPerSymbol.mk?_toNat_eq n h

/-- `CodewordLength.mk?` on a positive input returns `Except.ok`. -/
example (n : Nat) (h : 0 < n) :
    CodewordLength.mk? n = Except.ok ⟨n, h⟩ :=
  CodewordLength.mk?_of_pos n h

/-- `CodewordLength.mk?` on a non-positive input returns `Except.error`. -/
example (n : Nat) (h : ¬ 0 < n) :
    CodewordLength.mk? n
      = Except.error (ChannelError.nonPositive "CodewordLength") :=
  CodewordLength.mk?_of_not_pos n h

/-- `CodewordLength.mk?` round-trip identity through `.toNat`. -/
example (n : Nat) (h : 0 < n) :
    (CodewordLength.mk? n).map (·.toNat) = Except.ok n :=
  CodewordLength.mk?_toNat_eq n h

/-- `BlockSize.mk?` round-trip identity through `.toNat`. -/
example (n : Nat) (h : 0 < n) :
    (BlockSize.mk? n).map (·.toNat) = Except.ok n :=
  BlockSize.mk?_toNat_eq n h

/-- `BlockSize.mk?` on a positive input returns `Except.ok`. -/
example (n : Nat) (h : 0 < n) :
    BlockSize.mk? n = Except.ok ⟨n, h⟩ :=
  BlockSize.mk?_of_pos n h

/-- `orbgrandAi` with zero budget returns `none`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi ⟨0⟩ patterns = none :=
  orbgrandAi_zero_budget Y Phi patterns

/-- `orbgrandAi` on empty pattern list returns `none`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget [] = none :=
  orbgrandAi_nil Y Phi budget

/-- `orbgrandAi` cons-conflict: conflicting head skipped, advance to rest. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (h : ¬ noSubstitutionConflict e) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi ⟨m + 1⟩ (e :: rest)
      = orbgrandAi Y Phi ⟨m⟩ rest :=
  orbgrandAi_cons_conflict Y Phi m e rest h

/-- `orbgrandAi` cons-reject: head rejected, advance to rest with `m` budget. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (hnc : noSubstitutionConflict e)
    (hp : ¬ Phi (substitute Y e)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi ⟨m + 1⟩ (e :: rest)
      = orbgrandAi Y Phi ⟨m⟩ rest :=
  orbgrandAi_cons_reject Y Phi m e rest hnc hp

/-- `orbgrandAi` cons-accept: head pattern accepted, return `some (substitute Y e)`. -/
example {n_s b numCandidates : Nat} (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (hnc : noSubstitutionConflict e)
    (hp : Phi (substitute Y e)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi ⟨m + 1⟩ (e :: rest)
      = some (substitute Y e) :=
  orbgrandAi_cons_accept Y Phi m e rest hnc hp

/-- `orbgrandAi` unfolds to `orbgrandAiLoop` at `budget.toNat`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (budget : AbandonmentBudget)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAi (b := b) (numCandidates := numCandidates)
      Y Phi budget patterns
      = orbgrandAiLoop Y Phi budget.toNat patterns :=
  orbgrandAi_unfolds_to_loop Y Phi budget patterns

/-- `orbgrandAiLoop` none-iff under sufficient budget: full failure characterisation. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (steps : Nat)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (hbudget : patterns.length <= steps) :
    orbgrandAiLoop Y Phi steps patterns = none <->
      forall e, e ∈ patterns ->
        ¬ noSubstitutionConflict e ∨ ¬ Phi (substitute Y e) :=
  orbgrandAiLoop_none_iff_of_budget Y Phi steps patterns hbudget

/-- `orbgrandAiLoop` none-of-all-fail: every pattern fails => loop returns `none`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (steps : Nat)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (hfail : forall e, e ∈ patterns ->
      ¬ noSubstitutionConflict e ∨ ¬ Phi (substitute Y e)) :
    orbgrandAiLoop Y Phi steps patterns = none :=
  orbgrandAiLoop_none_of_all_fail Y Phi steps patterns hfail

/-- `orbgrandAiLoop` append-left: a successful prefix stays successful after appending. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (c : Codeword n_s)
    (steps : Nat)
    (p1 : List (Fin (n_s / b) -> Fin numCandidates))
    (h : orbgrandAiLoop Y Phi steps p1 = some c)
    (p2 : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAiLoop Y Phi steps (p1 ++ p2) = some c :=
  orbgrandAiLoop_append_left Y Phi c steps p1 h p2

/-- `orbgrandAiLoop` returns strong: existential witness with both conflict + Phi checks. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (c : Codeword n_s)
    (steps : Nat)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (h : orbgrandAiLoop Y Phi steps patterns = some c) :
    exists e, e ∈ patterns
              /\ noSubstitutionConflict e
              /\ Phi (substitute Y e)
              /\ c = substitute Y e :=
  orbgrandAiLoop_returns_strong Y Phi c steps patterns h

/-- `orbgrandAiLoop` returns substituted form: any output `c` is `substitute Y e`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (c : Codeword n_s)
    (steps : Nat)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (h : orbgrandAiLoop Y Phi steps patterns = some c) :
    exists e, e ∈ patterns /\ c = substitute Y e :=
  orbgrandAiLoop_returns_substituted Y Phi c steps patterns h

/-- `orbgrandAiLoop` cons-accept: non-conflicting accepted head returns immediately. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (hnc : noSubstitutionConflict e)
    (hp : Phi (substitute Y e)) :
    orbgrandAiLoop Y Phi (m + 1) (e :: rest)
      = some (substitute Y e) :=
  orbgrandAiLoop_cons_accept Y Phi m e rest hnc hp

/-- `orbgrandAiLoop` cons-reject: rejected non-conflicting head advances to rest. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (hnc : noSubstitutionConflict e)
    (hp : ¬ Phi (substitute Y e)) :
    orbgrandAiLoop Y Phi (m + 1) (e :: rest)
      = orbgrandAiLoop Y Phi m rest :=
  orbgrandAiLoop_cons_reject Y Phi m e rest hnc hp

/-- `orbgrandAiLoop` cons-conflict: conflicting head skipped, advance to rest. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (m : Nat)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates))
    (h : ¬ noSubstitutionConflict e) :
    orbgrandAiLoop Y Phi (m + 1) (e :: rest)
      = orbgrandAiLoop Y Phi m rest :=
  orbgrandAiLoop_cons_conflict Y Phi m e rest h

/-- `orbgrandAiLoop` accept-sound: any `some c` output satisfies `Phi c = true`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (c : Codeword n_s)
    (steps : Nat)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates))
    (h : orbgrandAiLoop Y Phi steps patterns = some c) :
    Phi c = true :=
  orbgrandAiLoop_accept_sound Y Phi c steps patterns h

/-- `orbgrandAiLoop` with empty pattern list returns `none` at any step count. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s) (steps : Nat) :
    orbgrandAiLoop (b := b) (numCandidates := numCandidates)
      Y Phi steps [] = none :=
  orbgrandAiLoop_nil Y Phi steps

/-- `orbgrandAiLoop` with vacuous codebook returns `none` always. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (steps : Nat)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAiLoop Y (fun _ => false) steps patterns = none :=
  orbgrandAiLoop_empty_codebook Y steps patterns

/-- `orbgrandAiLoop` with zero steps returns `none` for any patterns. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (patterns : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAiLoop Y Phi 0 patterns = none :=
  orbgrandAiLoop_zero_steps Y Phi patterns

/-- `orbgrandAiLoop` with zero steps and a non-empty list returns `none`. -/
example {n_s b numCandidates : Nat}
    (Y : Codeword n_s) (Phi : CodebookMembership n_s)
    (e : Fin (n_s / b) -> Fin numCandidates)
    (rest : List (Fin (n_s / b) -> Fin numCandidates)) :
    orbgrandAiLoop Y Phi 0 (e :: rest) = none :=
  orbgrandAiLoop_zero_steps_cons Y Phi e rest

/-- QPSK exceedance is bounded above by 1. -/
example (s s_hat : Fin 4) : qpsk.exceed s s_hat <= 1 :=
  qpsk_exceed_le_one s s_hat

/-- QPSK exceedance is binary-valued (0 or 1). -/
example (s s_hat : Fin 4) :
    qpsk.exceed s s_hat = 0 ∨ qpsk.exceed s s_hat = 1 :=
  qpsk_exceed_zero_or_one s s_hat

/-- BPSK exceedance is bounded above by 1. -/
example (s s_hat : Bool) : bpsk.exceed s s_hat <= 1 :=
  bpsk_exceed_le_one s s_hat

/-- BPSK exceedance is binary-valued (0 or 1). -/
example (s s_hat : Bool) :
    bpsk.exceed s s_hat = 0 ∨ bpsk.exceed s s_hat = 1 :=
  bpsk_exceed_zero_or_one s s_hat

/-- Receiver at both-zero inputs is zero. -/
example {n_s : Nat} (ch : LinearIsi n_s) :
    ch.receive 0 0 = 0 :=
  LinearIsi.receive_zero_signal_zero_noise ch

/-- At zero signal, `receive 0 N = 0` iff `N = 0`. -/
example {n_s : Nat} (ch : LinearIsi n_s) (N : SymbolVector n_s) :
    ch.receive 0 N = 0 <-> N = 0 :=
  LinearIsi.receive_zero_signal_eq_zero_iff ch N

/-- At zero noise, `receive X 0 = 0` iff `h * X = 0`. -/
example {n_s : Nat} (ch : LinearIsi n_s) (X : SymbolVector n_s) :
    ch.receive X 0 = 0 <-> ch.channel.mulVec X = 0 :=
  LinearIsi.receive_zero_noise_eq_zero_iff ch X

/-- Double perturbation entry: `h i j * ((1 + ε₁) * (1 + ε₂))`. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (ε₁ ε₂ : Matrix (Fin n_s) (Fin n_s) Complex) (i j : Fin n_s) :
    perturbChannel (perturbChannel h ε₁) ε₂ i j
      = h i j * ((1 + ε₁ i j) * (1 + ε₂ i j)) :=
  perturbChannel_perturbChannel_apply h ε₁ ε₂ i j

/-- Perturbed channel general entry: `h i j * (1 + epsilon i j)`. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i j : Fin n_s) :
    perturbChannel h epsilon i j = h i j * (1 + epsilon i j) :=
  perturbChannel_apply h epsilon i j

/-- Perturbed channel diagonal entry. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex) (i : Fin n_s) :
    perturbChannel h epsilon i i = h i i * (1 + epsilon i i) :=
  perturbChannel_diag h epsilon i

/-- `perturbChannel` preserves zero entries pointwise. -/
example {n_s : Nat} (h : ChannelMatrix n_s)
    (epsilon : Matrix (Fin n_s) (Fin n_s) Complex)
    {i j : Fin n_s} (hzero : h i j = 0) :
    perturbChannel h epsilon i j = 0 :=
  perturbChannel_zero_entry h epsilon hzero

/-- Pointwise four-argument XOR shuffle at index `i`. -/
example {n : Nat} (a b c d : Codeword n) (i : Fin n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor c d) i
      = Codeword.xor (Codeword.xor a c) (Codeword.xor b d) i :=
  Codeword.xor_xor_comm_apply a b c d i

/-- Four-argument XOR shuffle: `(a xor b) xor (c xor d) = (a xor c) xor (b xor d)`. -/
example {n : Nat} (a b c d : Codeword n) :
    Codeword.xor (Codeword.xor a b) (Codeword.xor c d)
      = Codeword.xor (Codeword.xor a c) (Codeword.xor b d) :=
  Codeword.xor_xor_comm a b c d

/-- Constellation exceedance: positive iff non-zero. -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    0 < cs.exceed s s_hat <-> cs.exceed s s_hat ≠ 0 :=
  cs.exceed_pos_iff_ne_zero s s_hat

/-- Non-zero Constellation exceedance is strictly positive. -/
example {chi : Type} (cs : Constellation chi)
    {s s_hat : chi} (h : cs.exceed s s_hat ≠ 0) :
    0 < cs.exceed s s_hat :=
  cs.exceed_pos_of_ne_zero h

/-- Constellation exceedance dichotomy: zero (on equality) or positive. -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s_hat = 0 \/ 0 < cs.exceed s s_hat :=
  cs.exceed_zero_or_pos s s_hat

/-- Two-argument congruence for Constellation exceed. -/
example {chi : Type} (cs : Constellation chi) {s s' s_hat s_hat' : chi}
    (h_s : s = s') (h_hat : s_hat = s_hat') :
    cs.exceed s s_hat = cs.exceed s' s_hat' :=
  cs.exceed_eq_of_eq h_s h_hat

/-- Symbol inequality implies strictly positive exceedance (generic). -/
example {chi : Type} (cs : Constellation chi) {s s_hat : chi} (h : s ≠ s_hat) :
    0 < cs.exceed s s_hat :=
  cs.exceed_pos_of_ne h

/-- Constellation diagonal at `s_hat` is a lower bound (right form). -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s_hat s_hat <= cs.exceed s s_hat :=
  cs.exceed_self_le_exceed_right s s_hat

/-- Constellation diagonal exceedance is a lower bound. -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s <= cs.exceed s s_hat :=
  cs.exceed_self_le_exceed s s_hat

/-- Constellation exceedance is non-zero iff the symbols differ. -/
example {chi : Type} (cs : Constellation chi) (s s_hat : chi) :
    cs.exceed s s_hat ≠ 0 <-> s ≠ s_hat :=
  cs.exceed_ne_zero_iff_ne s s_hat

/-- `sinc(1) = 0`. -/
example : sinc 1 = 0 := sinc_one

/-- `sinc(0) = 1`. -/
example : sinc 0 = 1 := sinc_zero

/-- Delay-tap impulse response with zero attenuations everywhere is 0. -/
example {p : Nat} (paths : Fin p -> DelayTapPath)
    (h_zero : forall d, (paths d).attenuation = 0)
    (f_s : SamplingFreq) (k' : SymbolIndex) :
    delayTapImpulseResponse paths f_s k' = 0 :=
  delayTapImpulseResponse_zero_attenuations paths h_zero f_s k'

/-- Delay-tap matrix lower-triangular branch: entry = impulse at `i - j`. -/
example {n_s p : Nat} (paths : Fin p -> DelayTapPath) (f_s : SamplingFreq)
    (i j : Fin n_s) (h : j.val ≤ i.val) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s
          { toNat := i.val - j.val } :=
  delayTapMatrix_apply_le paths f_s i j h

/-- Delay-tap matrix at arbitrary sub-diagonal `d`: impulse response at delay `d`. -/
example {n_s p d : Nat} (paths : Fin p -> DelayTapPath) (f_s : SamplingFreq)
    (i j : Fin n_s) (h : i.val = j.val + d) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := d } :=
  delayTapMatrix_at_subdiag paths f_s i j h

/-- Delay-tap matrix third sub-diagonal: impulse response at delay 3. -/
example {n_s p : Nat} (paths : Fin p -> DelayTapPath) (f_s : SamplingFreq)
    (i j : Fin n_s) (h : i.val = j.val + 3) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 3 } :=
  delayTapMatrix_third_subdiag paths f_s i j h

/-- Delay-tap matrix second sub-diagonal: impulse response at delay 2. -/
example {n_s p : Nat} (paths : Fin p -> DelayTapPath) (f_s : SamplingFreq)
    (i j : Fin n_s) (h : i.val = j.val + 2) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 2 } :=
  delayTapMatrix_second_subdiag paths f_s i j h

/-- Delay-tap matrix first sub-diagonal: impulse response at delay 1. -/
example {n_s p : Nat} (paths : Fin p -> DelayTapPath) (f_s : SamplingFreq)
    (i j : Fin n_s) (h : i.val = j.val + 1) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 1 } :=
  delayTapMatrix_first_subdiag paths f_s i j h

/-- Delay-tap matrix diagonal by val-equality: impulse response at delay 0. -/
example {n_s p : Nat} (paths : Fin p -> DelayTapPath) (f_s : SamplingFreq)
    (i j : Fin n_s) (h : i.val = j.val) :
    delayTapMatrix n_s paths f_s i j
      = delayTapImpulseResponse paths f_s { toNat := 0 } :=
  delayTapMatrix_at_diag paths f_s i j h

/-- Delay-tap matrix diagonal entry is the impulse response at delay 0. -/
example {n_s p : Nat} (paths : Fin p -> DelayTapPath)
    (f_s : SamplingFreq) (i : Fin n_s) :
    delayTapMatrix n_s paths f_s i i
      = delayTapImpulseResponse paths f_s { toNat := 0 } :=
  delayTapMatrix_diag paths f_s i

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

/-- Identity-channel zero-signal receive is the noise itself. -/
example {n_s : Nat} (N : SymbolVector n_s) (noiseCov : CovMatrix n_s) :
    ({ channel := 1, noiseCov := noiseCov } : LinearIsi n_s).receive 0 N
      = N :=
  LinearIsi.receive_one_zero_signal N noiseCov

/-- `LinearIsi.tap?` definitional unfold: dependent `if` on `j.val <= k'.val`
    selecting the channel column at index `k'.val - j.val`, else `none`. -/
example {n_s : Nat} (ch : LinearIsi n_s) (k' j : Fin n_s) :
    ch.tap? k' j =
      (if h : j.val <= k'.val then
        some (ch.channel k' ⟨k'.val - j.val,
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) k'.isLt⟩)
      else none) := rfl

/-- Identity-channel zero-noise receive is the signal itself. -/
example {n_s : Nat} (X : SymbolVector n_s) (noiseCov : CovMatrix n_s) :
    ({ channel := 1, noiseCov := noiseCov } : LinearIsi n_s).receive X 0
      = X :=
  LinearIsi.receive_one_zero_noise X noiseCov

/-- `receive` is additive in the noise at zero signal. -/
example {n_s : Nat} (ch : LinearIsi n_s) (N1 N2 : SymbolVector n_s) :
    ch.receive 0 (N1 + N2) = ch.receive 0 N1 + ch.receive 0 N2 :=
  LinearIsi.receive_noise_add_zero_signal ch N1 N2

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

/-- `cov1_lag` at any negative-natural lag: general closed form. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (n : Nat) :
    cov1_lag sigma rho (-(n : Int)) = sigma.val * rho.val ^ n :=
  cov1_lag_of_neg_nat sigma rho n

/-- `cov2_lag` at zero noise power: identically zero (at every lag). -/
example (rho1 rho2 : CorrelationCoefficient) (beta1 beta2 : Real) (n : Nat) :
    cov2_lag ⟨0, le_refl 0⟩ rho1 rho2 beta1 beta2 n = 0 :=
  cov2_lag_zero_sigma rho1 rho2 beta1 beta2 n

/-- `cov1_lag` at zero noise power: identically zero. -/
example (rho : CorrelationCoefficient) (i : Int) :
    cov1_lag ⟨0, le_refl 0⟩ rho i = 0 :=
  cov1_lag_zero_sigma rho i

/-- `cov1_lag` at lag 0: stationary variance. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 0 = sigma.val :=
  cov1_lag_zero sigma rho

/-- `cov1_lag` at lag 1: `sigma * rho`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 1 = sigma.val * rho.val :=
  cov1_lag_one sigma rho

/-- `cov1_lag` is sign-symmetric: `cov1_lag (-i) = cov1_lag i`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (i : Int) :
    cov1_lag sigma rho (-i) = cov1_lag sigma rho i :=
  cov1_lag_neg sigma rho i

/-- `cov2_lag` recurrence at lag `n + 3`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) (n : Nat) :
    cov2_lag sigma rho1 rho2 beta1 beta2 (n + 3)
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 (n + 2)
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 (n + 1) :=
  cov2_lag_succ_succ_succ sigma rho1 rho2 beta1 beta2 n

/-- `cov1_lag` at any natural lag: general closed form. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) (n : Nat) :
    cov1_lag sigma rho (n : Int) = sigma.val * rho.val ^ n :=
  cov1_lag_of_nat sigma rho n

/-- `cov1_lag` at lag 3 = `sigma * rho^3`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 3 = sigma.val * rho.val ^ 3 :=
  cov1_lag_three sigma rho

/-- `cov1_lag` at lag 2 = `sigma * rho^2`. -/
example (sigma : NoisePower) (rho : CorrelationCoefficient) :
    cov1_lag sigma rho 2 = sigma.val * rho.val ^ 2 :=
  cov1_lag_two sigma rho

/-- `cov2_lag` at lag 6: recurrence step from lag 5 and lag 4. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 6
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 5
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 4 :=
  cov2_lag_six sigma rho1 rho2 beta1 beta2

/-- `cov2_lag` at lag 5: recurrence step from lag 4 and lag 3. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 5
      = beta1 * cov2_lag sigma rho1 rho2 beta1 beta2 4
        + beta2 * cov2_lag sigma rho1 rho2 beta1 beta2 3 :=
  cov2_lag_five sigma rho1 rho2 beta1 beta2

/-- `cov2_lag` at lag 0: stationary variance `sigma`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 0 = sigma.val :=
  cov2_lag_zero sigma rho1 rho2 beta1 beta2

/-- `beta1?` definitional unfold: zeta-reduces the `let denom` and pins the
    if-then-else branches to their Yule-Walker AR(1) coefficient form. -/
example (rho1 rho2 : CorrelationCoefficient) :
    beta1? rho1 rho2
      = (if (1 - rho1.val ^ 2) = 0 then none
         else some (rho1.val * (1 - rho2.val) / (1 - rho1.val ^ 2))) := rfl

/-- `cov2_lag` at lag 1: `sigma * rho_1`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 1 = sigma.val * rho1.val :=
  cov2_lag_one sigma rho1 rho2 beta1 beta2

/-- `cov2_lag` at lag 2: `sigma * rho_2`. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 2 = sigma.val * rho2.val :=
  cov2_lag_two sigma rho1 rho2 beta1 beta2

/-- `cov2_lag` at lag 3: first recurrence step. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 3
      = beta1 * (sigma.val * rho2.val) + beta2 * (sigma.val * rho1.val) :=
  cov2_lag_three sigma rho1 rho2 beta1 beta2

/-- `cov2_lag` at lag 4: two-step recurrence expansion. -/
example (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (beta1 beta2 : Real) :
    cov2_lag sigma rho1 rho2 beta1 beta2 4
      = beta1 * (beta1 * (sigma.val * rho2.val)
                  + beta2 * (sigma.val * rho1.val))
        + beta2 * (sigma.val * rho2.val) :=
  cov2_lag_four sigma rho1 rho2 beta1 beta2

/-- Symbol equality implies zero exceedance (generic). -/
example {chi : Type} (cs : Constellation chi) {s s_hat : chi} (h : s = s_hat) :
    cs.exceed s s_hat = 0 :=
  cs.exceed_zero_of_eq h

/-- Zero exceedance implies symbol equality (generic). -/
example {chi : Type} (cs : Constellation chi) {s s_hat : chi}
    (h : cs.exceed s s_hat = 0) :
    s = s_hat :=
  cs.eq_of_exceed_zero h

/-- Generic constellation exceedance vanishes on the diagonal. -/
example {chi : Type} (cs : Constellation chi) (s : chi) :
    cs.exceed s s = 0 :=
  cs.exceed_self s

/-- All-zero-taps lookup yields zero after `getD` at any delay. -/
example (t : RFViewTaps)
    (h1 : t.tap1 = 0) (h2 : t.tap2 = 0) (h3 : t.tap3 = 0)
    (h4 : t.tap4 = 0) (h5 : t.tap5 = 0) (h6 : t.tap6 = 0) (d : Nat) :
    (t.tap? d).getD (0 : Complex) = (0 : Complex) :=
  RFViewTaps.tap?_getD_zero_of_all_zero t h1 h2 h3 h4 h5 h6 d

/-- A row of `rfViewMatrix` is zero when all six of its taps are zero. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i : Fin n_s)
    (h1 : (rowTaps i).tap1 = 0) (h2 : (rowTaps i).tap2 = 0)
    (h3 : (rowTaps i).tap3 = 0) (h4 : (rowTaps i).tap4 = 0)
    (h5 : (rowTaps i).tap5 = 0) (h6 : (rowTaps i).tap6 = 0)
    (j : Fin n_s) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  rfViewMatrix_row_zero_of_taps_zero rowTaps i h1 h2 h3 h4 h5 h6 j

end OrbgrandAi.Examples.SmokeTest
