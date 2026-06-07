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

/-- AR(2) recurrence step at index 5. -/
example (phi1 phi2 z1 z2 : Complex) :
    ar2 phi1 phi2 z1 z2 5
      = phi1 * ar2 phi1 phi2 z1 z2 4
        + phi2 * ar2 phi1 phi2 z1 z2 3 :=
  ar2_five phi1 phi2 z1 z2

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

/-- A row of `rfViewMatrix` is zero when all six of its taps are zero. -/
example {n_s : Nat} (rowTaps : Fin n_s -> RFViewTaps) (i : Fin n_s)
    (h1 : (rowTaps i).tap1 = 0) (h2 : (rowTaps i).tap2 = 0)
    (h3 : (rowTaps i).tap3 = 0) (h4 : (rowTaps i).tap4 = 0)
    (h5 : (rowTaps i).tap5 = 0) (h6 : (rowTaps i).tap6 = 0)
    (j : Fin n_s) :
    rfViewMatrix n_s rowTaps i j = (0 : Complex) :=
  rfViewMatrix_row_zero_of_taps_zero rowTaps i h1 h2 h3 h4 h5 h6 j

end OrbgrandAi.Examples.SmokeTest
