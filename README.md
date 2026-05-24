# orbgrand-ai-lean4

Lean 4 formalization of

> Ken R. Duffy, Moritz Grundei, Jane A. Millward, Muralidhar Rangaswamy,
> Muriel Medard.  *Decoding in the presence of ISI without
> interleaving - ORBGRAND-AI.*  arXiv:2510.14939 (May 2026).

The paper develops ORBGRAND-AI, a soft-input decoder that exploits
the statistical correlation that an inter-symbol-interference (ISI)
channel imparts on additive noise.  Rather than equalising the
correlation away, ORBGRAND-AI factors it into the noise-guessing
order, achieving block error rates competitive with state-of-the-art
turbo decoders without interleaving.

## What is being proved

The library mirrors the paper's section structure.  All items below
are stated as Lean theorems; the table tracks which are fully proved.

| Item | Module | Status |
|------|--------|--------|
| Linear ISI channel `Y = h * X + N`, causality, bandwidth predicates | `Section02.LinearIsi` | defs |
| `LinearIsi.receive_one` (identity channel: `receive X N = X + N`) | `Section02.LinearIsi` | proved |
| `LinearIsi.zero_causal`, `LinearIsi.one_causal` (boundary causality) | `Section02.LinearIsi` | proved (2) |
| `LinearIsi.zero_bandwidth`, `LinearIsi.one_bandwidth` (boundary bandwidth) | `Section02.LinearIsi` | proved (2) |
| `LinearIsi.bandwidth_le` (bandwidth monotonicity: stronger => weaker) | `Section02.LinearIsi` | proved |
| `LinearIsi.zero_channel_receive` (zero channel ignores X: `receive X N = N`) | `Section02.LinearIsi` | proved |
| `LinearIsi.receive_zero_noise` (`receive X 0 = h * X`) | `Section02.LinearIsi` | proved |
| `LinearIsi.receive_zero_signal` (`receive 0 N = N`) | `Section02.LinearIsi` | proved |
| `LinearIsi.receive_noise_add` (additivity in the noise term) | `Section02.LinearIsi` | proved |
| `LinearIsi.receive_add` (full linearity: `receive (X1+X2) (N1+N2) = receive X1 N1 + receive X2 N2`) | `Section02.LinearIsi` | proved |
| Dicode partial-response channel `(1, -rho, 0, ...)` (matrix def) | `Section02.Dicode` | def |
| `dicodeMatrix_diag`, `_subdiag`, `_off` (explicit per-branch entries) | `Section02.Dicode` | proved (3) |
| `dicode_bandwidth` (entries `j + 1 < i` vanish) | `Section02.Dicode` | proved |
| `dicode_causal` (entries `i < j` vanish) | `Section02.Dicode` | proved |
| `dicode_zf_equalisation` (post-equalisation covariance = Gauss-Markov template) | `Section02.Dicode` | proved |
| `gaussMarkovCov_diag` (general `n_s`: `M i i = sigma`) | `Section02.Dicode` | proved |
| `gaussMarkovCov_entry_of_le`, `_of_ge` (general off-diagonal) | `Section02.Dicode` | proved (2) |
| `gaussMarkovCov_sym` (matrix is symmetric: `M i j = M j i`) | `Section02.Dicode` | proved |
| `gaussMarkovCov_two_00`, `_01`, `_10`, `_11` (2x2 entry lemmas) | `Section02.Dicode` | proved (4) |
| `cov1_det_fin_two` (2x2 first-order Gauss-Markov det, unfolded form) | `Section02.Dicode` | proved |
| `cov1_det_fin_two_factored` (`= sigma^2 * (1 - rho^2)`) | `Section02.Dicode` | proved |
| Delay-tap impulse response `h_{k', j} = sum_d a sinc(...)` | `Section02.DelayTap` | def |
| `delayTap_causal` (entries `i < j` vanish) | `Section02.DelayTap` | proved |
| `sinc_zero` (sinc(0) = 1) | `Section02.DelayTap` | proved |
| `delayTapImpulseResponse_zero_attenuations` (no paths => zero response) | `Section02.DelayTap` | proved |
| RFView 6-tap channel matrix | `Section02.RFView` | def |
| `rfView_causal` (entries `i < j` vanish) | `Section02.RFView` | proved |
| `RFViewTaps.tap?_zero` through `tap?_six` | `Section02.RFView` | proved (7 rfl) |
| `RFViewTaps.tap?_of_ge_seven` helper | `Section02.RFView` | proved |
| `rfView_bandwidth` (entries `j + 6 < i` vanish) | `Section02.RFView` | proved |
| First-order Gauss-Markov `cov1_lag` and AR(1) recurrence | `Section03.GaussMarkov` | def |
| `cov1_lag_zero`, `cov1_lag_one`, `cov1_lag_neg` (closed-form values + sign-symmetry) | `Section03.GaussMarkov` | proved (3) |
| Second-order Gauss-Markov `cov2_lag` and Yule-Walker coeffs | `Section03.GaussMarkov` | def |
| `cov2_lag_zero`, `_one`, `_two`, `_three`, `_succ_succ_succ` base cases + first recurrence step | `Section03.GaussMarkov` | proved (5 rfl) |
| `cov2_lag_beta_zero` (trivial AR coeffs vanish past lag 2) | `Section03.GaussMarkov` | proved |
| Yule-Walker variance bound -> `rho_1^2 < (rho_2 + 1) / 2` | `Section03.GaussMarkov` | placeholder (3/4 sub-lemmas) |
| `yuleWalker_denom_pos` (sub-lemma 1: `0 < 1 - rho_1^2`) | `Section03.GaussMarkov` | proved |
| `yuleWalker_rho1_sq_lt_one` (corollary: `rho_1^2 < 1`) | `Section03.GaussMarkov` | proved |
| `yuleWalker_rho1_lt_one` (corollary: `rho_1 < 1`) | `Section03.GaussMarkov` | proved |
| `yuleWalker_num_lt_denom` (sub-lemma 2) | `Section03.GaussMarkov` | proved |
| `yuleWalker_step3` (sub-lemma 3: `2*rho_1^2 + rho_2^2 - 2*rho_1^2*rho_2 < 1`) | `Section03.GaussMarkov` | proved |
| Auto-covariance determinant closed form for `n_s >= 4` | `Section03.Determinant` | placeholder |
| Determinant positivity under Yule-Walker | `Section03.Determinant` | placeholder |
| `entropyRate1_eq` first-order entropy rate formula | `Section03.EntropyRate` | proved |
| `entropyRate1_block_eq` block-`b` entropy rate formula | `Section03.EntropyRate` | proved |
| `entropyRate1_asymp_eq` (asymptotic form unfolding) | `Section03.EntropyRate` | proved (rfl) |
| `entropyRate1_eq_block` (entropyRate1 = entropyRate1_block at n_s = b.toNat) | `Section03.EntropyRate` | proved (rfl) |
| `entropyRate2_eq` second-order entropy rate formula | `Section03.EntropyRate` | proved |
| Hadamard bound on `log |C_N|` | `Section03.Capacity` | placeholder |
| Channel capacity upper bound | `Section03.Capacity` | placeholder |
| GRAND syndrome and search loop | `Section04.Grand` | def |
| `Codeword.xor_eq_add` (bridge to Pi.instAdd), `sub_eq_xor`, `neg_eq_self` (CharTwo) | `Section04.Grand` | proved (3) |
| `Codeword.zero_xor`, `xor_zero`, `xor_self`, `xor_comm`, `xor_assoc` | `Section04.Grand` | proved (5) |
| `Codeword.xor_xor_self` (XOR involution; now derived from the algebra) | `Section04.Grand` | proved |
| `Codeword.xor_xor_right` (right cancel: `(a xor b) xor b = a`) | `Section04.Grand` | proved |
| `Codeword.xor_eq_iff_eq_xor` (transposition: `a xor b = c ↔ a = c xor b`) | `Section04.Grand` | proved |
| `Codeword.xor_left_cancel`, `xor_right_cancel` | `Section04.Grand` | proved (2) |
| `Codeword.xor_left_eq_iff`, `xor_right_eq_iff` (iff forms of cancellation) | `Section04.Grand` | proved (2) |
| `Codeword.xor_eq_self_iff` (identity iff right arg zero) | `Section04.Grand` | proved |
| `Codeword.add_eq_zero_iff` (`+` form of equality characterisation: `a + b = 0 ↔ a = b`) | `Section04.Grand` | proved |
| `Codeword.eq_iff_xor_eq_zero`, `eq_of_xor_eq_zero`, `xor_eq_zero_of_eq` | `Section04.Grand` | proved (3) |
| `syndrome_decomp` (syndrome linearity: H*Y + H*N_g) | `Section04.Grand` | proved |
| `syndrome_codeword` (on a codeword receiver, syndrome = H*N_g) | `Section04.Grand` | proved |
| `syndromeZero_iff_noise_codeword` (Y codeword => GRAND accepts iff N_g is codeword) | `Section04.Grand` | proved |
| `syndrome_zero_noise`, `syndrome_zero_received`, `syndrome_comm` (boundary syndrome algebra) | `Section04.Grand` | proved (3) |
| `syndrome_invariant_under_codeword` (coset property: syndrome stable under codeword shift of Y) | `Section04.Grand` | proved |
| `Codeword.zero_is_codeword`, `Codeword.xor_codeword_is_codeword` (subspace identity + closure) | `Section04.Grand` | proved (2) |
| `grandFind_none_imp`, `_mpr`, `_iff` (GRAND failure characterisation) | `Section04.Grand` | proved (3) |
| `grandFind_nil` (empty list returns none) | `Section04.Grand` | proved |
| `grandFind_cons_zero_syndrome`, `_nonzero_syndrome` (cons-case decomposition) | `Section04.Grand` | proved (2) |
| `grandFind_zero_syndrome` (decoder output has zero syndrome) | `Section04.Grand` | proved |
| `grandFind_returns_xor` (output = `Codeword.xor Y Ng` for some `Ng ∈ order`) | `Section04.Grand` | proved |
| `grandFind_zero_first` (Y a codeword + 0 first in order => GRAND returns Y) | `Section04.Grand` | proved |
| `grandFind_sound` (zero syndrome AND candidate-from-input, full GRAND spec) | `Section04.Grand` | proved |
| `grandFind_singleton` (one-candidate case = single syndrome check) | `Section04.Grand` | proved |
| `grandFind_append_left` (extension stability: acceptance survives list extension) | `Section04.Grand` | proved |
| `grandFind_syndromeZero` (alias on syndromeZero) | `Section04.Grand` | proved |
| `grand_ml_optimal` (ML-optimality under decreasing-likelihood order) | `Section04.Grand` | proved |
| ORBGRAND landslide enumeration (`landslideExtend` + `landslide`) | `Section04.Orbgrand` | def (concrete) |
| `landslide_zero_zero`, `landslide_zero_succ`, `logisticWeight_elim0` (base cases) | `Section04.Orbgrand` | proved (3) |
| `landslide_one_zero`, `landslide_one_one` (closed-form at length 1) | `Section04.Orbgrand` | proved (2) |
| `landslide_two_one`, `landslide_two_two` (closed-form at length 2) | `Section04.Orbgrand` | proved (2 rfl) |
| `landslideExtend_last`, `landslideExtend_castSucc` (Fin.lastCases at last/castSucc) | `Section04.Orbgrand` | proved (2) |
| `bitWeight` (identity-rank logistic weight) + `bitWeight_elim0`, `bitWeight_extend_false`, `bitWeight_extend_true` | `Section04.Orbgrand` | def + proved (3) |
| `bitWeight_landslideExtend` (unified extension rule: bitWeight + ite) | `Section04.Orbgrand` | proved |
| `bitWeight_le_landslideExtend` (extension never decreases bit-weight) | `Section04.Orbgrand` | proved |
| `bitWeight_lt_landslideExtend_true` (extension by true strictly increases bit-weight) | `Section04.Orbgrand` | proved |
| `bitWeight_fin_zero` (any length-0 pattern has zero bit-weight) | `Section04.Orbgrand` | proved |
| `landslide_zero_iff` (landslide correctness base case n = 0) | `Section04.Orbgrand` | proved |
| `landslideExtend_split` (every pattern is extend of top bit + restriction) | `Section04.Orbgrand` | proved |
| `landslideExtend_inj` (extend with fixed top bit is injective) | `Section04.Orbgrand` | proved |
| `landslideExtend_inj_top` (extend with fixed restriction is injective in top bit) | `Section04.Orbgrand` | proved |
| `landslideExtend_eq_iff` (extensions equal iff top bits AND restrictions agree) | `Section04.Orbgrand` | proved |
| `landslideExtend_bijective` (as a function `Bool × restriction → pattern`) | `Section04.Orbgrand` | proved |
| `landslideExtend_inv` (def) + roundtrip lemmas (`_inv_landslideExtend`, `landslideExtend_landslideExtend_inv`) | `Section04.Orbgrand` | def + proved (2) |
| `landslideExtend_exists` (existential decomposition) | `Section04.Orbgrand` | proved |
| `bitWeight_split_false`, `bitWeight_split_true` (weight decomposition under top bit) | `Section04.Orbgrand` | proved (2) |
| `bitWeight_castSucc_le` (restriction never increases bit-weight) | `Section04.Orbgrand` | proved |
| `bitWeight_castSucc_lt_of_last_true` (strict <: when top bit true) | `Section04.Orbgrand` | proved |
| `mem_map_extend_iff` (membership in `(...).map (landslideExtend b)`) | `Section04.Orbgrand` | proved |
| `landslide_correct` (e ∈ landslide n w ↔ bitWeight e = w, full inductive proof) | `Section04.Orbgrand` | proved |
| `landslide_self_mem` (every pattern is in its own bucket) | `Section04.Orbgrand` | proved |
| `landslide_unique_bucket` (a pattern lives in only one bucket) | `Section04.Orbgrand` | proved |
| `orbgrandEnumeration_correct` (wrapper around `landslide_correct`) | `Section04.Orbgrand` | proved |
| `bitWeight_zero_iff_all_false` (zero weight iff all bits false) | `Section04.Orbgrand` | proved |
| `bitWeight_const_false`, `const_false_mem_landslide_zero` (all-false pattern in bucket 0) | `Section04.Orbgrand` | proved (2) |
| `landslideExtend_false_const_false`, `landslide_zero_singleton` (bucket 0 is exactly `[fun _ => false]`) | `Section04.Orbgrand` | proved (2) |
| `landslideExtend_true_const_true` (dual: extending all-true by true yields all-true) | `Section04.Orbgrand` | proved |
| `landslide_max_singleton` (max-weight bucket = `[fun _ => true]`) | `Section04.Orbgrand` | proved |
| `landslide_max_length` (max-weight bucket has length 1) | `Section04.Orbgrand` | proved |
| `landslide_max_nodup`, `landslide_zero_nodup` (singleton buckets are Nodup) | `Section04.Orbgrand` | proved (2) |
| `bitWeight_le_sum` (upper bound on bit-weight = sum of `(i + 1)` over `Fin n`) | `Section04.Orbgrand` | proved |
| `bitWeight_const_true` (all-true pattern's weight = sum) | `Section04.Orbgrand` | proved (rfl) |
| `bitWeight_le_const_true` (bit-weight always ≤ all-true's bit-weight) | `Section04.Orbgrand` | proved |
| `bitWeight_lt_const_true_of_exists_false` (strict <: any false bit ⇒ strict less) | `Section04.Orbgrand` | proved |
| `bitWeight_eq_const_true_iff` (max-weight iff all bits true; dual of `bitWeight_zero_iff_all_false`) | `Section04.Orbgrand` | proved |
| `bitWeight_zero_iff_eq_const_false`, `bitWeight_eq_max_iff_eq_const_true` (pattern-equality forms) | `Section04.Orbgrand` | proved (2) |
| `landslide_eq_nil_of_too_large` (`w > bitWeight (fun _ => true)` ⇒ bucket empty) | `Section04.Orbgrand` | proved |
| `landslide_eq_nil_iff` (bucket empty iff no pattern has that bit-weight) | `Section04.Orbgrand` | proved |
| `landslide_singleton_unique` (singleton bucket's element is unique) | `Section04.Orbgrand` | proved |
| `landslide_not_mem_iff` (negation of `landslide_correct`) | `Section04.Orbgrand` | proved |
| `landslide_zero_zero_length`, `landslide_zero_succ_length` (size at length 0) | `Section04.Orbgrand` | proved (2) |
| `landslideBucket` predicate, `landslideBucket_self` (membership reflexivity) | `Section04.Orbgrand` | proved |
| `orbgrand_ordering_sound` (lower logistic weight => earlier bucket) | `Section04.Orbgrand` | proved |
| ORBGRAND-AI Algorithm 1 (`orbgrandAi`, `orbgrandAiLoop`) | `Section04.OrbgrandAi` | def |
| `orbgrandAiLoop_accept_sound`, `orbgrandAi_accept_sound` | `Section04.OrbgrandAi` | proved |
| `orbgrandAiLoop_cons_conflict`, `_cons_accept`, `_cons_reject` (cons-case decomposition) | `Section04.OrbgrandAi` | proved (3) |
| `orbgrandAiLoop_nil`, `_zero_steps` (loop boundary cases) | `Section04.OrbgrandAi` | proved (2) |
| `orbgrandAi_empty_patterns`, `_zero_budget` (top-level boundary cases) | `Section04.OrbgrandAi` | proved (2) |
| `orbgrandAiLoop_empty_codebook` (`Phi = fun _ => false` => loop returns none) | `Section04.OrbgrandAi` | proved |
| `orbgrandAi_empty_codebook` (top-level vacuous-codebook wrapper) | `Section04.OrbgrandAi` | proved |
| `orbgrandAiLoop_returns_substituted` (output = substitute Y e for some pattern e) | `Section04.OrbgrandAi` | proved |
| `orbgrandAi_returns_substituted` (top-level substitution-provenance) | `Section04.OrbgrandAi` | proved |
| `orbgrandAi_sound` (codebook acceptance AND substitution-provenance, full spec) | `Section04.OrbgrandAi` | proved |
| `orbgrandAiLoop_returns_strong`, `orbgrandAi_returns_strong` (witness pattern carries noSubsConflict + Phi) | `Section04.OrbgrandAi` | proved (2) |
| `orbgrandAiLoop_none_of_all_fail`, `orbgrandAi_none_of_all_fail` (all-fail => none, dual of strong soundness) | `Section04.OrbgrandAi` | proved (2) |
| `orbgrandAiLoop_none_imp_all_fail_of_budget` (sufficient budget => failure forces all-fail) | `Section04.OrbgrandAi` | proved |
| `orbgrandAiLoop_none_iff_of_budget`, `orbgrandAi_none_iff_of_budget` (full iff under sufficient budget) | `Section04.OrbgrandAi` | proved (2) |
| `orbgrandAiLoop_append_left`, `orbgrandAi_append_left` (extension stability) | `Section04.OrbgrandAi` | proved (2) |
| Approximate-independence block factorisation | `Section04.OrbgrandAi` | def |
| `perturbChannel_zero` (zero perturbation is identity) | `Section06.Csi` | proved |
| `perturbChannel_zero_channel` (zero channel stays zero under any perturbation) | `Section06.Csi` | proved |
| `perturbChannel_causal_of_causal` (causality preserved under perturbation) | `Section06.Csi` | proved |
| `perturbChannel_bandwidth_of_bandwidth` (bandwidth preserved under perturbation) | `Section06.Csi` | proved |
| `Constellation.exceed_pos_iff_ne` (strict positivity dual of `exceed_zero_iff`) | `Section04.SymbolLevel` | proved |
| `bpsk` (BPSK constellation instance: `Constellation Bool`) | `Section04.SymbolLevel` | def |
| `bpsk_exceed_self`, `bpsk_exceed_diff`, `bpsk_exceed_symm` (BPSK exceedance: closed forms + symmetry) | `Section04.SymbolLevel` | proved (3) |
| `qpsk` (QPSK constellation: `Constellation (Fin 4)`) | `Section04.SymbolLevel` | def |
| `qpsk_exceed_self`, `qpsk_exceed_diff`, `qpsk_exceed_symm` (QPSK exceedance: closed forms + symmetry) | `Section04.SymbolLevel` | proved (3) |
| `trivialConstellation` (1-symbol constellation over Unit) + `trivialConstellation_exceed` | `Section04.SymbolLevel` | def + proved |
| AR(2) least-squares coefficient fit | `Section06.Ar2Approximation` | def (opaque fit) |
| `ar2_zero`, `ar2_one`, `ar2_succ_succ` base cases | `Section06.Ar2Approximation` | proved (3 rfl) |
| `ar2_two`, `ar2_three`, `ar2_four` closed-form values | `Section06.Ar2Approximation` | proved (3 rfl) |
| `ar2_phi_zero` (trivial coefficients vanish past initial conditions) | `Section06.Ar2Approximation` | proved |
| `ar2_phi1_one_phi2_zero` (AR(1)-like degenerate: constant at z2 from index 1) | `Section06.Ar2Approximation` | proved |
| Query-order stability under `|delta_rho| <= eps` | `Section06.QueryOrderStability` | placeholder |

### Status legend

* **def**: a Lean `def` or `structure` with the right type, no proof obligation.
* **proved**: a Lean `theorem` with a full proof; no `sorry`, no `True`-placeholder.
* **placeholder**: stated as `... -> True := by kan_intro _h; kan_constructor`; the formal theorem signature lives in the file but discharging it is scheduled for a follow-up.

## Building

### Prerequisites

* [elan](https://github.com/leanprover/elan) (Lean version manager).

`kan-tactics` is pulled in automatically from
<https://github.com/MavenRain/kan-tactics> by `lake update`; no
sibling checkout is required.

### Build

```sh
lake build
```

The first build fetches and compiles Mathlib, which takes a while.
Subsequent builds are incremental.

### Verify

A successful `lake build` with no errors and no `sorry` warnings
confirms that all proofs type-check.

### Smoke test

The `OrbgrandAi.Examples.SmokeTest` module exercises every major
public theorem via short `example` declarations.  It is *not* part
of the default `lake build` target so that downstream projects
depending on `OrbgrandAi` do not pay the compile cost.  Run it
explicitly with:

```sh
lake build OrbgrandAiExamples
```

If any `example` fails to type-check, the corresponding theorem's
public API has changed and downstream uses will break.

### Documentation

API documentation is generated by
[`doc-gen4`](https://github.com/leanprover/doc-gen4), pinned to the
`v4.30.0-rc1` tag so it stays compatible with Mathlib's toolchain.
The `doc-gen4` require in `lakefile.lean` is unconditional; an
attempt to gate it behind `meta if get_config? env = some "dev"` did
not activate under `lake -Kenv=dev update` on this Lake version, so
the require is always evaluated.  The default `lake build` does not
invoke any doc-gen4 facet, so the unconditional require costs only a
one-time fetch but no extra build work.

To build the documentation locally:

```sh
lake update
lake build OrbgrandAi:docs
```

The HTML output lands in `.lake/build/doc/`.  Open
`.lake/build/doc/index.html` in a browser.

The repository's `.github/workflows/docs.yml` workflow builds the
documentation on every push and pull request, and deploys it to
GitHub Pages on pushes to `main`.  The workflow checks out
`kan-tactics` as a sibling directory before invoking `lake`, so the
sibling-path `require` in `lakefile.lean` resolves correctly on CI.

A second workflow, `.github/workflows/ci.yml`, runs a plain
`lake build` via `leanprover/lean-action@v1` on every push and pull
request.  It catches type-check regressions without invoking
`doc-gen4`, so a failing PR's signal arrives in a couple of minutes
rather than waiting for the full docs build.

## Using as a dependency

Other Lean 4 projects can depend on this library by adding to their
`lakefile.lean`:

```lean
require OrbgrandAi from git
  "https://github.com/MavenRain/orbgrand-ai-lean4" @ "main"
```

and then importing the top-level module:

```lean
import OrbgrandAi
```

## Project structure

```
orbgrand-ai-lean4/
  lakefile.lean              -- package config; depends on Mathlib + kan-tactics
  lean-toolchain             -- leanprover/lean4:v4.30.0-rc1
  OrbgrandAi.lean            -- root import; project-level documentation
  OrbgrandAi/
    Section02.lean           -- Section II re-export
    Section02/
      Basic.lean             -- newtypes shared by all channel models
      LinearIsi.lean         -- linear ISI model Y = h * X + N
      Dicode.lean            -- two-tap dicode partial-response channel
      DelayTap.lean          -- delay-tap impulse response with sinc kernel
      RFView.lean            -- RFView 6-tap channel and AR(2) approximation
    Section03.lean           -- Section III re-export
    Section03/
      GaussMarkov.lean       -- Gauss-Markov processes, Yule-Walker constraints
      Determinant.lean       -- |C_N^{n x n}| closed form
      EntropyRate.lean       -- differential entropy rates of noise
      Capacity.lean          -- Verdu-Han information rate, capacity upper bound
    Section04.lean           -- Section IV re-export
    Section04/
      Grand.lean             -- GRAND decoder, syndrome, ML optimality
      Orbgrand.lean          -- soft-input ORBGRAND, logistic-weight ordering
      OrbgrandAi.lean        -- the paper's Algorithm 1, block factorisation
      SymbolLevel.lean       -- symbol-level pattern-dedup variant
    Section06.lean           -- Section VI re-export
    Section06/
      Csi.lean               -- imperfect channel-state-information model
      QueryOrderStability.lean -- stability of the noise-guess order
      Ar2Approximation.lean  -- AR(2) least-squares fit, approximation error
```

## kan-tactics

All tactic proofs in this project use exclusively
[kan-tactics](https://github.com/MavenRain/kan-tactics), a library
that re-implements Lean 4 tactics as Kan-extension computations.  No
standard tactics (`simp`, `rfl`, `intro`, `apply`, ...) appear in any
`by ...` block.  Term-mode proofs that happen to involve names like
`rfl` as values are permitted.

## Dependencies

* **Mathlib4** (commit `c290b55`): complex numbers, matrices,
  determinants, Gaussian measures, differential entropy,
  `Filter.liminf` / `limsup`, log / exp analysis.
* **kan-tactics** (local, `../kan-tactics/`): all proof tactics.

## References

* K. R. Duffy, M. Grundei, J. A. Millward, M. Rangaswamy, M. Medard,
  "Decoding in the presence of ISI without interleaving -
  ORBGRAND-AI," 2026.
  [arXiv:2510.14939](https://arxiv.org/abs/2510.14939).
* K. R. Duffy, J. Li, M. Medard, "Capacity-achieving guessing random
  additive noise decoding," *IEEE Trans. Inf. Theory* 65(7), 2019.
* S. Verdu, T. S. Han, "A general formula for channel capacity,"
  *IEEE Trans. Inf. Theory* 40(4), 1994.

## License

Licensed under either of

* Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
* MIT License
  ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.
