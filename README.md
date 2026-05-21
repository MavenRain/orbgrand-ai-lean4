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
| Dicode partial-response channel `(1, -rho, 0, ...)` (matrix def) | `Section02.Dicode` | def |
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
| RFView 6-tap channel matrix | `Section02.RFView` | def |
| `rfView_causal` (entries `i < j` vanish) | `Section02.RFView` | proved |
| `RFViewTaps.tap?_zero` through `tap?_six` | `Section02.RFView` | proved (7 rfl) |
| `RFViewTaps.tap?_of_ge_seven` helper | `Section02.RFView` | proved |
| `rfView_bandwidth` (entries `j + 6 < i` vanish) | `Section02.RFView` | proved |
| First-order Gauss-Markov `cov1_lag` and AR(1) recurrence | `Section03.GaussMarkov` | def |
| Second-order Gauss-Markov `cov2_lag` and Yule-Walker coeffs | `Section03.GaussMarkov` | def |
| `cov2_lag_zero`, `_one`, `_two`, `_succ_succ_succ` base cases | `Section03.GaussMarkov` | proved (4 rfl) |
| Yule-Walker variance bound -> `rho_1^2 < (rho_2 + 1) / 2` | `Section03.GaussMarkov` | placeholder (3/4 sub-lemmas) |
| `yuleWalker_denom_pos` (sub-lemma 1) | `Section03.GaussMarkov` | proved |
| `yuleWalker_num_lt_denom` (sub-lemma 2) | `Section03.GaussMarkov` | proved |
| `yuleWalker_step3` (sub-lemma 3: `2*rho_1^2 + rho_2^2 - 2*rho_1^2*rho_2 < 1`) | `Section03.GaussMarkov` | proved |
| Auto-covariance determinant closed form for `n_s >= 4` | `Section03.Determinant` | placeholder |
| Determinant positivity under Yule-Walker | `Section03.Determinant` | placeholder |
| `entropyRate1_eq` first-order entropy rate formula | `Section03.EntropyRate` | proved |
| `entropyRate1_block_eq` block-`b` entropy rate formula | `Section03.EntropyRate` | proved |
| `entropyRate2_eq` second-order entropy rate formula | `Section03.EntropyRate` | proved |
| Hadamard bound on `log |C_N|` | `Section03.Capacity` | placeholder |
| Channel capacity upper bound | `Section03.Capacity` | placeholder |
| GRAND syndrome and search loop | `Section04.Grand` | def |
| `Codeword.zero_xor`, `xor_zero`, `xor_self`, `xor_comm`, `xor_assoc` | `Section04.Grand` | proved (5) |
| `Codeword.xor_xor_self` (XOR involution; now derived from the algebra) | `Section04.Grand` | proved |
| `Codeword.xor_left_cancel`, `xor_right_cancel` | `Section04.Grand` | proved (2) |
| `Codeword.eq_iff_xor_eq_zero`, `eq_of_xor_eq_zero`, `xor_eq_zero_of_eq` | `Section04.Grand` | proved (3) |
| `grandFind_zero_syndrome` (decoder output has zero syndrome) | `Section04.Grand` | proved |
| `grandFind_syndromeZero` (alias on syndromeZero) | `Section04.Grand` | proved |
| `grand_ml_optimal` (ML-optimality under decreasing-likelihood order) | `Section04.Grand` | proved |
| ORBGRAND landslide enumeration | `Section04.Orbgrand` | def (opaque enum) |
| ORBGRAND-AI Algorithm 1 (`orbgrandAi`, `orbgrandAiLoop`) | `Section04.OrbgrandAi` | def |
| `orbgrandAiLoop_accept_sound`, `orbgrandAi_accept_sound` | `Section04.OrbgrandAi` | proved |
| Approximate-independence block factorisation | `Section04.OrbgrandAi` | def |
| AR(2) least-squares coefficient fit | `Section06.Ar2Approximation` | def (opaque fit) |
| `ar2_zero`, `ar2_one`, `ar2_succ_succ` base cases | `Section06.Ar2Approximation` | proved (3 rfl) |
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
