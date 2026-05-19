import OrbgrandAi.Section04.Grand
import OrbgrandAi.Section04.Orbgrand
import OrbgrandAi.Section04.OrbgrandAi
import OrbgrandAi.Section04.SymbolLevel

/-!
# Section IV.  ORBGRAND-AI

Top-level re-export for the decoder layer.  Members:

* `OrbgrandAi.Section04.Grand` -- the abstract Guessing Random
  Additive Noise Decoding scheme.  Encodes parity-check matrices,
  syndrome computation, and the noise-guess search.  States and
  proves the ML-optimality theorem under a sound (decreasing-
  likelihood) query order.
* `OrbgrandAi.Section04.Orbgrand` -- soft-input variant.  Linear-
  reliability approximation, logistic-weight ordering, the landslide
  pattern generator.
* `OrbgrandAi.Section04.OrbgrandAi` -- the correlation-aware variant
  of the paper.  Block factorisation under approximate independence,
  candidate-block ranking, Algorithm 1 with abandonment threshold.
* `OrbgrandAi.Section04.SymbolLevel` -- the symbol-level rank-ordering
  variant referenced in IV.C, including pattern deduplication.
-/
