import OrbgrandAi.Section00.Probability

/-!
# Section 0.  Probability layer (umbrella)

Top-level re-export for the probability layer.  Members:

* `OrbgrandAi.Section00.Probability` -- the AWGN noise distribution
  `noiseMeasure n_s sigma` on `EuclideanSpace ℝ (Fin n_s)` (built
  from Mathlib's `multivariateGaussian`), the real-valued symbol
  vector type `RealSymbolVector n_s`, and the block error rate
  `bler sigma decode`.

This sub-module sits at "Section 0" in the project layout: the paper
does not have a numbered probability section, but downstream Section IV
(symbol-level / bit-level equivalence) and Section VI.B
(imperfect-CSI error floor) both depend on a noise probability layer.
Promoting it to its own module pays the Mathlib measure-theory imports
exactly once.
-/
