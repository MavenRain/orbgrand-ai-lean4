import OrbgrandAi.Section03.GaussMarkov
import OrbgrandAi.Section03.Determinant
import OrbgrandAi.Section03.EntropyRate
import OrbgrandAi.Section03.Capacity

/-!
# Section III.  Theoretical Heuristic

Top-level re-export for the information-theoretic layer.  Members:

* `OrbgrandAi.Section03.GaussMarkov` -- noise covariance structure for
  first- and second-order stationary Gauss-Markov processes, including
  the Yule-Walker stability constraints
  `rho_1^2 < (rho_2 + 1) / 2`.
* `OrbgrandAi.Section03.Determinant` -- the closed-form determinant
  of the second-order Gauss-Markov auto-covariance matrix for
  `n_s >= 4`.
* `OrbgrandAi.Section03.EntropyRate` -- normalised differential entropy
  rates of first- and second-order Gauss-Markov noise, and of
  block-independent approximations of size `b`.
* `OrbgrandAi.Section03.Capacity` -- the Verdu-Han lim-inf
  information rate, the lim-sup entropy rate, and the upper bound on
  channel capacity for additive second-order Gauss-Markov noise via
  Hadamard's inequality.
-/
