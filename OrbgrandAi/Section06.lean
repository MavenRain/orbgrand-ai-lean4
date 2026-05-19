import OrbgrandAi.Section06.Csi
import OrbgrandAi.Section06.QueryOrderStability
import OrbgrandAi.Section06.Ar2Approximation

/-!
# Section VI.  Robustness Considerations

Top-level re-export for the robustness layer.  Members:

* `OrbgrandAi.Section06.Csi` -- imperfect channel-state-information
  model `h_est = h * (1 + epsilon)` with normally-distributed
  estimation error, and the normalised mean-squared-error (NMSE) scalar.
* `OrbgrandAi.Section06.QueryOrderStability` -- statement of how
  the ORBGRAND-AI query order degrades smoothly under `|delta_rho| <= eps`
  perturbations of the assumed correlation.
* `OrbgrandAi.Section06.Ar2Approximation` -- the AR(2) approximation
  of the RFView channel, the least-squares fit for the AR coefficients
  `phi_1, phi_2`, and the approximation-error budget that drives the
  observed BLER gap between perfect-CSI and AR(2)-CSI decoding.
-/
