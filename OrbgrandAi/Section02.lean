import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section02.LinearIsi
import OrbgrandAi.Section02.DelayTap
import OrbgrandAi.Section02.Dicode
import OrbgrandAi.Section02.RFView

/-!
# Section II.  ISI Channel Description

Top-level re-export for the channel-model layer.  Members:

* `OrbgrandAi.Section02.Basic` -- newtype primitives shared across
  the channel models: symbol index, block size, sampling frequency,
  noise power, complex amplitude.  Also the section-wide `ChannelError`
  sum type.
* `OrbgrandAi.Section02.LinearIsi` -- the underlying linear ISI
  model `Y = h * X + N` with the channel matrix indexed as
  `h_{k', j}` and the matricised form `Y^{n_s} = h^{n_s x n_s} X^{n_s} + N^{n_s}`.
* `OrbgrandAi.Section02.DelayTap` -- delay-tap channel profile with
  the `sinc`-kernel impulse response.
* `OrbgrandAi.Section02.Dicode` -- the two-tap dicode partial-response
  channel `(1, -rho, 0, ...)` and its zero-forcing equalisation into
  first-order Gauss-Markov noise.
* `OrbgrandAi.Section02.RFView` -- the RFView impulse-response
  channel `h_RFV`, including its 6-tap structure and the AR(2)
  approximation.
-/
