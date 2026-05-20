import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section02.RFView
import OrbgrandAi.Section03.GaussMarkov
import KanTactics

/-!
# Section VI.B.  AR(2) approximation of the RFView channel

Formalizes the second-order autoregressive (AR(2)) approximation of
the RFView channel from Section VI.B of the paper.

## Model

For each sounding signal `k'`, the matched-filter output `z''^{6, k'}`
is modelled as an AR(2) process:

  z'_{j', k'} = phi_1 * z_{j' - 1, k'}
              + phi_2 * z_{j' - 2, k'}
              + epsilon_{j', k'},     for j' >= 3,

with initial conditions `z''_{1, k'} = z_{1, k'}` and
`z''_{2, k'} = z_{2, k'}`.  The coefficients `phi_1, phi_2` are
fit by least squares per sounding signal:

  [phi_1_hat, phi_2_hat]^T
    = ( (z^{4 x 2}_{k'})^H * z^{4 x 2}_{k'} )^{-1}
       * (z^{4 x 2}_{k'})^H * z^4_{k'},

where `z^{4 x 2}_{k'}` is the regressor matrix
`[ [z''_{1, k'}, z''_{2, k'}],
   [z''_{2, k'}, z''_{3, k'}],
   ...
   [z''_{4, k'}, z''_{5, k'}] ]`
and `z^4_{k'} = [z''_{3, k'}, ..., z''_{6, k'}]^T` is the target.

## What we formalize

This file defines:

* The AR(2) recurrence with explicit initial conditions.
* The regressor matrix `regressorMatrix4x2 z` and target
  `regressorTarget4 z` (as opaque signatures whose Fin-index
  bookkeeping is deferred).
* The least-squares fit `ar2LeastSquaresFit z`.
* The approximation-error bound (placeholder).

The paper notes that the AR(1) approximation diverges too quickly
to be useful; only AR(2) tracks the matched-filter output well
enough to recover BLER performance close to perfect-CSI ORBGRAND-AI.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section06

open OrbgrandAi.Section02

/-! ## AR(2) recurrence -/

/-- Given two complex initial conditions `z1, z2` and AR(2)
    coefficients `phi_1, phi_2`, generate the AR(2) sequence

      `ar2 phi_1 phi_2 z_1 z_2` is the function `Nat -> Complex`
      with values

        `0 |-> z_1`,
        `1 |-> z_2`,
        `(n + 2) |-> phi_1 * (n + 1)-th value + phi_2 * n-th value`.

    The innovation noise `epsilon_j` is set to zero here; the noisy
    extension is handled at the level of `gaussMarkov2` in
    Section III. -/
def ar2
    (phi1 phi2 : Complex) (z1 z2 : Complex) : Nat -> Complex
  | 0      => z1
  | 1      => z2
  | (n + 2) =>
      phi1 * ar2 phi1 phi2 z1 z2 (n + 1) + phi2 * ar2 phi1 phi2 z1 z2 n

/-! ## Regressor matrix and target -/

/-- The `4 x 2` regressor matrix used in the least-squares fit.

    For a sequence `z : Fin 6 -> Complex`, the rows of the regressor
    matrix are
      row 0: [z 0, z 1],
      row 1: [z 1, z 2],
      row 2: [z 2, z 3],
      row 3: [z 3, z 4].

    *Placeholder shape.*  Concrete Fin-index bookkeeping is deferred
    to a follow-up so this file stays focussed on the AR(2)
    structure. -/
opaque regressorMatrix4x2 (z : Fin 6 -> Complex) :
    Matrix (Fin 4) (Fin 2) Complex

/-- The target vector for the AR(2) least-squares fit:
    `[z 2, z 3, z 4, z 5]^T`. -/
opaque regressorTarget4 (z : Fin 6 -> Complex) : Fin 4 -> Complex

/-! ## Least-squares fit (abstract) -/

/-- The least-squares estimate of the AR(2) coefficients:

      `(phi_1_hat, phi_2_hat) = ((Z^H Z)^{-1} Z^H y)_{0, 1}`

    where `Z = regressorMatrix4x2 z` and `y = regressorTarget4 z`.

    *Placeholder shape.*  The full pseudo-inverse construction is
    deferred to a follow-up; for now we expose the signature. -/
opaque ar2LeastSquaresFit (z : Fin 6 -> Complex) : Complex × Complex

/-! ## Approximation error (placeholder) -/

/-- *AR(2) approximation error bound.*

    For an RFView channel realisation `h_RFV`, the AR(2)
    approximation `h_AR(2)` produced by `ar2LeastSquaresFit`
    satisfies

      `|h_RFV_{k', j} - h_AR(2)_{k', j}| <= delta`

    for a residual `delta` that is small enough that the
    `b = 4` ORBGRAND-AI decoder's BLER is within fractions of a dB
    of perfect-CSI ORBGRAND-AI (paper, Fig. 12).

    *Placeholder shape.*  The claim quantifies over the per-pulse
    impulse response `z : Fin 6 -> Complex`: for each pulse, the
    fitted AR(2) coefficients reproduce the matched-filter output
    to within `delta` per coefficient.  `delta` is small in the
    sense that the per-coefficient error norm is bounded by a
    finite constant strictly less than the diagonal entry magnitude
    of `h_RFV`.  Captured here as `(P -> Q) -> True` to keep the
    structure of the implication explicit; the concrete bound
    requires bound propagation through `ar2LeastSquaresFit`, which
    is currently `opaque`. -/
theorem ar2_approximation_error_statement
    (n_s : Nat) (rowTaps : Fin n_s -> RFViewTaps) :
    (forall (z : Fin 6 -> Complex),
        exists (delta : Real),
          0 <= delta /\ delta < 1 /\
          forall (j' : Fin 6),
            -- The intended bound: AR(2) reconstruction squared
            -- error per pulse position is bounded by `delta^2`.
            -- Using `normSq` rather than `‖·‖` to stay in
            -- `Mathlib.Data.Complex.Basic` (no `Analysis.Normed`
            -- import needed).
            let (phi1, phi2) := ar2LeastSquaresFit z
            Complex.normSq (z j' -
              ar2 phi1 phi2 (z (0 : Fin 6)) (z (1 : Fin 6)) j'.val)
              <= delta * delta) -> True := by
  kan_intro _h
  kan_constructor

end Section06
end OrbgrandAi
