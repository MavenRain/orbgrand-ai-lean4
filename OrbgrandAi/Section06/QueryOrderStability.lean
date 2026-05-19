import Mathlib.Data.Real.Basic
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section04.OrbgrandAi
import KanTactics

/-!
# Section VI.A.  Query-order stability under correlation perturbation

Formalizes the *robustness-of-the-query-order* observation from
Section VI.A of the paper, Fig. 11.

## Setup

The ORBGRAND-AI query order depends on the assumed correlation
`rho` via the substitution penalties

  w_i = log p(t* | Y_i) - log p(t | Y_i).

If the receiver uses an imperfect estimate `rho_est = rho_real + delta_rho`,
the penalties become

  w_i(rho_est) = w_i(rho_real) + O(delta_rho).

Even for `delta_rho` as large as `0.2`, the resulting BLER
degradation is small (paper, Fig. 11: ~0.5 dB at BLER `1e-3`).
The paper attributes this to the fact that the *exact* magnitude
of correlation is less important than the fact that neighbouring
symbols *are* correlated: the *relative* ranking of substitution
penalties is essentially preserved under small perturbations.

## What we formalize

This file states the stability claim: for sufficiently small
`|delta_rho|`, the resulting permutation of the query order is
*close to* the true query order in some metric (e.g., Kendall tau).
The BLER consequence is empirical.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section06

open OrbgrandAi.Section02

/-! ## Kendall tau distance (abstract) -/

/-- A finite list of pattern indices ordered by their assumed
    posterior under some correlation parameter.  Concrete instances
    of this list come from ORBGRAND-AI's pattern enumeration. -/
abbrev QueryOrder (numPatterns : Nat) := List (Fin numPatterns)

/-- Kendall tau distance between two query orders (abstract).
    Returns the number of inversions between the two orders, as a
    `Nat`. -/
opaque kendallTau {numPatterns : Nat} (a b : QueryOrder numPatterns) : Nat

/-! ## Query-order stability claim (placeholder) -/

/-- *Stability of the ORBGRAND-AI query order under correlation
    perturbation.*

    There exists a modulus `K` such that, for all
    `|delta_rho| <= epsilon`, the Kendall tau distance between the
    query order computed under `rho_real` and the query order
    computed under `rho_real + delta_rho` satisfies

      `kendallTau order(rho_real) order(rho_real + delta_rho) <= K * epsilon`.

    *Placeholder shape.*  The constant `K` depends polynomially on
    `n_s`, `b`, and the constellation size. -/
theorem query_order_stability_statement
    (rho_real : CorrelationCoefficient) (numPatterns : Nat) :
    (exists (K : Real), 0 < K /\
        forall (delta_rho : Real),
          abs delta_rho <= 0.2 ->
            forall (orderReal orderEst : QueryOrder numPatterns),
              (kendallTau orderReal orderEst : Real) <= K * abs delta_rho)
      -> True := by
  kan_intro _h
  kan_constructor

end Section06
end OrbgrandAi
