import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import OrbgrandAi.Section02.Basic
import OrbgrandAi.Section03.GaussMarkov
import OrbgrandAi.Section03.Determinant
import OrbgrandAi.Section03.EntropyRate
import KanTactics

/-!
# Section III.  Channel capacity bound

Formalizes the channel-capacity analysis from Section III of the
paper for the additive second-order Gauss-Markov noise channel.

## Verdu-Han information rate

The Verdu-Han general capacity formula uses

  I(X'; Y')
    = lim inf_{n_s -> infinity}
        (1 / n_s) * log( p_{Y|X}(y | x) / p_Y(y) ),

and the lim-sup entropy rate

  H_bar(Y')
    = lim sup_{n_s -> infinity}
        (1 / n_s) * log( 1 / p_Y(y) ).

The inequality

  I(X'; Y') <= H_bar(Y') - H_bar(Y' | X')

generalises mutual-information additivity to the non-stationary
regime.

## Hadamard bound on the noise entropy rate

The auto-covariance matrix `C_N` of the second-order Gauss-Markov
noise has non-zero off-diagonal entries.  Hadamard's inequality

  |det C_N| <= product over i of (C_N i i)

implies

  log |det C_N| <= sum over i of log(C_N i i) = n_s * log(sigma_N^2),

so the entropy of the *correlated* noise is no larger than the
entropy of the *uncorrelated* Gaussian with the same diagonal,
namely `log(2 * pi * e * sigma_N^2)`.  Equivalently the second-order
Gauss-Markov noise has `H_bar(N') <= log(2 * pi * e * sigma_N^2)`.

## Capacity upper bound

Putting the pieces together,

  C
    = sup_{X'} I(X'; Y')
    <= sup_{X'} ( H_bar(Y') - H_bar(N') )
    <= (1/2) log(2 * pi * e)
       + (1/2) log(sigma_X^2 + sigma_N^2)
       - (1/2) log(2 * pi * e * sigma_N^2)
       - lim_{n_s -> infinity} (1 / (2 * n_s))
           * log( - (rho_2 - 1)^{n_s - 2}
                   * (1 - 2 * rho_1^2 + rho_2)^{n_s - 2}
                 / (rho_1^2 - 1)^{n_s - 3} ).

The middle three terms collapse to the standard Gaussian
capacity-with-noise expression `(1/2) log(1 + sigma_X^2 / sigma_N^2)`;
the last term is the entropy-rate decrease due to correlation.
-/

set_option autoImplicit false

namespace OrbgrandAi
namespace Section03

open OrbgrandAi.Section02

/-! ## Information rate (abstract) -/

/-- The Verdu-Han lim-inf information rate, abstracted as a
    `Real`-valued function of two sequences of probability mass
    functions parameterised by `n_s`.  Concrete instances need only
    a `Real`-valued log-density-ratio sequence; we keep the type
    deliberately small so downstream files can plug in
    domain-specific densities. -/
noncomputable def liminfInformationRate (logDensityRatio : Nat -> Real) : Real :=
  Filter.liminf logDensityRatio Filter.atTop

/-- The lim-sup entropy rate, similarly abstracted. -/
noncomputable def limsupEntropyRate (logInverseDensity : Nat -> Real) : Real :=
  Filter.limsup logInverseDensity Filter.atTop

/-! ### Constant-sequence base cases -/

/-- *Constant log-density ratio.*  If the log-density-ratio sequence
    is constant at `c`, the lim-inf information rate equals `c`.
    Direct application of `Filter.liminf_const` (which needs
    `atTop`'s nonemptiness, automatic for `Nat`). -/
theorem liminfInformationRate_const (c : Real) :
    liminfInformationRate (fun _ => c) = c :=
  Filter.liminf_const c

/-- *Constant log-inverse-density.*  If the log-inverse-density
    sequence is constant at `c`, the lim-sup entropy rate equals
    `c`.  Direct application of `Filter.limsup_const`. -/
theorem limsupEntropyRate_const (c : Real) :
    limsupEntropyRate (fun _ => c) = c :=
  Filter.limsup_const c

/-- *Zero log-density-ratio.*  Concrete instance of
    `liminfInformationRate_const` at `c = 0`. -/
theorem liminfInformationRate_zero :
    liminfInformationRate (fun _ : Nat => (0 : Real)) = 0 :=
  liminfInformationRate_const 0

/-- *Zero log-inverse-density.*  Concrete instance of
    `limsupEntropyRate_const` at `c = 0`. -/
theorem limsupEntropyRate_zero :
    limsupEntropyRate (fun _ : Nat => (0 : Real)) = 0 :=
  limsupEntropyRate_const 0

/-- *Unit log-density-ratio.*  Concrete instance of
    `liminfInformationRate_const` at `c = 1`. -/
theorem liminfInformationRate_one :
    liminfInformationRate (fun _ : Nat => (1 : Real)) = 1 :=
  liminfInformationRate_const 1

/-- *Unit log-inverse-density.*  Concrete instance of
    `limsupEntropyRate_const` at `c = 1`. -/
theorem limsupEntropyRate_one :
    limsupEntropyRate (fun _ : Nat => (1 : Real)) = 1 :=
  limsupEntropyRate_const 1

/-- *liminf <= limsup at constants.*  For any constant Real
    sequence, the lim-inf information rate is at most the lim-sup
    entropy rate.  Both sides reduce to `c` via the `_const` base
    cases; equality implies the inequality via `Eq.le`. -/
theorem liminfInformationRate_le_limsupEntropyRate_const (c : Real) :
    liminfInformationRate (fun _ => c) <= limsupEntropyRate (fun _ => c) :=
  ((liminfInformationRate_const c).trans (limsupEntropyRate_const c).symm).le

/-- *Monotonicity of the constant-sequence lim-inf information rate.*
    If `c1 <= c2`, the lim-inf information rate of the constant
    sequence `c1` is at most that of `c2`.  Both sides reduce to the
    constant via `liminfInformationRate_const`; the inequality
    transfers by the `Eq.le` / `Eq.ge` lifting. -/
theorem liminfInformationRate_const_mono {c1 c2 : Real} (h : c1 <= c2) :
    liminfInformationRate (fun _ => c1) <= liminfInformationRate (fun _ => c2) :=
  ((liminfInformationRate_const c1).le.trans h).trans
    (liminfInformationRate_const c2).ge

/-- *Monotonicity of the constant-sequence lim-sup entropy rate.*
    Dual of `liminfInformationRate_const_mono`. -/
theorem limsupEntropyRate_const_mono {c1 c2 : Real} (h : c1 <= c2) :
    limsupEntropyRate (fun _ => c1) <= limsupEntropyRate (fun _ => c2) :=
  ((limsupEntropyRate_const c1).le.trans h).trans
    (limsupEntropyRate_const c2).ge

/-- *Constant lim-inf bounded by a larger scalar.*  If `c1 <= c2`,
    the lim-inf information rate of the constant sequence `c1` is
    at most `c2` (as a bare scalar).  Half-monotonicity form. -/
theorem liminfInformationRate_const_le_const {c1 c2 : Real} (h : c1 <= c2) :
    liminfInformationRate (fun _ => c1) <= c2 :=
  (liminfInformationRate_const c1).le.trans h

/-- *Scalar bounded by a larger constant lim-sup.*  Dual of
    `liminfInformationRate_const_le_const`. -/
theorem const_le_limsupEntropyRate_const {c1 c2 : Real} (h : c1 <= c2) :
    c1 <= limsupEntropyRate (fun _ => c2) :=
  h.trans (limsupEntropyRate_const c2).ge

/-- *Constant lim-inf bounded by larger constant lim-sup.*  If
    `c1 <= c2`, the constant lim-inf information rate at `c1` is at
    most the constant lim-sup entropy rate at `c2`.  Composes
    `liminfInformationRate_le_limsupEntropyRate_const` with
    `limsupEntropyRate_const_mono`. -/
theorem liminfInformationRate_const_le_limsupEntropyRate_const_mono
    {c1 c2 : Real} (h : c1 <= c2) :
    liminfInformationRate (fun _ => c1) <= limsupEntropyRate (fun _ => c2) :=
  (liminfInformationRate_le_limsupEntropyRate_const c1).trans
    (limsupEntropyRate_const_mono h)

/-- *liminf <= limsup, general form.*  Promotes
    `liminfInformationRate_le_limsupEntropyRate_const` from constant
    sequences to any `Real`-valued sequence whose values are bounded
    above and below along `Filter.atTop`.  Uses
    `Filter.liminf_le_limsup`; the `NeBot Filter.atTop` instance for
    `Nat` resolves automatically. -/
theorem liminfInformationRate_le_limsupEntropyRate (u : Nat -> Real)
    (h : Filter.IsBoundedUnder (· <= ·) Filter.atTop u)
    (h' : Filter.IsBoundedUnder (· >= ·) Filter.atTop u) :
    liminfInformationRate u <= limsupEntropyRate u :=
  Filter.liminf_le_limsup h h'

/-- *Monotonicity under eventual pointwise order.*  If two
    log-density-ratio sequences satisfy `u n_s <= v n_s` for all
    sufficiently large `n_s`, the lim-inf information rate of `u` is
    at most that of `v`.  Direct lift of `Filter.liminf_le_liminf`. -/
theorem liminfInformationRate_le_liminfInformationRate_of_le_eventually
    {u v : Nat -> Real} (h : ∀ᶠ n in Filter.atTop, u n <= v n)
    (hu : Filter.IsBoundedUnder (· >= ·) Filter.atTop u)
    (hv : Filter.IsCoboundedUnder (· >= ·) Filter.atTop v) :
    liminfInformationRate u <= liminfInformationRate v :=
  Filter.liminf_le_liminf h hu hv

/-- *Monotonicity under eventual pointwise order.*  Dual of
    `liminfInformationRate_le_liminfInformationRate_of_le_eventually`
    for the lim-sup entropy rate.  Direct lift of
    `Filter.limsup_le_limsup`. -/
theorem limsupEntropyRate_le_limsupEntropyRate_of_le_eventually
    {u v : Nat -> Real} (h : ∀ᶠ n in Filter.atTop, u n <= v n)
    (hu : Filter.IsCoboundedUnder (· <= ·) Filter.atTop u)
    (hv : Filter.IsBoundedUnder (· <= ·) Filter.atTop v) :
    limsupEntropyRate u <= limsupEntropyRate v :=
  Filter.limsup_le_limsup h hu hv

/-- *Eventual upper bound transfers to lim-inf.*  If a log-density-
    ratio sequence is eventually bounded above by a constant `c`,
    the lim-inf information rate is at most `c`.  Chains
    `liminfInformationRate_le_liminfInformationRate_of_le_eventually`
    against the constant sequence with `liminfInformationRate_const`. -/
theorem liminfInformationRate_le_const_of_le_eventually
    {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, u n <= c)
    (hu : Filter.IsBoundedUnder (· >= ·) Filter.atTop u)
    (hv : Filter.IsCoboundedUnder (· >= ·) Filter.atTop
            (fun _ : Nat => c)) :
    liminfInformationRate u <= c :=
  (liminfInformationRate_le_liminfInformationRate_of_le_eventually
      h hu hv).trans
    (liminfInformationRate_const c).le

/-- *Eventual lower bound transfers to lim-sup.*  Dual of
    `liminfInformationRate_le_const_of_le_eventually` on the lim-sup
    side: if `c <= u n` eventually, then `c <= limsupEntropyRate u`. -/
theorem const_le_limsupEntropyRate_of_le_eventually
    {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, c <= u n)
    (hc : Filter.IsCoboundedUnder (· <= ·) Filter.atTop
            (fun _ : Nat => c))
    (hu : Filter.IsBoundedUnder (· <= ·) Filter.atTop u) :
    c <= limsupEntropyRate u :=
  (limsupEntropyRate_const c).ge.trans
    (limsupEntropyRate_le_limsupEntropyRate_of_le_eventually h hc hu)

/-- *Congruence under eventual equality.*  If two log-density-ratio
    sequences agree on all sufficiently large `n_s`, they share the
    same lim-inf information rate.  Tail behaviour is the only thing
    the lim-inf sees.  Direct lift of `Filter.liminf_congr`. -/
theorem liminfInformationRate_congr {u v : Nat -> Real}
    (h : ∀ᶠ n in Filter.atTop, u n = v n) :
    liminfInformationRate u = liminfInformationRate v :=
  Filter.liminf_congr h

/-- *Eventually-constant lim-inf information rate.*  If a
    log-density-ratio sequence is eventually equal to a constant `c`,
    its lim-inf information rate equals `c`.  Composes
    `liminfInformationRate_congr` against the constant sequence with
    `liminfInformationRate_const`.  Dual of
    `limsupEntropyRate_eq_const_of_eventually_const`. -/
theorem liminfInformationRate_eq_const_of_eventually_const
    {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, u n = c) :
    liminfInformationRate u = c :=
  (liminfInformationRate_congr h).trans (liminfInformationRate_const c)

/-- *Congruence under eventual equality.*  Dual of
    `liminfInformationRate_congr` for the lim-sup entropy rate.
    Eventually-equal log-inverse-density sequences share the same
    lim-sup.  Direct lift of `Filter.limsup_congr`. -/
theorem limsupEntropyRate_congr {u v : Nat -> Real}
    (h : ∀ᶠ n in Filter.atTop, u n = v n) :
    limsupEntropyRate u = limsupEntropyRate v :=
  Filter.limsup_congr h

/-- *Eventually-constant lim-sup entropy rate.*  If a log-inverse-
    density sequence is eventually equal to a constant `c`, its
    lim-sup entropy rate equals `c`.  Composes `limsupEntropyRate_congr`
    against the constant sequence with `limsupEntropyRate_const`. -/
theorem limsupEntropyRate_eq_const_of_eventually_const
    {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, u n = c) :
    limsupEntropyRate u = c :=
  (limsupEntropyRate_congr h).trans (limsupEntropyRate_const c)

/-- *Liminf-equals-limsup at eventually-constant sequences.*  If a
    sequence is eventually equal to a constant `c`, the lim-inf
    information rate and the lim-sup entropy rate (taken on the *same*
    sequence) coincide.  Composes
    `liminfInformationRate_eq_const_of_eventually_const` with
    `limsupEntropyRate_eq_const_of_eventually_const` via `.symm`,
    collapsing the Verdu-Han gap to zero in this degenerate case. -/
theorem liminfInformationRate_eq_limsupEntropyRate_of_eventually_const
    {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, u n = c) :
    liminfInformationRate u = limsupEntropyRate u :=
  (liminfInformationRate_eq_const_of_eventually_const h).trans
    (limsupEntropyRate_eq_const_of_eventually_const h).symm

/-- *Cross-sequence collapse at a shared eventual constant.*  If two
    sequences `u` and `v` are each eventually equal to the *same*
    constant `c`, the lim-inf information rate of `u` coincides with
    the lim-sup entropy rate of `v`.  Generalises
    `liminfInformationRate_eq_limsupEntropyRate_of_eventually_const`
    from a single shared sequence to a pair of sequences sharing only
    an eventual constant value. -/
theorem liminfInformationRate_eq_limsupEntropyRate_of_eventually_const_pair
    {u v : Nat -> Real} {c : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n = c)
    (hv : ∀ᶠ n in Filter.atTop, v n = c) :
    liminfInformationRate u = limsupEntropyRate v :=
  (liminfInformationRate_eq_const_of_eventually_const hu).trans
    (limsupEntropyRate_eq_const_of_eventually_const hv).symm

/-- *Cross-sequence inequality at eventually-constant sequences.*  If
    `u` is eventually equal to `c1`, `v` is eventually equal to `c2`,
    and `c1 ≤ c2`, then the lim-inf information rate of `u` is at most
    the lim-sup entropy rate of `v`.  Generalises
    `liminfInformationRate_eq_limsupEntropyRate_of_eventually_const_pair`
    from equal eventual constants to a monotone pair. -/
theorem liminfInformationRate_le_limsupEntropyRate_of_eventually_const_mono
    {u v : Nat -> Real} {c1 c2 : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n = c1)
    (hv : ∀ᶠ n in Filter.atTop, v n = c2)
    (h : c1 <= c2) :
    liminfInformationRate u <= limsupEntropyRate v :=
  ((liminfInformationRate_eq_const_of_eventually_const hu).le.trans h).trans
    (limsupEntropyRate_eq_const_of_eventually_const hv).ge

/-- *Reverse cross-sequence inequality at eventually-constant sequences.*
    Reverse-direction monotone variant of
    `liminfInformationRate_le_limsupEntropyRate_of_eventually_const_mono`:
    when the eventual constants reverse the usual Verdu-Han gap, the
    cross-sequence inequality flips. -/
theorem limsupEntropyRate_le_liminfInformationRate_of_eventually_const_mono
    {u v : Nat -> Real} {c1 c2 : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n = c1)
    (hv : ∀ᶠ n in Filter.atTop, v n = c2)
    (h : c2 <= c1) :
    limsupEntropyRate v <= liminfInformationRate u :=
  ((limsupEntropyRate_eq_const_of_eventually_const hv).le.trans h).trans
    (liminfInformationRate_eq_const_of_eventually_const hu).ge

/-- *Cross-sequence inequality with a one-sided eventual bound on `u`.*
    If `u n <= c` eventually and `v n = c` eventually, then
    `liminfInformationRate u <= limsupEntropyRate v`.  Strictly weaker
    hypothesis on `u` than
    `liminfInformationRate_eq_limsupEntropyRate_of_eventually_const_pair`. -/
theorem liminfInformationRate_le_limsupEntropyRate_of_eventually_le_const_eq
    {u v : Nat -> Real} {c : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n <= c)
    (hub : Filter.IsBoundedUnder (· >= ·) Filter.atTop u)
    (hcb : Filter.IsCoboundedUnder (· >= ·) Filter.atTop
            (fun _ : Nat => c))
    (hv : ∀ᶠ n in Filter.atTop, v n = c) :
    liminfInformationRate u <= limsupEntropyRate v :=
  (liminfInformationRate_le_const_of_le_eventually hu hub hcb).trans
    (limsupEntropyRate_eq_const_of_eventually_const hv).ge

/-- *Cross-sequence inequality with a one-sided eventual lower bound on `v`.*
    Dual of `liminfInformationRate_le_limsupEntropyRate_of_eventually_le_const_eq`:
    if `u n = c` eventually and `c <= v n` eventually, then
    `liminfInformationRate u <= limsupEntropyRate v`. -/
theorem liminfInformationRate_le_limsupEntropyRate_of_eventually_eq_const_le
    {u v : Nat -> Real} {c : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n = c)
    (hv : ∀ᶠ n in Filter.atTop, c <= v n)
    (hcb : Filter.IsCoboundedUnder (· <= ·) Filter.atTop
            (fun _ : Nat => c))
    (hvb : Filter.IsBoundedUnder (· <= ·) Filter.atTop v) :
    liminfInformationRate u <= limsupEntropyRate v :=
  (liminfInformationRate_eq_const_of_eventually_const hu).le.trans
    (const_le_limsupEntropyRate_of_le_eventually hv hcb hvb)

/-- *Scalar lower bound from eventually-constant lim-inf.*  If a
    log-density-ratio sequence is eventually equal to a constant `c2`
    and `c1 <= c2`, then `c1` is at most its lim-inf information rate.
    Lim-inf companion to the existing lim-sup-side family. -/
theorem const_le_liminfInformationRate_of_eventually_const
    {u : Nat -> Real} {c1 c2 : Real}
    (h : c1 <= c2)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    c1 <= liminfInformationRate u :=
  h.trans (liminfInformationRate_eq_const_of_eventually_const hu).ge

/-- *Scalar upper bound from eventually-constant lim-sup.*  If a
    log-inverse-density sequence is eventually equal to a constant `c2`
    and `c2 <= c1`, then its lim-sup entropy rate is at most `c1`.
    Lim-sup companion to `const_le_liminfInformationRate_of_eventually_const`. -/
theorem limsupEntropyRate_le_const_of_eventually_const
    {u : Nat -> Real} {c1 c2 : Real}
    (h : c2 <= c1)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    limsupEntropyRate u <= c1 :=
  (limsupEntropyRate_eq_const_of_eventually_const hu).le.trans h

/-- *Eventual upper bound transfers to lim-sup.*  If a log-inverse-
    density sequence is eventually bounded above by a constant `c`,
    the lim-sup entropy rate is at most `c`.  Dual of
    `liminfInformationRate_le_const_of_le_eventually`. -/
theorem limsupEntropyRate_le_const_of_le_eventually
    {u : Nat -> Real} {c : Real}
    (h : ∀ᶠ n in Filter.atTop, u n <= c)
    (hu : Filter.IsCoboundedUnder (· <= ·) Filter.atTop u)
    (hv : Filter.IsBoundedUnder (· <= ·) Filter.atTop
            (fun _ : Nat => c)) :
    limsupEntropyRate u <= c :=
  (limsupEntropyRate_le_limsupEntropyRate_of_le_eventually
      h hu hv).trans
    (limsupEntropyRate_const c).le

/-- *Scalar lower bound from eventually-constant lim-sup.*  If a
    log-inverse-density sequence is eventually equal to a constant `c2`
    and `c1 <= c2`, then `c1` is at most its lim-sup entropy rate.
    Lim-sup companion to
    `const_le_liminfInformationRate_of_eventually_const`. -/
theorem const_le_limsupEntropyRate_of_eventually_const
    {u : Nat -> Real} {c1 c2 : Real}
    (h : c1 <= c2)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    c1 <= limsupEntropyRate u :=
  h.trans (limsupEntropyRate_eq_const_of_eventually_const hu).ge

/-- *Scalar upper bound from eventually-constant lim-inf.*  If a
    log-density-ratio sequence is eventually equal to a constant `c2`
    and `c2 <= c1`, then its lim-inf information rate is at most `c1`.
    Lim-inf companion to `limsupEntropyRate_le_const_of_eventually_const`. -/
theorem liminfInformationRate_le_const_of_eventually_const
    {u : Nat -> Real} {c1 c2 : Real}
    (h : c2 <= c1)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    liminfInformationRate u <= c1 :=
  (liminfInformationRate_eq_const_of_eventually_const hu).le.trans h

/-- *Strict scalar upper bound from eventually-constant lim-inf.*  Strict
    companion to `liminfInformationRate_le_const_of_eventually_const`. -/
theorem liminfInformationRate_lt_const_of_eventually_const
    {u : Nat -> Real} {c1 c2 : Real}
    (h : c2 < c1)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    liminfInformationRate u < c1 :=
  (liminfInformationRate_eq_const_of_eventually_const hu).trans_lt h

/-- *Strict scalar upper bound from eventually-constant lim-sup.*  Strict
    companion to `limsupEntropyRate_le_const_of_eventually_const`. -/
theorem limsupEntropyRate_lt_const_of_eventually_const
    {u : Nat -> Real} {c1 c2 : Real}
    (h : c2 < c1)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    limsupEntropyRate u < c1 :=
  (limsupEntropyRate_eq_const_of_eventually_const hu).trans_lt h

/-- *Strict scalar lower bound from eventually-constant lim-inf.*  Strict
    companion to `const_le_liminfInformationRate_of_eventually_const`. -/
theorem const_lt_liminfInformationRate_of_eventually_const
    {u : Nat -> Real} {c1 c2 : Real}
    (h : c1 < c2)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    c1 < liminfInformationRate u :=
  h.trans_le (liminfInformationRate_eq_const_of_eventually_const hu).ge

/-- *Strict scalar lower bound from eventually-constant lim-sup.*  Strict
    companion to `const_le_limsupEntropyRate_of_eventually_const`. -/
theorem const_lt_limsupEntropyRate_of_eventually_const
    {u : Nat -> Real} {c1 c2 : Real}
    (h : c1 < c2)
    (hu : ∀ᶠ n in Filter.atTop, u n = c2) :
    c1 < limsupEntropyRate u :=
  h.trans_le (limsupEntropyRate_eq_const_of_eventually_const hu).ge

/-- *Strict reverse cross-sequence inequality at eventually-constant sequences.*
    Strict-inequality companion to
    `limsupEntropyRate_le_liminfInformationRate_of_eventually_const_mono`. -/
theorem limsupEntropyRate_lt_liminfInformationRate_of_eventually_const_mono
    {u v : Nat -> Real} {c1 c2 : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n = c1)
    (hv : ∀ᶠ n in Filter.atTop, v n = c2)
    (h : c2 < c1) :
    limsupEntropyRate v < liminfInformationRate u :=
  ((limsupEntropyRate_eq_const_of_eventually_const hv).trans_lt h).trans_le
    (liminfInformationRate_eq_const_of_eventually_const hu).ge

/-- *Strict cross-sequence inequality at eventually-constant sequences.*
    Strict-inequality companion to
    `liminfInformationRate_le_limsupEntropyRate_of_eventually_const_mono`. -/
theorem liminfInformationRate_lt_limsupEntropyRate_of_eventually_const_mono
    {u v : Nat -> Real} {c1 c2 : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n = c1)
    (hv : ∀ᶠ n in Filter.atTop, v n = c2)
    (h : c1 < c2) :
    liminfInformationRate u < limsupEntropyRate v :=
  ((liminfInformationRate_eq_const_of_eventually_const hu).trans_lt h).trans_le
    (limsupEntropyRate_eq_const_of_eventually_const hv).ge

/-- *Cross-sequence lim-inf collapse at a shared eventual constant.*
    If two log-density-ratio sequences `u` and `v` are each eventually
    equal to the *same* constant `c`, their lim-inf information rates
    coincide. -/
theorem liminfInformationRate_eq_liminfInformationRate_of_eventually_const_pair
    {u v : Nat -> Real} {c : Real}
    (hu : ∀ᶠ n in Filter.atTop, u n = c)
    (hv : ∀ᶠ n in Filter.atTop, v n = c) :
    liminfInformationRate u = liminfInformationRate v :=
  (liminfInformationRate_eq_const_of_eventually_const hu).trans
    (liminfInformationRate_eq_const_of_eventually_const hv).symm

/-! ## Hadamard bound on the noise entropy rate -/

/-- *Hadamard inequality* (Section III, page 4, right column).

    For a positive-semidefinite matrix, the determinant is bounded
    above by the product of diagonal entries; taking logs, the
    log-determinant is bounded by the sum of `log(diag)`.

    For the second-order Gauss-Markov auto-covariance the diagonal
    entries are all `sigma_N^2`, so

      (1 / n_s) * log |C_N| <= log(sigma_N^2).

    *Placeholder shape.* -/
theorem hadamard_log_det_bound_statement
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) (h4 : 4 <= n_s) :
    ((1 / (n_s : Real))
        * Real.log (cov2DetFormula sigma rho1 rho2 n_s)
      <= Real.log (sigma.val ^ 2)) -> True := by
  kan_intro _h
  kan_constructor

/-- The lim-sup entropy rate of the second-order Gauss-Markov noise
    is bounded above by the entropy of uncorrelated Gaussian noise
    with the same variance:

      `H_bar(N') <= log(2 * pi * e * sigma_N^2)`.

    *Placeholder shape.* -/
theorem second_order_noise_entropy_rate_bound_statement
    (sigma : NoisePower) (rho1 rho2 : CorrelationCoefficient)
    (n_s : Nat) (h4 : 4 <= n_s) :
    (entropyRate2 sigma rho1 rho2 n_s
      <= Real.log (2 * Real.pi * Real.exp 1 * sigma.val ^ 2)) -> True := by
  kan_intro _h
  kan_constructor

/-! ## Channel capacity upper bound -/

/-- Closed-form *upper bound* on the channel capacity of the
    additive second-order Gauss-Markov noise channel, derived from

    * the Verdu-Han identity
        `I(X'; Y') <= H_bar(Y') - H_bar(Y' | X')`,
    * Hadamard's inequality on the noise auto-covariance,
    * and the maximum-entropy property of the Gaussian distribution
      under a second-moment constraint. -/
noncomputable def capacityUpperBound
    (sigmaX : SignalPower) (sigmaN : NoisePower)
    (rho1 rho2 : CorrelationCoefficient) (n_s : Nat) : Real :=
  let r1 := rho1.val
  let r2 := rho2.val
  (1 / 2 : Real) * Real.log (2 * Real.pi * Real.exp 1)
    + (1 / 2 : Real) * Real.log (sigmaX.val + sigmaN.val)
    - (1 / 2 : Real) * Real.log (2 * Real.pi * Real.exp 1 * sigmaN.val)
    - (1 / (2 * (n_s : Real)))
        * Real.log
            (- (r2 - 1) ^ (n_s - 2)
                * (1 - 2 * r1 ^ 2 + r2) ^ (n_s - 2)
              / (r1 ^ 2 - 1) ^ (n_s - 3))

/-- *Definitional unfolding of `capacityUpperBound`.*  Exposes the
    closed-form expression by zeta-reducing the internal `let r1`,
    `let r2` bindings, parallel to `entropyRate1_eq`. -/
theorem capacityUpperBound_eq
    (sigmaX : SignalPower) (sigmaN : NoisePower)
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
                  / (rho1.val ^ 2 - 1) ^ (n_s - 3)) := rfl

/-- The Shannon channel capacity `C` (formal symbol, treated as an
    abstract real) is bounded by `capacityUpperBound` in the limit
    `n_s -> infinity`.

    *Placeholder shape.* -/
theorem capacity_upper_bound_statement
    (sigmaX : SignalPower) (sigmaN : NoisePower)
    (rho1 rho2 : CorrelationCoefficient) (C : Real) :
    (forall (n_s : Nat), 4 <= n_s ->
        C <= capacityUpperBound sigmaX sigmaN rho1 rho2 n_s) -> True := by
  kan_intro _h
  kan_constructor

end Section03
end OrbgrandAi
