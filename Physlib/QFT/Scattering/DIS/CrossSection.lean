/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The leading-order neutral-current DIS cross section

The inclusive differential cross section for `e p → e X` through single photon exchange,

$$\frac{d^2\sigma}{dx\,dQ^2}
  = \frac{4\pi\alpha^2}{x\,Q^4}\Bigl[(1-y)\,F_2 + x y^2 F_1\Bigr].$$

With the Callan–Gross relation `F₂ = 2x F₁` — equivalently a vanishing longitudinal structure
function, which is exactly the leading-order statement — the bracket collapses onto `F₂` times
a function of the inelasticity alone:

$$(1-y) F_2 + x y^2 F_1 = F_2\Bigl(1 - y + \tfrac{y^2}{2}\Bigr).$$

That function is `yFactor` below.  Writing it this way is not cosmetic: `yFactor` is *strictly
positive for every real `y`*, with no kinematic hypothesis at all, which is what makes the
positivity of the cross section reduce to the positivity of `F₂`.  `yFactor_pos` proves it by
completing the square, and `two_mul_yFactor` recovers the `1 + (1-y)²` form usually quoted.

## Why this file is at the `ℝ` level

The generator samples this distribution in `Float` (`Physlib.Generator.CrossSection`).  The
plan's Phase 1 asks for "specification lemmas against the existing `ℝ` definitions", while §6
rules out anything needing a proved `Float`↔`ℝ` bridge; those two pull in opposite directions.
The resolution taken here is to put **all the provable content at the `ℝ` level**, where
positivity, the Callan–Gross reduction and the conventional-form identity are ordinary
theorems, and to let the `Float` layer be an explicitly-unproved transcription of these
definitions.  Nothing is claimed about the transcription beyond its being one.

## Scope

Single photon exchange only.  No `Z` exchange and hence no parity violation, no `γ`–`Z`
interference, and no charged-current process; at the reference configuration of the generator
plan (`√s = 60 GeV`, `Q² ≲ 10³ GeV²`) the `Z` contribution is a per-mille-level correction, but
it is a real omission and not an approximation that improves with statistics.
-/

@[expose] public section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS

open scoped BigOperators

/-- The inelasticity factor `1 - y + y²/2` appearing in the leading-order neutral-current
cross section once Callan–Gross has been used. -/
noncomputable def yFactor (y : ℝ) : ℝ := 1 - y + y ^ 2 / 2

/-- `yFactor` is a shifted square: `1 - y + y²/2 = ((y-1)² + 1)/2`. -/
lemma yFactor_eq_sq (y : ℝ) : yFactor y = ((y - 1) ^ 2 + 1) / 2 := by
  unfold yFactor; ring

/-- **The inelasticity factor is strictly positive for every real `y`.**

No kinematic hypothesis is needed — not even `0 ≤ y ≤ 1`.  This is what reduces positivity of
the cross section to positivity of `F₂`. -/
lemma yFactor_pos (y : ℝ) : 0 < yFactor y := by
  rw [yFactor_eq_sq]
  positivity

/-- `yFactor` is bounded below by `1/2`, attained at `y = 1`. -/
lemma yFactor_ge_half (y : ℝ) : 1 / 2 ≤ yFactor y := by
  rw [yFactor_eq_sq]
  have h : (0 : ℝ) ≤ (y - 1) ^ 2 := sq_nonneg _
  linarith

/-- The conventional form: `2(1 - y + y²/2) = 1 + (1-y)²`. -/
lemma two_mul_yFactor (y : ℝ) : 2 * yFactor y = 1 + (1 - y) ^ 2 := by
  unfold yFactor; ring

/-- The leading-order neutral-current differential cross section `d²σ/(dx dQ²)`,
in terms of the electromagnetic coupling `α`, the Bjorken variable `x`, the hard scale `Q²`,
the inelasticity `y`, and the structure function value `F₂ = F2`. -/
noncomputable def loNCdSigma (α x Q2 y F2 : ℝ) : ℝ :=
  4 * Real.pi * α ^ 2 / (x * Q2 ^ 2) * F2 * yFactor y

/-- The same cross section in the form usually quoted, with `1 + (1-y)²` and a factor `2π`. -/
lemma loNCdSigma_eq_conventional (α x Q2 y F2 : ℝ) :
    loNCdSigma α x Q2 y F2
      = 2 * Real.pi * α ^ 2 / (x * Q2 ^ 2) * F2 * (1 + (1 - y) ^ 2) := by
  unfold loNCdSigma
  rw [← two_mul_yFactor]
  ring

/-- **The cross section is non-negative wherever `F₂` is.**

The only hypotheses are that the kinematic point is in the physical region (`0 < x`, `0 < Q²`)
and that the structure function is non-negative; no constraint on `y` is required, by
`yFactor_pos`. -/
lemma loNCdSigma_nonneg {α x Q2 y F2 : ℝ} (hx : 0 < x) (hQ : 0 < Q2) (hF : 0 ≤ F2) :
    0 ≤ loNCdSigma α x Q2 y F2 := by
  unfold loNCdSigma
  have hy : 0 < yFactor y := yFactor_pos y
  have hden : 0 < x * Q2 ^ 2 := by positivity
  have hpre : 0 ≤ 4 * Real.pi * α ^ 2 / (x * Q2 ^ 2) := by positivity
  have : 0 ≤ 4 * Real.pi * α ^ 2 / (x * Q2 ^ 2) * F2 := mul_nonneg hpre hF
  exact mul_nonneg this hy.le

/-- Strict positivity, when the coupling and the structure function are strictly positive. -/
lemma loNCdSigma_pos {α x Q2 y F2 : ℝ} (hα : α ≠ 0) (hx : 0 < x) (hQ : 0 < Q2) (hF : 0 < F2) :
    0 < loNCdSigma α x Q2 y F2 := by
  unfold loNCdSigma
  have hy : 0 < yFactor y := yFactor_pos y
  have hα2 : 0 < α ^ 2 := by positivity
  have hpre : 0 < 4 * Real.pi * α ^ 2 / (x * Q2 ^ 2) := by positivity
  exact mul_pos (mul_pos hpre hF) hy

/-- The leading-order structure function `F₂ = x ∑_f e_f² (f + f̄)`, as a flavour sum over
charge-weighted parton densities.  `q f x Q2` is understood to be the *sum* of the quark and
antiquark densities of flavour `f`. -/
noncomputable def f2LO {Flavor : Type} [Fintype Flavor]
    (charge : Flavor → ℝ) (q : Flavor → ℝ → ℝ → ℝ) (x Q2 : ℝ) : ℝ :=
  x * ∑ f, (charge f) ^ 2 * q f x Q2

/-- `F₂` is non-negative wherever the parton densities are, which with `loNCdSigma_nonneg`
gives a non-negative cross section. -/
lemma f2LO_nonneg {Flavor : Type} [Fintype Flavor]
    (charge : Flavor → ℝ) {q : Flavor → ℝ → ℝ → ℝ} {x Q2 : ℝ}
    (hx : 0 ≤ x) (hq : ∀ f, 0 ≤ q f x Q2) : 0 ≤ f2LO charge q x Q2 := by
  unfold f2LO
  refine mul_nonneg hx (Finset.sum_nonneg fun f _ => ?_)
  exact mul_nonneg (sq_nonneg _) (hq f)

/-- The cross section built from leading-order parton densities is non-negative on the
physical region. -/
lemma loNCdSigma_f2LO_nonneg {Flavor : Type} [Fintype Flavor]
    {α x Q2 y : ℝ} (charge : Flavor → ℝ) {q : Flavor → ℝ → ℝ → ℝ}
    (hx : 0 < x) (hQ : 0 < Q2) (hq : ∀ f, 0 ≤ q f x Q2) :
    0 ≤ loNCdSigma α x Q2 y (f2LO charge q x Q2) :=
  loNCdSigma_nonneg hx hQ (f2LO_nonneg charge hx.le hq)

end DIS
end Scattering
end QFT
end Physlib
