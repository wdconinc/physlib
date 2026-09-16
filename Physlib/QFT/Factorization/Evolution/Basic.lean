/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.Convolution.Basic
public import Physlib.Particles.Parton.PDF.Basic
public import Physlib.Meta.Linters.Sorry
/-!

# DGLAP Evolution Core

## i. Overview

This module introduces the collinear splitting kernels, the DGLAP evolution operator, and
the DGLAP evolution equation in the logarithmic scale variable `τ = log Q2`.

The equation formalized here is

`∂ f i x τ / ∂ τ = (αs (exp τ) / (2 * π)) * ∑ j, ∫_x^1 (dz / z) * P i j (x / z) (exp τ)
  * f j z (exp τ)`,

a coupled system of integro-differential equations, one per flavor channel.

## ii. Key results

- `collinearKernel` turns a one-variable splitting function into a `Convolution.Kernel`,
  supplying the collinear Jacobian `1 / z` and the support restriction `x ≤ z`.
- `dglapOperator` is the flavor-summed collinear convolution of the splitting kernels with
  the parton densities.
- `dglapOperator_add` and `dglapOperator_const_mul` are its linearity in the densities.
- `IsDGLAPLogScaleEquation` is the DGLAP evolution equation, stated with `HasDerivAt` in
  `τ = log Q2`.
- `IsDGLAPFixedPoint` is the scale-local fixed-point condition that
  `IsDGLAPLogScaleEquation` used to assert before this module was corrected; it is retained
  under a name that describes it.

## iii. Conventions

- `αs` is the standard strong coupling, as constructed by
  `Physlib.QFT.QCD.oneLoopAlphaS`, whose one-loop normalization uses
  `β₀ = 11 / 3 * C_A - 4 / 3 * T_F * n_F` (`Physlib.QFT.QCD.beta0`). The conventional
  prefactor `αs / (2 * π)` of the DGLAP equation is carried by `dglapRhsLogScale`. Before
  this module was corrected the factor `1 / (2 * π)` was absent altogether.
- The last two real arguments of `SplittingKernel` are the momentum-fraction ratio
  `y = x / z` and the scale `Q2`; they are *not* the pair `(x, z)`. The collinear structure
  in `(x, z)` — the Jacobian and the support restriction — is supplied by `collinearKernel`,
  not by the kernel data. This differs from the earlier reading of the same type, under
  which `dglapOperator` was the general integral operator on `[0, 1]` with no Jacobian and
  no support restriction.
- Splitting kernels here are ordinary functions. The physical leading-order kernels contain
  a `1 / (1 - y)` plus-distribution and a `δ (1 - y)` term, which `Convolution.convolveAt`
  cannot represent, since it integrates an ordinary function against Lebesgue measure.
  Every statement in this module is therefore about integrable kernels; the distributional
  case needs a distributional kernel type and is an open gap.

## iv. Table of contents

- A. Splitting kernels and the collinear convolution kernel
- B. The DGLAP operator
  - B.1. Definition and the zero-kernel case
  - B.2. Linearity in the parton densities
- C. The running coupling and the right-hand side
- D. The evolution equation
- E. A general analysis input

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace QFT
namespace Factorization
namespace Evolution

variable {Flavor : Type}

/-! ## A. Splitting kernels and the collinear convolution kernel -/

/-- Splitting kernels `P i j y Q2` for DGLAP evolution.

`P i j` is the splitting function for the transition `j → i`, evaluated at the
momentum-fraction ratio `y = x / z` of the daughter to the parent parton and at the scale
`Q2` (the scale dependence is the perturbative expansion in `αs (Q2)`). The collinear
convolution structure is not part of this datum; it is supplied by `collinearKernel`. -/
abbrev SplittingKernel (Flavor : Type) : Type := Flavor → Flavor → ℝ → ℝ → ℝ

/-- The collinear convolution kernel built from a one-variable splitting function `p`.

`collinearKernel p x z = p (x / z) / z` on the physical region `0 < z` and `x ≤ z`, and `0`
elsewhere. The factor `1 / z` is the Jacobian of the collinear convolution

`(p ⊗ f) x = ∫_x^1 (dz / z) * p (x / z) * f z`,

and the support restriction `x ≤ z` implements the lower limit of that integral: a parton
carrying momentum fraction `x` can only come from a parent carrying `z ≥ x`.

Duplicated definition. Task `task/e1-mellin-convolution` introduces the same construction as
`Physlib.QFT.Factorization.Convolution.collinearKernel`, together with the Mellin
convolution theorem for it. This copy exists only because the two tasks were developed on
separate branches; at merge time the two must be de-duplicated, keeping the version in the
`Convolution` namespace and deleting this one. -/
def collinearKernel (p : ℝ → ℝ) : Convolution.Kernel :=
  fun x z => if 0 < z ∧ x ≤ z then p (x / z) / z else 0

/-- On the physical region the collinear kernel is the splitting function divided by the
momentum fraction of the parent. -/
lemma collinearKernel_apply (p : ℝ → ℝ) {x z : ℝ} (hz : 0 < z) (hxz : x ≤ z) :
    collinearKernel p x z = p (x / z) / z := by
  simp [collinearKernel, hz, hxz]

/-- The collinear kernel vanishes when the parent momentum fraction is below the daughter's:
this is the support restriction of the collinear convolution. -/
lemma collinearKernel_of_lt (p : ℝ → ℝ) {x z : ℝ} (hxz : z < x) :
    collinearKernel p x z = 0 := by
  have hnot : ¬ (0 < z ∧ x ≤ z) := fun h => absurd h.2 (not_le.mpr hxz)
  simp [collinearKernel, hnot]

/-- The collinear kernel vanishes for non-positive parent momentum fraction. -/
lemma collinearKernel_of_nonpos (p : ℝ → ℝ) {x z : ℝ} (hz : z ≤ 0) :
    collinearKernel p x z = 0 := by
  have hnot : ¬ (0 < z ∧ x ≤ z) := fun h => absurd h.1 (not_lt.mpr hz)
  simp [collinearKernel, hnot]

/-- The collinear kernel of the zero splitting function is the zero kernel. -/
lemma collinearKernel_zero : collinearKernel (fun _ => 0) = fun _ _ => (0 : ℝ) := by
  funext x z
  by_cases h : 0 < z ∧ x ≤ z
  · simp [collinearKernel, h]
  · simp [collinearKernel, h]

/-! ## B. The DGLAP operator -/

/-! ### B.1. Definition and the zero-kernel case -/

/-- The integrand of the `j → i` channel of `dglapOperator`, as a function of the
integration variable `z`.

Naming this integrand keeps the integrability hypotheses of the linearity lemmas readable;
`dglapOperator` is a Bochner integral, so its linearity in the densities is conditional on
integrability of exactly this function. -/
def dglapIntegrand
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i j : Flavor) (x Q2 z : ℝ) : ℝ :=
  Convolution.integrand (collinearKernel (fun y => P i j y Q2)) (fun z' => f j z' Q2) x z

/-- The DGLAP convolution operator acting on flavor channel `i`:

`dglapOperator P f i x Q2 = ∑ j, ∫_x^1 (dz / z) * P i j (x / z) Q2 * f j z Q2`,

the flavor-summed collinear convolution of the splitting kernels with the parton densities,
including the Jacobian `1 / z` and the support restriction `x ≤ z` carried by
`collinearKernel`.

The conventional prefactor `αs / (2 * π)` is *not* included here; it is supplied by
`dglapRhsLogScale`. -/
def dglapOperator [Fintype Flavor]
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x Q2 : ℝ) : ℝ :=
  ∑ j, Convolution.convolveAt (collinearKernel (fun y => P i j y Q2)) (fun z => f j z Q2) x

/-- The DGLAP operator in terms of its named integrand. -/
lemma dglapOperator_eq_sum_integral [Fintype Flavor]
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x Q2 : ℝ) :
    dglapOperator P f i x Q2
      = ∑ j, ∫ z in Set.Icc (0 : ℝ) 1, dglapIntegrand P f i j x Q2 z :=
  rfl

/-- The operator vanishes for identically zero splitting kernels. -/
lemma dglapOperator_zero_kernel [Fintype Flavor]
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x Q2 : ℝ) :
    dglapOperator (fun _ _ _ _ => 0) f i x Q2 = 0 := by
  have h : ∀ j : Flavor,
      Convolution.convolveAt (collinearKernel (fun _ => (0 : ℝ))) (fun z => f j z Q2) x = 0 := by
    intro j
    refine Convolution.convolveAt_eq_zero_of_integrand_zero _ _ _ ?_
    intro z
    simp [Convolution.integrand, collinearKernel]
  simp [dglapOperator, h]

/-! ### B.2. Linearity in the parton densities

Linearity of `dglapOperator` in the densities is the hypothesis every later proof needs
(it is what makes the moment-space system linear, hence globally well posed). Additivity
carries integrability hypotheses because `Convolution.convolveAt` is a Bochner integral and
`∫ (g₁ + g₂) = ∫ g₁ + ∫ g₂` fails without them; scalar multiplication does not. -/

/-- Additivity of the DGLAP operator in the parton densities. -/
lemma dglapOperator_add [Fintype Flavor]
    (P : SplittingKernel Flavor)
    (f g : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x Q2 : ℝ)
    (hf : ∀ j, MeasureTheory.IntegrableOn
      (fun z => dglapIntegrand P f i j x Q2 z) (Set.Icc (0 : ℝ) 1))
    (hg : ∀ j, MeasureTheory.IntegrableOn
      (fun z => dglapIntegrand P g i j x Q2 z) (Set.Icc (0 : ℝ) 1)) :
    dglapOperator P (fun j y Q => f j y Q + g j y Q) i x Q2
      = dglapOperator P f i x Q2 + dglapOperator P g i x Q2 := by
  have hchan : ∀ j : Flavor,
      Convolution.convolveAt (collinearKernel (fun y => P i j y Q2))
          (fun z => f j z Q2 + g j z Q2) x
        = Convolution.convolveAt (collinearKernel (fun y => P i j y Q2))
            (fun z => f j z Q2) x
          + Convolution.convolveAt (collinearKernel (fun y => P i j y Q2))
            (fun z => g j z Q2) x := by
    intro j
    have hpt : ∀ z : ℝ,
        Convolution.integrand (collinearKernel (fun y => P i j y Q2))
            (fun z' => f j z' Q2 + g j z' Q2) x z
          = dglapIntegrand P f i j x Q2 z + dglapIntegrand P g i j x Q2 z := by
      intro z
      simp [dglapIntegrand, Convolution.integrand, mul_add]
    simp only [Convolution.convolveAt, hpt]
    exact MeasureTheory.integral_add (hf j) (hg j)
  simp only [dglapOperator, hchan, Finset.sum_add_distrib]

/-- Homogeneity of the DGLAP operator in the parton densities. -/
lemma dglapOperator_const_mul [Fintype Flavor]
    (P : SplittingKernel Flavor) (c : ℝ)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x Q2 : ℝ) :
    dglapOperator P (fun j y Q => c * f j y Q) i x Q2 = c * dglapOperator P f i x Q2 := by
  have hchan : ∀ j : Flavor,
      Convolution.convolveAt (collinearKernel (fun y => P i j y Q2))
          (fun z => c * f j z Q2) x
        = c * Convolution.convolveAt (collinearKernel (fun y => P i j y Q2))
            (fun z => f j z Q2) x := by
    intro j
    have hpt : ∀ z : ℝ,
        Convolution.integrand (collinearKernel (fun y => P i j y Q2))
            (fun z' => c * f j z' Q2) x z
          = c • dglapIntegrand P f i j x Q2 z := by
      intro z
      simp [dglapIntegrand, Convolution.integrand, smul_eq_mul]
      ring
    have hsmul : ∫ z in Set.Icc (0 : ℝ) 1, c • dglapIntegrand P f i j x Q2 z
        = c • ∫ z in Set.Icc (0 : ℝ) 1, dglapIntegrand P f i j x Q2 z :=
      MeasureTheory.integral_smul _ _
    simp only [Convolution.convolveAt, hpt]
    -- The preceding `simp only` unfolds `convolveAt`, so the goal now speaks of
    -- `Convolution.integrand (collinearKernel ...) ...`, whereas `hsmul` is stated in
    -- terms of `dglapIntegrand`. Those are the same by definition of `dglapIntegrand`,
    -- so unfold it here too and the two sides meet.
    simpa [smul_eq_mul, dglapIntegrand] using hsmul
  simp only [dglapOperator, hchan]
  rw [Finset.mul_sum]

/-! ## C. The running coupling and the right-hand side -/

/-- Running coupling profile used by the evolution equation, as a function of `Q2`. -/
abbrev RunningCoupling : Type := ℝ → ℝ

/-- The right-hand side of the DGLAP equation in the log-scale variable `τ = log Q2`:

`dglapRhsLogScale P αs f i x τ = (αs (exp τ) / (2 * π)) * dglapOperator P f i x (exp τ)`.

The prefactor `1 / (2 * π)` is the conventional one, paired with `αs` normalized as the
standard strong coupling (`Physlib.QFT.QCD.oneLoopAlphaS`, one-loop coefficient
`Physlib.QFT.QCD.beta0`). The literature also uses `αs / (4 * π)` and
`a_s = αs / (4 * π)`, which rescale the splitting kernels by factors of two; the choice
here must be respected by any concrete kernel supplied for `P`. -/
def dglapRhsLogScale [Fintype Flavor]
    (P : SplittingKernel Flavor)
    (αs : RunningCoupling)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ : ℝ) : ℝ :=
  αs (Real.exp τ) / (2 * Real.pi) * dglapOperator P f i x (Real.exp τ)

/-- The right-hand side vanishes for identically zero splitting kernels. -/
lemma dglapRhsLogScale_zero_kernel [Fintype Flavor]
    (αs : RunningCoupling)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ : ℝ) :
    dglapRhsLogScale (fun _ _ _ _ => 0) αs f i x τ = 0 := by
  simp [dglapRhsLogScale, dglapOperator_zero_kernel]

/-- The right-hand side vanishes for identically zero coupling. -/
lemma dglapRhsLogScale_zero_coupling [Fintype Flavor]
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ : ℝ) :
    dglapRhsLogScale P (fun _ => 0) f i x τ = 0 := by
  simp [dglapRhsLogScale]

/-! ## D. The evolution equation -/

/-- The DGLAP *fixed-point* condition: at every scale the parton densities equal their own
convolution against the splitting kernels,

`f i x (exp τ) = dglapRhsLogScale P αs f i x τ`.

This is the predicate that carried the name `IsDGLAPLogScaleEquation` before this module was
corrected. It contains no derivative and is **not** the DGLAP evolution equation: it is a
scale-local fixed-point condition, with a much smaller solution set. It is retained under a
name that describes it because it is the statement the pre-existing zero-density example was
actually about. New developments should use `IsDGLAPLogScaleEquation`. -/
def IsDGLAPFixedPoint [Fintype Flavor]
    (P : SplittingKernel Flavor)
    (αs : RunningCoupling)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor) : Prop :=
  ∀ i x τ, f i x (Real.exp τ) = dglapRhsLogScale P αs f i x τ

/-- The DGLAP evolution equation in the log-scale variable `τ = log Q2`: for every flavor
`i` and momentum fraction `x`, the function `s ↦ f i x (exp s)` is differentiable at every
`τ` with derivative the convolution right-hand side,

`∂ f i x τ / ∂ τ = (αs (exp τ) / (2 * π)) * ∑ j, ∫_x^1 (dz / z) * P i j (x / z) (exp τ)
  * f j z (exp τ)`.

The derivative is taken with respect to `τ = log Q2`, matching the name: the density
`Physlib.Particles.Parton.PDF.Pdf` carries `Q2`, so the composition with `Real.exp` is the
function that has the derivative, and the `exp` is kept explicit rather than introducing a
second density type. -/
def IsDGLAPLogScaleEquation [Fintype Flavor]
    (P : SplittingKernel Flavor)
    (αs : RunningCoupling)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor) : Prop :=
  ∀ i x τ, HasDerivAt (fun s => f i x (Real.exp s)) (dglapRhsLogScale P αs f i x τ) τ

/-- A solution of the DGLAP equation is differentiable in `τ = log Q2`. -/
lemma differentiable_of_isDGLAPLogScaleEquation [Fintype Flavor]
    {P : SplittingKernel Flavor} {αs : RunningCoupling}
    {f : Physlib.Particles.Parton.PDF.Pdf Flavor}
    (h : IsDGLAPLogScaleEquation P αs f) (i : Flavor) (x : ℝ) :
    Differentiable ℝ (fun s => f i x (Real.exp s)) :=
  fun τ => (h i x τ).differentiableAt

/-- The `deriv` form of the DGLAP equation. -/
lemma deriv_of_isDGLAPLogScaleEquation [Fintype Flavor]
    {P : SplittingKernel Flavor} {αs : RunningCoupling}
    {f : Physlib.Particles.Parton.PDF.Pdf Flavor}
    (h : IsDGLAPLogScaleEquation P αs f) (i : Flavor) (x τ : ℝ) :
    deriv (fun s => f i x (Real.exp s)) τ = dglapRhsLogScale P αs f i x τ :=
  (h i x τ).deriv

/-! ## E. A general analysis input

The results below need one standard consequence of the mean value theorem: a function on
`ℝ` with vanishing derivative everywhere is constant. It is stated here rather than used
inline so that there is a single place to substitute the mathlib lemma. -/

/-- A function on `ℝ` with values in a real normed space and vanishing derivative
everywhere is constant.

TODO(task/e2-dglap-wellposedness): this is a restatement of a mathlib corollary of the mean
value theorem — `is_const_of_deriv_eq_zero` for real-valued functions, or
`constant_of_has_deriv_right_zero` for functions into a normed space. Neither the exact
name nor the exact signature at the pinned mathlib revision could be confirmed offline, so
the step is left as `sorry` rather than guessed. Intended proof, in the normed-space
generality stated here: apply `constant_of_has_deriv_right_zero` on `Set.Icc (min τ₁ τ₂)
(max τ₁ τ₂)`, whose continuity hypothesis follows from `HasDerivAt.continuousAt` and whose
one-sided derivative hypothesis follows from `HasDerivAt.hasDerivWithinAt`. At the build
phase this declaration should be replaced by the mathlib lemma and deleted. -/
@[sorryful]
lemma eq_of_hasDerivAt_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (h : ∀ t : ℝ, HasDerivAt g 0 t) (τ₁ τ₂ : ℝ) :
    g τ₁ = g τ₂ := by
  sorry

end Evolution
end Factorization
end QFT
end Physlib
