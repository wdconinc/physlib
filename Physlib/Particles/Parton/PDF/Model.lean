/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.PDF.Positivity
/-!

# An explicit collinear PDF model

## i. Overview

`Physlib.Particles.Parton.PDF.Assumptions` had no instance anywhere in the repository: every
result stated against it was conditional, and a hypothesis bundle with no model is not known
to be satisfiable at all. This module supplies one. `modelPdf Flavor a b` is the valence-like
shape `x^a (1-x)^b` on `[0, 1]`, zero outside, independent of flavour and of scale.

Both halves of the bundle are discharged for it. The physical half
(`isPartonDensity_modelPdf`) holds because the shape is nonnegative on `[0, 1]` and the
support is imposed by construction. The analytic half (`regularity_modelPdf`) —
measurability in the momentum fraction and integrability of every Mellin-moment integrand —
holds because the shape is continuous and the support is compact. The analytic half is the
part that was a genuine obligation; the physical half is what "parton density" means.

The same shape carried by a diagonal spin-density matrix discharges
`Physlib.Particles.Parton.PDF.SpinDensityAssumptions`
(`spinDensityAssumptions_modelSpinDensity`), which likewise had no instance.

## ii. Key results

- `Physlib.Particles.Parton.PDF.assumptions_modelPdf`
- `Physlib.Particles.Parton.PDF.regularity_modelPdf`
- `Physlib.Particles.Parton.PDF.isPartonDensity_modelPdf`
- `Physlib.Particles.Parton.PDF.spinDensityAssumptions_modelSpinDensity`

## iii. Table of contents

- A. The shape and the model
- B. The physical half
- C. The analytic half
- D. The spin-density model

## Implementation notes

The exponents are natural numbers, not reals. A realistic small-`x` fit wants `x^a` with
`-1 < a < 0`, which is `Real.rpow` and needs the Beta-integral convergence argument in place
of continuity on a compact set; that generalization is not attempted here. Nothing in the
statements below depends on the particular values of `a` and `b`.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace Particles
namespace Parton
namespace PDF

variable {Flavor : Type}

/-! ### A. The shape and the model -/

/-- The valence-like shape `x^a (1-x)^b`, before restriction to the physical support. -/
def betaShape (a b : ℕ) (x : ℝ) : ℝ := x ^ a * (1 - x) ^ b

/-- The shape is continuous, being a polynomial. -/
lemma continuous_betaShape (a b : ℕ) : Continuous (betaShape a b) :=
  (continuous_pow a).mul ((continuous_const.sub continuous_id).pow b)

/-- The shape is nonnegative on the physical interval. -/
lemma betaShape_nonneg {a b : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ betaShape a b x :=
  mul_nonneg (pow_nonneg hx0 a) (pow_nonneg (by linarith) b)

/-- The explicit collinear PDF: `x^a (1-x)^b` on `[0, 1]` and `0` outside, at every flavour
and every scale. -/
def modelPdf (Flavor : Type) (a b : ℕ) : Pdf Flavor :=
  fun _ x _ => Set.indicator (Set.Icc (0 : ℝ) 1) (betaShape a b) x

/-- Unfolding lemma for the model. -/
lemma modelPdf_apply (Flavor : Type) (a b : ℕ) (i : Flavor) (x Q2 : ℝ) :
    modelPdf Flavor a b i x Q2 = Set.indicator (Set.Icc (0 : ℝ) 1) (betaShape a b) x := rfl

/-! ### B. The physical half -/

/-- The model vanishes off the physical interval, by construction. -/
lemma modelPdf_eq_zero_of_notMem (Flavor : Type) {a b : ℕ} {x : ℝ}
    (hx : x ∉ Set.Icc (0 : ℝ) 1) (i : Flavor) (Q2 : ℝ) :
    modelPdf Flavor a b i x Q2 = 0 := by
  rw [modelPdf_apply]
  simp [Set.indicator_apply, hx]

/-- **The model is a parton density**: supported in `[0, 1]`, and nonnegative there. -/
lemma isPartonDensity_modelPdf (Flavor : Type) (a b : ℕ) :
    IsPartonDensity (modelPdf Flavor a b) := by
  refine ⟨?_, ?_⟩
  · intro i x Q2 hx
    refine modelPdf_eq_zero_of_notMem Flavor ?_ i Q2
    rcases hx with h | h
    · exact fun hm => absurd hm.1 (not_le.mpr h)
    · exact fun hm => absurd hm.2 (not_le.mpr h)
  · intro i x Q2 hx0 hx1
    have h : Set.indicator (Set.Icc (0 : ℝ) 1) (betaShape a b) x = betaShape a b x := by
      simp [Set.indicator_apply, Set.mem_Icc, hx0, hx1]
    rw [modelPdf_apply, h]
    exact betaShape_nonneg hx0 hx1

/-! ### C. The analytic half -/

/-- Every Mellin-moment integrand of the model is integrable: it is the indicator of a
compact interval carrying a continuous function. -/
lemma modelPdf_momentIntegrable (Flavor : Type) (a b n : ℕ) (i : Flavor) (Q2 : ℝ) :
    MeasureTheory.Integrable (fun x : ℝ => x ^ n * modelPdf Flavor a b i x Q2) := by
  have hrw : (fun x : ℝ => x ^ n * modelPdf Flavor a b i x Q2)
      = Set.indicator (Set.Icc (0 : ℝ) 1) (fun y : ℝ => y ^ n * betaShape a b y) := by
    funext x
    rw [modelPdf_apply]
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simp [Set.indicator_apply, hx]
    · simp [Set.indicator_apply, hx]
  rw [hrw]
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
    ((continuous_pow n).mul (continuous_betaShape a b)).integrableOn_Icc

/-- **The analytic half of `Assumptions` holds for the model**: measurability in the momentum
fraction, and integrability of every Mellin-moment integrand. This is the half that was a
real obligation. -/
lemma regularity_modelPdf (Flavor : Type) (a b : ℕ) : Regularity (modelPdf Flavor a b) := by
  refine ⟨?_, ?_⟩
  · intro i Q2
    exact ((continuous_betaShape a b).measurable.indicator
      measurableSet_Icc).aestronglyMeasurable
  · intro n i Q2
    exact modelPdf_momentIntegrable Flavor a b n i Q2

/-- **`PDF.Assumptions` is satisfiable, by an explicit model.** -/
lemma assumptions_modelPdf (Flavor : Type) (a b : ℕ) : Assumptions (modelPdf Flavor a b) :=
  assumptions_iff.mpr ⟨isPartonDensity_modelPdf Flavor a b, regularity_modelPdf Flavor a b⟩

/-- Every Mellin moment of the model is nonnegative. -/
lemma mellinMoment_modelPdf_nonneg (Flavor : Type) (a b n : ℕ) (i : Flavor) (Q2 : ℝ) :
    0 ≤ mellinMoment (modelPdf Flavor a b) n i Q2 := by
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc ?_
  intro x hx
  exact mul_nonneg (pow_nonneg hx.1 n)
    ((isPartonDensity_modelPdf Flavor a b).nonneg i x Q2 hx.1 hx.2)

/-! ### D. The spin-density model -/

/-- A diagonal spin-density family whose induced unpolarized density is `modelPdf`: all four
helicity-diagonal number densities equal `x^a (1-x)^b / 2` on `[0, 1]`. Positive
semidefiniteness of a diagonal matrix is nonnegativity of its entries. -/
def modelSpinDensity (Flavor : Type) (a b : ℕ) : Flavor → ℝ → ℝ → SpinDensity :=
  fun _ x _ =>
    { mat := Matrix.diagonal fun _ =>
        Set.indicator (Set.Icc (0 : ℝ) 1) (betaShape a b) x / 2
      posSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]
        intro j
        have h : 0 ≤ Set.indicator (Set.Icc (0 : ℝ) 1) (betaShape a b) x := by
          by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
          · have h1 : Set.indicator (Set.Icc (0 : ℝ) 1) (betaShape a b) x
                = betaShape a b x := by
              simp [Set.indicator_apply, hx]
            rw [h1]
            exact betaShape_nonneg hx.1 hx.2
          · simp [Set.indicator_apply, hx]
        linarith }

/-- The unpolarized density induced by the diagonal model is `modelPdf`. -/
lemma f1_modelSpinDensity (Flavor : Type) (a b : ℕ) (i : Flavor) (x Q2 : ℝ) :
    f1 (modelSpinDensity Flavor a b i x Q2) = modelPdf Flavor a b i x Q2 := by
  have hdiag : ∀ j : Fin 4, (modelSpinDensity Flavor a b i x Q2).mat j j
      = Set.indicator (Set.Icc (0 : ℝ) 1) (betaShape a b) x / 2 := by
    intro j
    exact Matrix.diagonal_apply_eq _ j
  rw [f1_def, hdiag idxPP, hdiag idxPM, hdiag idxMP, hdiag idxMM, modelPdf_apply]
  ring

/-- **`SpinDensityAssumptions` is satisfiable, by an explicit model.** By
`spinDensityAssumptions_iff_assumptions` this is the same statement as `assumptions_modelPdf`
for the induced density, whose nonnegativity is then a theorem rather than an assumption. -/
lemma spinDensityAssumptions_modelSpinDensity (Flavor : Type) (a b : ℕ) :
    SpinDensityAssumptions (modelSpinDensity Flavor a b) := by
  refine (spinDensityAssumptions_iff_assumptions _).mpr ?_
  have h : pdfOfSpinDensity (modelSpinDensity Flavor a b) = modelPdf Flavor a b := by
    funext i x Q2
    exact f1_modelSpinDensity Flavor a b i x Q2
  rw [h]
  exact assumptions_modelPdf Flavor a b

end PDF
end Parton
end Particles
end Physlib
