/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.Convolution.Basic
public import Physlib.Particles.Parton.PDF.Basic
/-!

# DGLAP Evolution Core

This module introduces the DGLAP evolution operator and equation
statement in logarithmic scale.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace QFT
namespace Factorization
namespace Evolution

variable {Flavor : Type}

/-- Splitting kernels `P_{ij}(x,z)` for DGLAP evolution. -/
abbrev SplittingKernel (Flavor : Type) : Type := Flavor → Flavor → ℝ → ℝ → ℝ

/-- The DGLAP convolution operator acting on flavor channel `i`. -/
def dglapOperator [Fintype Flavor]
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x Q2 : ℝ) : ℝ :=
  ∑ j, Convolution.convolveAt (fun x' z => P i j x' z) (fun z => f j z Q2) x

/-- Running coupling profile used by the evolution equation. -/
abbrev RunningCoupling : Type := ℝ → ℝ

/-- The right-hand side of the DGLAP equation in log-scale variable `τ = log Q2`. -/
def dglapRhsLogScale [Fintype Flavor]
    (P : SplittingKernel Flavor)
    (αs : RunningCoupling)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ : ℝ) : ℝ :=
  αs (Real.exp τ) * dglapOperator P f i x (Real.exp τ)

/-- Log-scale DGLAP equation schema. -/
def IsDGLAPLogScaleEquation [Fintype Flavor]
    (P : SplittingKernel Flavor)
    (αs : RunningCoupling)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor) : Prop :=
  ∀ i x τ, f i x (Real.exp τ) = dglapRhsLogScale P αs f i x τ

/-- Operator vanishes for identically zero splitting kernels. -/
lemma dglapOperator_zero_kernel [Fintype Flavor]
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x Q2 : ℝ) :
    dglapOperator (fun _ _ _ _ => 0) f i x Q2 = 0 := by
  simp [dglapOperator, Convolution.convolveAt_zero_kernel]

end Evolution
end Factorization
end QFT
end Physlib
