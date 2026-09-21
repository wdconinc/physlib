/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.Evolution.Basic
/-!

# DGLAP Evolution Toy Solutions

## i. Overview

This module contains restricted solved examples of the DGLAP evolution equation
`Physlib.QFT.Factorization.Evolution.IsDGLAPLogScaleEquation`, and of the scale-local
fixed-point condition `IsDGLAPFixedPoint` that the equation predicate used to assert.

## ii. Key results

- `toySolution_zeroKernel_zeroCoupling`: the identically zero density solves the evolution
  equation with zero kernels and zero coupling.
- `toySolution_zeroKernel`: the same, for zero kernels and an arbitrary coupling.
- `scale_independent_of_zeroKernel`: with vanishing kernels every solution of the evolution
  equation is independent of the scale. This is the statement that distinguishes the
  corrected predicate from the fixed-point condition: it is a conclusion *about* solutions,
  and it is unavailable for a predicate with no derivative in it.
- `toyFixedPoint_zeroKernel_zeroCoupling`: the zero-density example for the fixed-point
  condition, which is what the pre-existing `toySolution_zeroKernel_zeroCoupling` proved.

## iii. Table of contents

- A. Solutions of the evolution equation
- B. Solutions of the fixed-point condition

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Factorization
namespace Evolution

variable {Flavor : Type}

/-! ## A. Solutions of the evolution equation -/

/-- A toy solved case: a pointwise zero PDF solves the log-scale evolution equation with
zero kernels and zero coupling. Both sides vanish identically, the left-hand side because
the derivative of a constant function is zero. -/
lemma toySolution_zeroKernel_zeroCoupling [Fintype Flavor]
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (hzero : ∀ i x Q2, f i x Q2 = 0) :
    IsDGLAPLogScaleEquation (fun _ _ _ _ => 0) (fun _ => 0) f := by
  intro i x τ
  have hfun : (fun s : ℝ => f i x (Real.exp s)) = fun _ => (0 : ℝ) := by
    funext s
    exact hzero i x (Real.exp s)
  have hrhs : dglapRhsLogScale (Flavor := Flavor) (fun _ _ _ _ => 0) (fun _ => 0) f i x τ = 0 :=
    dglapRhsLogScale_zero_kernel _ f i x τ
  rw [hfun, hrhs]
  exact hasDerivAt_const τ 0

/-- A pointwise zero PDF solves the log-scale evolution equation with zero kernels and an
arbitrary running coupling. -/
lemma toySolution_zeroKernel [Fintype Flavor]
    (αs : RunningCoupling)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (hzero : ∀ i x Q2, f i x Q2 = 0) :
    IsDGLAPLogScaleEquation (fun _ _ _ _ => 0) αs f := by
  intro i x τ
  have hfun : (fun s : ℝ => f i x (Real.exp s)) = fun _ => (0 : ℝ) := by
    funext s
    exact hzero i x (Real.exp s)
  have hrhs : dglapRhsLogScale (Flavor := Flavor) (fun _ _ _ _ => 0) αs f i x τ = 0 :=
    dglapRhsLogScale_zero_kernel _ f i x τ
  rw [hfun, hrhs]
  exact hasDerivAt_const τ 0

/-- With vanishing splitting kernels the DGLAP right-hand side vanishes, so every solution
of the evolution equation is independent of the scale.

This is a statement about *all* solutions, not an exhibited one, and it is the kind of
conclusion the corrected predicate supports: it follows from the vanishing of the
`τ`-derivative.

The proof below is complete and uses only proved inputs (`dglapRhsLogScale_zero_kernel` and
`eq_of_hasDerivAt_zero`). It nevertheless carried a `@[sorryful]` attribute, which was stale:
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` (verified at `b63a5fcc`,
grex job 5450e7a7, node n352). Since physlib's sorry linter also rejects a tag on a
sorry-free declaration, the tag has been removed. -/
lemma scale_independent_of_zeroKernel [Fintype Flavor]
    (αs : RunningCoupling)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (h : IsDGLAPLogScaleEquation (fun _ _ _ _ => 0) αs f)
    (i : Flavor) (x τ₁ τ₂ : ℝ) :
    f i x (Real.exp τ₁) = f i x (Real.exp τ₂) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s => f i x (Real.exp s)) 0 t := by
    intro t
    have ht := h i x t
    rwa [dglapRhsLogScale_zero_kernel (Flavor := Flavor) αs f i x t] at ht
  exact eq_of_hasDerivAt_zero hderiv τ₁ τ₂

/-! ## B. Solutions of the fixed-point condition -/

/-- A toy solved case for the scale-local fixed-point condition: zero kernels and zero
coupling are satisfied by any PDF that is pointwise zero.

This is the statement that the pre-correction `toySolution_zeroKernel_zeroCoupling` proved,
back when `IsDGLAPLogScaleEquation` denoted the fixed-point condition. -/
lemma toyFixedPoint_zeroKernel_zeroCoupling [Fintype Flavor]
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (hzero : ∀ i x Q2, f i x Q2 = 0) :
    IsDGLAPFixedPoint (fun _ _ _ _ => 0) (fun _ => 0) f := by
  intro i x τ
  rw [hzero i x (Real.exp τ)]
  exact (dglapRhsLogScale_zero_kernel (Flavor := Flavor) (fun _ => 0) f i x τ).symm

end Evolution
end Factorization
end QFT
end Physlib
