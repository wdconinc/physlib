/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# Factorization Convolution Core

This module defines the convolution interface used by factorized
representations of DIS observables.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Factorization
namespace Convolution

/-- A two-variable coefficient kernel `K(x,z)`. -/
abbrev Kernel : Type := ℝ → ℝ → ℝ

/-- Integrand appearing in collinear factorization convolutions. -/
def integrand (K : Kernel) (f : ℝ → ℝ) (x z : ℝ) : ℝ :=
  K x z * f z

/-- Convolution of a kernel with a one-variable distribution proxy on `[0,1]`. -/
def convolveAt (K : Kernel) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z in Set.Icc (0 : ℝ) 1, integrand K f x z

lemma integrand_add_right (K : Kernel) (f g : ℝ → ℝ) (x z : ℝ) :
    integrand K (fun t => f t + g t) x z = integrand K f x z + integrand K g x z := by
  simp [integrand, mul_add]

lemma integrand_smul_right (K : Kernel) (c : ℝ) (f : ℝ → ℝ) (x z : ℝ) :
    integrand K (fun t => c * f t) x z = c * integrand K f x z := by
  simp [integrand, mul_left_comm]

lemma convolveAt_congr
    (K K' : Kernel) (f f' : ℝ → ℝ) (x : ℝ)
    (hEq : ∀ z : ℝ, integrand K f x z = integrand K' f' x z) :
    convolveAt K f x = convolveAt K' f' x := by
  simp [convolveAt, hEq]

lemma convolveAt_zero_kernel (f : ℝ → ℝ) (x : ℝ) :
    convolveAt (fun _ _ => 0) f x = 0 := by
  simp [convolveAt, integrand]

lemma convolveAt_eq_zero_of_integrand_zero
    (K : Kernel) (f : ℝ → ℝ) (x : ℝ)
    (hzero : ∀ z : ℝ, integrand K f x z = 0) :
    convolveAt K f x = 0 := by
  have hfun : (fun z : ℝ => integrand K f x z) = fun _ => (0 : ℝ) := by
    funext z
    exact hzero z
  simp [convolveAt, hfun]

/-- Integrability transfer interface for convolution integrands. -/
lemma integrable_integrand
    (K : Kernel) (f : ℝ → ℝ) (x : ℝ)
    (hint : MeasureTheory.Integrable (fun z : ℝ => Set.indicator (Set.Icc (0 : ℝ) 1)
      (fun t => integrand K f x t) z)) :
    MeasureTheory.Integrable (fun z : ℝ => Set.indicator (Set.Icc (0 : ℝ) 1)
      (fun t => integrand K f x t) z) :=
  hint

end Convolution
end Factorization
end QFT
end Physlib
