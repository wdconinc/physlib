/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.Convolution.Basic
/-!

# Factorization Convolution Properties

This module provides reusable theorems for the convolution API.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Factorization
namespace Convolution

lemma integrand_add_kernel (K1 K2 : Kernel) (f : ℝ → ℝ) (x z : ℝ) :
    integrand (fun x' z' => K1 x' z' + K2 x' z') f x z
      = integrand K1 f x z + integrand K2 f x z := by
  simp [integrand, add_mul]

lemma integrand_smul_kernel (c : ℝ) (K : Kernel) (f : ℝ → ℝ) (x z : ℝ) :
    integrand (fun x' z' => c * K x' z') f x z = c * integrand K f x z := by
  simp [integrand, mul_assoc]

lemma convolveAt_eq_of_kernel_eq
    (K K' : Kernel) (f : ℝ → ℝ) (x : ℝ)
    (hK : ∀ x z, K x z = K' x z) :
    convolveAt K f x = convolveAt K' f x := by
  apply convolveAt_congr K K' f f x
  intro z
  simp [integrand, hK]

end Convolution
end Factorization
end QFT
end Physlib
