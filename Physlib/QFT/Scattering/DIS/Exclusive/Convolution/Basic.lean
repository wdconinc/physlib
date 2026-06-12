/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.GPD.Basic
/-!

# Exclusive GPD Convolution Core

This module defines a shared convolution interface for exclusive observables
constructed from off-forward GPD kernels.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Exclusive
namespace Convolution

/-- A scalar hard kernel for exclusive GPD observables. -/
abbrev Kernel : Type := ℝ → ℝ → ℝ → ℝ

/-- Convolution of an exclusive kernel with the `H` component of a GPD model. -/
def convolveHAt
    {Flavor : Type}
    (K : Kernel)
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (xi t : ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, K x xi t * M.H i x xi t

/-- A constant unit kernel used for baseline bridge specializations. -/
def unitKernel : Kernel :=
  fun _x _xi _t => 1

lemma convolveHAt_unitKernel
    {Flavor : Type}
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (xi t : ℝ) :
    convolveHAt unitKernel M i xi t = ∫ x in Set.Icc (0 : ℝ) 1, M.H i x xi t := by
  simp [convolveHAt, unitKernel]

lemma convolveHAt_eq_of_kernel_eq
    {Flavor : Type}
    (K K' : Kernel)
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (xi t : ℝ)
    (hK : ∀ x xi' t', K x xi' t' = K' x xi' t') :
    convolveHAt K M i xi t = convolveHAt K' M i xi t := by
  simp [convolveHAt, hK]

/-- Shared-image theorem when two exclusive kernels agree pointwise. -/
lemma sharedImage_eq_of_kernel_eq
    {Flavor : Type}
    (Kdvcs Kdvmp : Kernel)
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (xi t : ℝ)
    (hK : ∀ x xi' t', Kdvcs x xi' t' = Kdvmp x xi' t') :
    convolveHAt Kdvcs M i xi t = convolveHAt Kdvmp M i xi t :=
  convolveHAt_eq_of_kernel_eq Kdvcs Kdvmp M i xi t hK

end Convolution
end Exclusive
end DIS
end Scattering
end QFT
end Physlib