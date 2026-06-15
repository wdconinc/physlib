/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Exclusive.Convolution.Basic
public import Physlib.QFT.Scattering.DIS.Exclusive.Amplitudes.Basic
public import Physlib.Particles.Parton.GPD.Basic
/-!

# DVCS CFF Interfaces

This module introduces CFF placeholders and GPD-to-CFF convolution contracts
for DVCS interfaces.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Exclusive
namespace DVCS

/-- Minimal CFF container used by the DVCS interfaces. -/
structure CFF where
  H : ℝ → ℝ → ℝ
  E : ℝ → ℝ → ℝ
  Htilde : ℝ → ℝ → ℝ
  Etilde : ℝ → ℝ → ℝ

/-- A basic CFF combination appearing in observable templates. -/
def cffCombination (C : CFF) (xi t : ℝ) : ℝ :=
  C.H xi t + C.E xi t + C.Htilde xi t + C.Etilde xi t

/-- Explicit exclusive-kernel representation of the DVCS `H` form factor. -/
def IsCFFKernelRepresentedAtScale
    {Flavor : Type}
    (K : Exclusive.Convolution.Kernel)
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (C : CFF)
    (_Q2 : ℝ) : Prop :=
  ∀ xi t, C.H xi t = Exclusive.Convolution.convolveHAt K M i xi t

/-- Convolution contract at fixed flavor and scale. -/
def IsCFFConvolutionAtScale
    {Flavor : Type}
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (C : CFF)
    (_Q2 : ℝ) : Prop :=
  IsCFFKernelRepresentedAtScale Exclusive.Convolution.unitKernel M i C _Q2

/-- Kernel-specialized bridge theorem for the DVCS `H` form factor. -/
lemma cff_kernel_representation_bridge
    {Flavor : Type}
    (K : Exclusive.Convolution.Kernel)
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (C : CFF)
    (Q2 : ℝ)
    (hConv : IsCFFKernelRepresentedAtScale K M i C Q2) :
    ∀ xi t, C.H xi t = Exclusive.Convolution.convolveHAt K M i xi t :=
  hConv

/-- Wrapper theorem exposing the CFF-to-GPD bridge contract. -/
lemma cff_convolution_bridge
    {Flavor : Type}
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (C : CFF)
    (Q2 : ℝ)
    (hConv : IsCFFConvolutionAtScale M i C Q2) :
    ∀ xi t, C.H xi t = ∫ x in Set.Icc (0 : ℝ) 1, M.H i x xi t := by
  intro xi t
  simpa [IsCFFConvolutionAtScale] using
    (cff_kernel_representation_bridge Exclusive.Convolution.unitKernel M i C Q2 hConv xi t).trans
      (Exclusive.Convolution.convolveHAt_unitKernel M i xi t)

/-- DVCS observable template. -/
def dvcsObservable (C : CFF) (xi t Q2 : ℝ) : ℝ :=
  cffCombination C xi t + Q2

lemma dvcsObservable_unfold (C : CFF) (xi t Q2 : ℝ) :
    dvcsObservable C xi t Q2 = cffCombination C xi t + Q2 :=
  rfl

end DVCS
end Exclusive
end DIS
end Scattering
end QFT
end Physlib
