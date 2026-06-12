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

# DVMP TFF Interfaces

This module introduces meson-channel tags and TFF contracts for DVMP
factorization interfaces.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Exclusive
namespace DVMP

/-- Minimal meson kind tag for DVMP channels. -/
inductive MesonKind where
  | vector
  | pseudoscalar
  deriving DecidableEq, Repr

/-- Minimal polarization tags for DVMP channels. -/
inductive PolarizationTag where
  | longitudinal
  | transverse
  deriving DecidableEq, Repr

/-- Channel metadata record for DVMP interfaces. -/
structure Channel (Meson : Type) where
  meson : Meson
  kind : MesonKind
  polarization : PolarizationTag

/-- Transition form-factor placeholder container. -/
structure TFF where
  longitudinal : ℝ → ℝ → ℝ
  transverse : ℝ → ℝ → ℝ

/-- Observable template combining longitudinal/transverse channel parts. -/
def dvmpObservable (T : TFF) (xi t Q2 : ℝ) : ℝ :=
  T.longitudinal xi t + T.transverse xi t + Q2

/-- Explicit exclusive-kernel representation of the DVMP longitudinal form factor. -/
def IsTFFKernelRepresentedAtScale
    {Flavor : Type}
    (K : Exclusive.Convolution.Kernel)
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (T : TFF)
    (_Q2 : ℝ) : Prop :=
  ∀ xi t, T.longitudinal xi t = Exclusive.Convolution.convolveHAt K M i xi t

/-- TFF-to-GPD convolution contract at fixed flavor and scale. -/
def IsTFFConvolutionAtScale
    {Flavor : Type}
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (T : TFF)
    (_Q2 : ℝ) : Prop :=
  IsTFFKernelRepresentedAtScale Exclusive.Convolution.unitKernel M i T _Q2

/-- Kernel-specialized bridge theorem for the DVMP longitudinal form factor. -/
lemma tff_kernel_representation_bridge
    {Flavor : Type}
    (K : Exclusive.Convolution.Kernel)
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (T : TFF)
    (Q2 : ℝ)
    (hConv : IsTFFKernelRepresentedAtScale K M i T Q2) :
    ∀ xi t, T.longitudinal xi t = Exclusive.Convolution.convolveHAt K M i xi t :=
  hConv

/-- Wrapper theorem exposing the TFF-to-GPD bridge contract. -/
lemma tff_convolution_bridge
    {Flavor : Type}
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (T : TFF)
    (Q2 : ℝ)
    (hConv : IsTFFConvolutionAtScale M i T Q2) :
    ∀ xi t, T.longitudinal xi t = ∫ x in Set.Icc (0 : ℝ) 1, M.H i x xi t :=
by
  intro xi t
  simpa [IsTFFConvolutionAtScale] using
    (tff_kernel_representation_bridge Exclusive.Convolution.unitKernel M i T Q2 hConv xi t).trans
      (Exclusive.Convolution.convolveHAt_unitKernel M i xi t)

end DVMP
end Exclusive
end DIS
end Scattering
end QFT
end Physlib
