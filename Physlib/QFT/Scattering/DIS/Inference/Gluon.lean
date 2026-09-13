/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Polarized.Basic
public import Physlib.QFT.Factorization.Evolution.Basic
public import Physlib.QFT.Factorization.HigherOrder.Basic
/-!

# DeltaG Access Interfaces

This module provides theorem-design targets for DeltaG-sensitive scaling
violations and tagged-channel observables.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Inference
namespace Gluon

/-- Finite-difference proxy for the log-scale slope of `g1` at fixed `x`. -/
def g1LogSlope
    (G : Polarized.StructureFunctions)
    (x tau h : ℝ) : ℝ :=
  (G.g1 x (Real.exp (tau + h)) - G.g1 x (Real.exp tau)) / h

/-- DeltaG sensitivity contract for inclusive scaling-violation observables. -/
structure DeltaGSlopeAssumptions
    (slope : ℝ → ℝ → ℝ)
    (deltaG : ℝ → ℝ → ℝ)
    (coeff residual : ℝ → ℝ → ℝ) : Prop where
  model : ∀ x tau,
    slope x tau = coeff x tau * deltaG x (Real.exp tau) + residual x tau

/-- Reconstruction formula for DeltaG from slope-model ingredients. -/
lemma deltaG_eq_of_slope_model
    (slope : ℝ → ℝ → ℝ)
    (deltaG : ℝ → ℝ → ℝ)
    (coeff residual : ℝ → ℝ → ℝ)
    (hSlope : DeltaGSlopeAssumptions slope deltaG coeff residual)
    (x tau : ℝ)
    (hCoeff : coeff x tau ≠ 0) :
    deltaG x (Real.exp tau)
      = (slope x tau - residual x tau) / coeff x tau := by
  have hEq := hSlope.model x tau
  have hLin : slope x tau - residual x tau = coeff x tau * deltaG x (Real.exp tau) := by
    linarith
  have hMul : deltaG x (Real.exp tau) * coeff x tau = slope x tau - residual x tau := by
    simpa [mul_comm] using hLin.symm
  exact (eq_div_iff hCoeff).2 hMul

/-- Identity-scheme stability for higher-order hard-kernel conversion. -/
lemma deltaG_identity_scheme_stability
    {Flavor : Type}
    [Fintype Flavor]
    (S : Factorization.HigherOrder.Scheme)
    (C : Factorization.HigherOrder.HardKernelFamily Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (x Q2 : ℝ)
    (ord : Factorization.HigherOrder.PerturbativeOrder) :
    Factorization.HigherOrder.truncatedStructureFunction
      (Factorization.HigherOrder.convertKernel S S C ord) f x Q2
      = Factorization.HigherOrder.truncatedStructureFunction C f x Q2 := by
  simp [Factorization.HigherOrder.truncatedStructureFunction,
    Factorization.HigherOrder.convertKernel]

/-- Tagged-channel labels for gluon-sensitive experimental observables. -/
inductive TaggedChannel where
  | charmTagged
  | highPt
  deriving DecidableEq, Repr

/-- Channel metadata for DeltaG-sensitive measurements. -/
structure TaggedChannelDataPoint where
  channel : TaggedChannel
  xBj : ℝ
  Q2 : ℝ
  observed : ℝ

/-- Regularized channel asymmetry interface. -/
def channelAsymmetry (num den : ℝ) : ℝ :=
  num / (|den| + 1)

/-- Channel-level DeltaG response model. -/
structure ChannelDeltaGAssumptions
    (obs : TaggedChannelDataPoint → ℝ)
    (deltaG : ℝ → ℝ → ℝ)
    (weight : TaggedChannel → ℝ)
    (residual : TaggedChannelDataPoint → ℝ) : Prop where
  model : ∀ d,
    obs d = weight d.channel * deltaG d.xBj d.Q2 + residual d

/-- Channel-level reconstruction formula for DeltaG-sensitive observables. -/
lemma deltaG_channel_access
    (obs : TaggedChannelDataPoint → ℝ)
    (deltaG : ℝ → ℝ → ℝ)
    (weight : TaggedChannel → ℝ)
    (residual : TaggedChannelDataPoint → ℝ)
    (hCh : ChannelDeltaGAssumptions obs deltaG weight residual)
    (d : TaggedChannelDataPoint)
    (hWeight : weight d.channel ≠ 0) :
    deltaG d.xBj d.Q2 = (obs d - residual d) / weight d.channel := by
  have hEq := hCh.model d
  have hLin : obs d - residual d = weight d.channel * deltaG d.xBj d.Q2 := by
    linarith
  have hMul : deltaG d.xBj d.Q2 * weight d.channel = obs d - residual d := by
    simpa [mul_comm] using hLin.symm
  exact (eq_div_iff hWeight).2 hMul

/-- Inclusive consistency check when tagged channels share a common DeltaG image. -/
lemma channel_consistency_if_same_weight
    (obs : TaggedChannelDataPoint → ℝ)
    (deltaG : ℝ → ℝ → ℝ)
    (weight : TaggedChannel → ℝ)
    (residual : TaggedChannelDataPoint → ℝ)
    (hCh : ChannelDeltaGAssumptions obs deltaG weight residual)
    (d1 d2 : TaggedChannelDataPoint)
    (hW : weight d1.channel = weight d2.channel)
    (hDG : deltaG d1.xBj d1.Q2 = deltaG d2.xBj d2.Q2)
    (hR : residual d1 = residual d2) :
    obs d1 = obs d2 := by
  calc
    obs d1 = weight d1.channel * deltaG d1.xBj d1.Q2 + residual d1 := hCh.model d1
    _ = weight d2.channel * deltaG d2.xBj d2.Q2 + residual d2 := by
      simp [hW, hDG, hR]
    _ = obs d2 := (hCh.model d2).symm

end Gluon
end Inference
end DIS
end Scattering
end QFT
end Physlib
