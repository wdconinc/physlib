/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Exclusive.DVCS.Interference
public import Physlib.QFT.Scattering.DIS.Exclusive.DVMP.Basic
public import Physlib.QFT.Scattering.DIS.SIDIS.Asymmetries.Basic
/-!

# Conjectural Theorem-Design Targets

This module registers theorem-design targets for cross-framework conjectures:

- DIS-CONJ-001: unified projection algebra across SIDIS and DVCS projection paths.
- DIS-CONJ-002: unified exclusive convolution bridge across DVCS CFF and DVMP TFF.

These targets are interface-level contracts intended to guide future proof
development.

Proof roadmap for DIS-CONJ-001:

1. isolate a generic regularized-ratio bridge lemma for numerator/denominator
  projection equalities;
2. instantiate that bridge for SIDIS Sivers and DVCS interference observables;
3. package the two instantiations into the unified conjecture statement.

Proof roadmap for DIS-CONJ-002:

1. isolate a generic shared-integrand bridge lemma for two convolution
  identifications;
2. instantiate it for the DVCS CFF and DVMP TFF bridges against the same GPD
  kernel;
3. package the two bridge equalities and their shared image into the unified
  conjecture statement.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Inference
namespace Conjectures

/--
Assumption bundle for DIS-CONJ-001, now phrased in terms of a shared
projector linearity and harmonic orthogonality contract.
-/
structure UnifiedProjectionDerivedAssumptions
    (P : SIDIS.Asymmetries.Harmonics.Projector) : Prop where
  linearity : SIDIS.Asymmetries.Harmonics.ProjectorAssumptions P
  orthogonality : SIDIS.Asymmetries.Harmonics.HarmonicOrthogonalityAssumptions P

/--
Generic regularized-ratio bridge used by the DIS-CONJ-001 proof roadmap.

If the numerator and denominator values agree with their projected counterparts,
then the corresponding regularized ratios agree as well.
-/
lemma projectedRatio_eq_of_equal_bridges
  (num den numProj denProj : ℝ)
  (hNum : num = numProj)
    (hDen : den = denProj) :
  num / (|den| + 1) = numProj / (|denProj| + 1) := by
  simp [hNum, hDen]

/--
Generic shared-integrand bridge used by the DIS-CONJ-002 proof roadmap.

If two observables are both identified with the same convolution image, then
they are equal to each other.
-/
lemma sharedIntegrand_eq_of_equal_bridges
    (obs1 obs2 img : ℝ)
    (h1 : obs1 = img)
    (h2 : obs2 = img) :
    obs1 = obs2 := by
  calc
    obs1 = img := h1
    _ = obs2 := by
      symm
      exact h2

/--
DIS-CONJ-001 theorem-design target: one projector-level assumption bundle yields
both the SIDIS and DVCS projected-ratio identities.
-/
lemma unified_projection_algebra_designTarget
    (P : SIDIS.Asymmetries.Harmonics.Projector)
    (F : SIDIS.Asymmetries.SpinStructureFunctions)
    (D : Exclusive.DVCS.Decomposition)
    (x zHad Q2sidis pT xi t Q2excl : ℝ)
    (h : UnifiedProjectionDerivedAssumptions P) :
    (SIDIS.Asymmetries.siversAsymmetry F x zHad Q2sidis pT
        = SIDIS.Asymmetries.Harmonics.projectedMoment
            P
            SIDIS.Asymmetries.Harmonics.sinPhiDiff
            (SIDIS.Asymmetries.siversAngularObservable F x zHad Q2sidis pT)
            / (|SIDIS.Asymmetries.Harmonics.projectedMoment
                P
                SIDIS.Asymmetries.Harmonics.oneWeight
                (SIDIS.Asymmetries.unpolarizedAngularObservable F x zHad Q2sidis pT)| + 1))
      ∧
      (Exclusive.DVCS.beamSpinAsymmetry D xi t Q2excl
        = SIDIS.Asymmetries.Harmonics.projectedMoment
            P
            SIDIS.Asymmetries.Harmonics.sinPhiDiff
            (Exclusive.DVCS.interferenceAngularObservable D xi t Q2excl)
            / (|SIDIS.Asymmetries.Harmonics.projectedMoment
                P
                SIDIS.Asymmetries.Harmonics.oneWeight
                (Exclusive.DVCS.totalAngularObservable D xi t Q2excl)| + 1)) := by
    constructor
    · exact SIDIS.Asymmetries.siversAsymmetry_eq_projectedRatio_of_harmonicDecomposition
        P F x zHad Q2sidis pT h.linearity h.orthogonality
    · exact Exclusive.DVCS.beamSpinAsymmetry_eq_projectedRatio_of_harmonicDecomposition
        P D xi t Q2excl h.linearity h.orthogonality

/-- Assumption bundle for DIS-CONJ-002 across CFF and TFF convolution interfaces. -/
structure UnifiedExclusiveConvolutionAssumptions
    {Flavor : Type}
    (Kdvcs Kdvmp : Exclusive.Convolution.Kernel)
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (C : Exclusive.DVCS.CFF)
    (T : Exclusive.DVMP.TFF)
    (Q2 : ℝ) : Prop where
  cffBridge : Exclusive.DVCS.IsCFFKernelRepresentedAtScale Kdvcs M i C Q2
  tffBridge : Exclusive.DVMP.IsTFFKernelRepresentedAtScale Kdvmp M i T Q2
  kernelEq : ∀ x xi' t', Kdvcs x xi' t' = Kdvmp x xi' t'

/--
DIS-CONJ-002 theorem-design target: one exclusive-convolution assumption bundle
recovers both bridge contracts and a shared integrand image.
-/
lemma unified_exclusive_convolution_designTarget
    {Flavor : Type}
    (Kdvcs Kdvmp : Exclusive.Convolution.Kernel)
    (M : Physlib.Particles.Parton.GPD.Model Flavor)
    (i : Flavor)
    (C : Exclusive.DVCS.CFF)
    (T : Exclusive.DVMP.TFF)
    (Q2 : ℝ)
    (h : UnifiedExclusiveConvolutionAssumptions Kdvcs Kdvmp M i C T Q2) :
    (∀ xi t, C.H xi t = Exclusive.Convolution.convolveHAt Kdvcs M i xi t)
      ∧ (∀ xi t, T.longitudinal xi t = Exclusive.Convolution.convolveHAt Kdvmp M i xi t)
      ∧ (∀ xi t, C.H xi t = T.longitudinal xi t) := by
  have hCFF : ∀ xi t, C.H xi t = Exclusive.Convolution.convolveHAt Kdvcs M i xi t :=
    Exclusive.DVCS.cff_kernel_representation_bridge Kdvcs M i C Q2 h.cffBridge
  have hTFF : ∀ xi t, T.longitudinal xi t = Exclusive.Convolution.convolveHAt Kdvmp M i xi t :=
    Exclusive.DVMP.tff_kernel_representation_bridge Kdvmp M i T Q2 h.tffBridge
  constructor
  · exact hCFF
  constructor
  · exact hTFF
  · intro xi t
    calc
      C.H xi t = Exclusive.Convolution.convolveHAt Kdvcs M i xi t := hCFF xi t
      _ = Exclusive.Convolution.convolveHAt Kdvmp M i xi t :=
        Exclusive.Convolution.sharedImage_eq_of_kernel_eq Kdvcs Kdvmp M i xi t h.kernelEq
      _ = T.longitudinal xi t := (hTFF xi t).symm

end Conjectures
end Inference
end DIS
end Scattering
end QFT
end Physlib
