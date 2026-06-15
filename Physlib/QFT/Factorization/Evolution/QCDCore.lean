/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.Evolution.Basic
public import Physlib.QFT.QCD.Basic
public import Physlib.QFT.QCD.OneLoopBeta
public import Physlib.QFT.QCD.RepresentationColor
public import Physlib.QFT.QCD.SUNDerivation
/-!

# QCD-Evolution Bridge

This module connects QCD core interfaces with DGLAP evolution interfaces.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Factorization
namespace Evolution

open Physlib.QFT.QCD

variable {Flavor : Type}

/-- QCD one-loop running coupling packaged as an evolution `RunningCoupling`. -/
def qcdRunningCoupling (cf : QCD.ColorFactors) (lambdaQCD2 : ℝ) : RunningCoupling :=
  fun Q2 => QCD.oneLoopAlphaS cf Q2 lambdaQCD2

/-- Group-parameterized QCD one-loop running coupling using derived color invariants. -/
def qcdRunningCouplingOf
    (G : Type) [QCD.HasColorInvariants G]
    (nF lambdaQCD2 : ℝ) : RunningCoupling :=
  qcdRunningCoupling (QCD.colorFactorsOf G nF) lambdaQCD2

/-- Representation-derived running coupling for groups equipped with normalized generators. -/
def qcdRunningCouplingFromRepresentation
    (G : Type) [QCD.RepresentationColor.HasNormalizedGeneratorData G]
    (nF lambdaQCD2 : ℝ) : RunningCoupling :=
  qcdRunningCouplingOf G nF lambdaQCD2

/-- Structural assumptions for QCD-flavored splitting kernels. -/
structure QCDSplittingKernelAssumptions (P : SplittingKernel Flavor) : Prop where
  /-- Positivity interface for migration probability density kernels. -/
  nonneg : ∀ i j x z, 0 ≤ P i j x z

/-- DGLAP equation schema specialized to QCD running-coupling input. -/
def IsQCDDGLAPLogScaleEquation [Fintype Flavor]
    (cf : QCD.ColorFactors)
    (lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor) : Prop :=
  IsDGLAPLogScaleEquation P (qcdRunningCoupling cf lambdaQCD2) f

/-- DGLAP schema specialized to a gauge-group-derived color-factor model. -/
def IsQCDDGLAPLogScaleEquationOf
    (G : Type) [QCD.HasColorInvariants G]
    [Fintype Flavor]
    (nF lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor) : Prop :=
  IsDGLAPLogScaleEquation P (qcdRunningCouplingOf G nF lambdaQCD2) f

/-- DGLAP schema specialized to representation-derived QCD color data. -/
def IsQCDDGLAPLogScaleEquationFromRepresentation
    (G : Type) [QCD.RepresentationColor.HasNormalizedGeneratorData G]
    [Fintype Flavor]
    (nF lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor) : Prop :=
  IsDGLAPLogScaleEquation P (qcdRunningCouplingFromRepresentation G nF lambdaQCD2) f

/-- One-loop beta coefficient through representation extraction data. -/
lemma beta0Of_eq_representation_data
    (G : Type) [QCD.RepresentationColor.HasNormalizedGeneratorData G]
    (nF : ℝ) :
    QCD.beta0Of G nF =
      QCD.beta0
        (QCD.RepresentationColor.colorFactorsOfData
          (QCD.RepresentationColor.HasNormalizedGeneratorData.data (G := G)) nF) := by
  simpa using QCD.RepresentationColor.beta0Of_eq_beta0OfData (G := G) (nF := nF)

/-- Two-loop beta coefficient through representation extraction data. -/
lemma beta1Of_eq_representation_data
    (G : Type) [QCD.RepresentationColor.HasNormalizedGeneratorData G]
    (nF : ℝ) :
    QCD.beta1Of G nF =
      QCD.beta1
        (QCD.RepresentationColor.colorFactorsOfData
          (QCD.RepresentationColor.HasNormalizedGeneratorData.data (G := G)) nF) := by
  simpa using QCD.RepresentationColor.beta1Of_eq_beta1OfData (G := G) (nF := nF)

/-- For `SU(Nc)`, representation-derived running coupling matches the direct
`suNColorFactors` running-coupling form when the normalized contracts are provided. -/
lemma qcdRunningCouplingFromRepresentation_suN_eq_of_contracts
    (nC nF lambdaQCD2 : ℝ)
    (hContracts :
      (QCD.RepresentationColor.sunNormalizedData nC).traceNormalization ∧
        (QCD.RepresentationColor.sunNormalizedData nC).fundamentalCasimir ∧
        (QCD.RepresentationColor.sunNormalizedData nC).adjointCasimir) :
    qcdRunningCouplingFromRepresentation (QCD.SUN nC) nF lambdaQCD2
      = qcdRunningCoupling (QCD.suNColorFactors nC nF) lambdaQCD2 := by
  funext Q2
  simpa [qcdRunningCouplingFromRepresentation, qcdRunningCouplingOf, qcdRunningCoupling] using
    congrArg (fun cf => QCD.oneLoopAlphaS cf Q2 lambdaQCD2)
      (QCD.RepresentationColor.colorFactorsOf_suN_eq_from_representation_of_contracts
        (nC := nC) (nF := nF) hContracts)

/-- Canonical `SU(Nc)` corollary of the running-coupling bridge. -/
lemma qcdRunningCouplingFromRepresentation_suN_eq
    (nC nF lambdaQCD2 : ℝ) :
    qcdRunningCouplingFromRepresentation (QCD.SUN nC) nF lambdaQCD2
      = qcdRunningCoupling (QCD.suNColorFactors nC nF) lambdaQCD2 :=
  qcdRunningCouplingFromRepresentation_suN_eq_of_contracts nC nF lambdaQCD2
    (QCD.RepresentationColor.sunNormalizedContracts nC)

/-- For `SU(Nc)`, the representation-derived DGLAP schema is equivalent to the
direct `suNColorFactors` schema when the normalized contracts are provided. -/
lemma isQCDDGLAPLogScaleEquationFromRepresentation_suN_iff_of_contracts
    [Fintype Flavor]
    (nC nF lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (hContracts :
      (QCD.RepresentationColor.sunNormalizedData nC).traceNormalization ∧
        (QCD.RepresentationColor.sunNormalizedData nC).fundamentalCasimir ∧
        (QCD.RepresentationColor.sunNormalizedData nC).adjointCasimir) :
    IsQCDDGLAPLogScaleEquationFromRepresentation (QCD.SUN nC) nF lambdaQCD2 P f
      ↔ IsQCDDGLAPLogScaleEquation (QCD.suNColorFactors nC nF) lambdaQCD2 P f := by
  unfold IsQCDDGLAPLogScaleEquationFromRepresentation IsQCDDGLAPLogScaleEquation
  simp [qcdRunningCouplingFromRepresentation_suN_eq_of_contracts
    (nC := nC) (nF := nF) (lambdaQCD2 := lambdaQCD2) hContracts]

/-- Canonical `SU(Nc)` corollary of the DGLAP schema transport. -/
lemma isQCDDGLAPLogScaleEquationFromRepresentation_suN_iff
    [Fintype Flavor]
    (nC nF lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor) :
    IsQCDDGLAPLogScaleEquationFromRepresentation (QCD.SUN nC) nF lambdaQCD2 P f
      ↔ IsQCDDGLAPLogScaleEquation (QCD.suNColorFactors nC nF) lambdaQCD2 P f :=
  isQCDDGLAPLogScaleEquationFromRepresentation_suN_iff_of_contracts nC nF lambdaQCD2 P f
    (QCD.RepresentationColor.sunNormalizedContracts nC)

/-- For `SU(Nc)`, the DGLAP rhs built from representation-derived running
coupling agrees with the rhs built from direct `suNColorFactors`, when the
normalized contracts are provided. -/
lemma qcdDglap_rhs_suN_fromRepresentation_eq_of_contracts
    [Fintype Flavor]
    (nC nF lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ : ℝ)
    (hContracts :
      (QCD.RepresentationColor.sunNormalizedData nC).traceNormalization ∧
        (QCD.RepresentationColor.sunNormalizedData nC).fundamentalCasimir ∧
        (QCD.RepresentationColor.sunNormalizedData nC).adjointCasimir) :
    dglapRhsLogScale P
        (qcdRunningCouplingFromRepresentation (QCD.SUN nC) nF lambdaQCD2) f i x τ
      = dglapRhsLogScale P
          (qcdRunningCoupling (QCD.suNColorFactors nC nF) lambdaQCD2) f i x τ := by
    simp [qcdRunningCouplingFromRepresentation_suN_eq_of_contracts
    (nC := nC) (nF := nF) (lambdaQCD2 := lambdaQCD2) hContracts]

/-- Canonical `SU(Nc)` corollary of the rhs-level computational bridge. -/
lemma qcdDglap_rhs_suN_fromRepresentation_eq
    [Fintype Flavor]
    (nC nF lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ : ℝ) :
    dglapRhsLogScale P
        (qcdRunningCouplingFromRepresentation (QCD.SUN nC) nF lambdaQCD2) f i x τ
      = dglapRhsLogScale P
          (qcdRunningCoupling (QCD.suNColorFactors nC nF) lambdaQCD2) f i x τ :=
  qcdDglap_rhs_suN_fromRepresentation_eq_of_contracts nC nF lambdaQCD2 P f i x τ
    (QCD.RepresentationColor.sunNormalizedContracts nC)

/-- Evolution-facing Step-4 corollary: if one-loop primitive poles satisfy the
`SU(Nc)` contracts and coupling-pole link, then `beta0Of (SUN nC)` equals the
renormalization-reconstructed coefficient used by one-loop interfaces. -/
lemma beta0Of_suN_from_oneLoopPoles
    (nC nF : ℝ)
    (ms : QCD.Renormalization.MSLikeRenormalizationData)
    (p : QCD.OneLoopBeta.PrimitivePoles)
    (hPole : QCD.OneLoopBeta.PrimitivePoleAssumptions (QCD.suNColorFactors nC nF) p)
    (hLink : QCD.OneLoopBeta.OneLoopRenormalizationLink ms p) :
    QCD.beta0Of (QCD.SUN nC) nF = QCD.Renormalization.beta0FromCouplingPole ms.couplingPole := by
  simpa using QCD.OneLoopBeta.beta0Of_suN_from_oneLoopPoles nC nF ms p hPole hLink

/-- Definitional expansion of QCD-DGLAP RHS in log-scale. -/
lemma qcdDglap_rhs_def [Fintype Flavor]
    (cf : QCD.ColorFactors)
    (lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ : ℝ) :
    dglapRhsLogScale P (qcdRunningCoupling cf lambdaQCD2) f i x τ
      = qcdRunningCoupling cf lambdaQCD2 (Real.exp τ)
          * dglapOperator P f i x (Real.exp τ) :=
  rfl

/-- Zero-kernel specialization remains zero under QCD running-coupling packaging. -/
lemma qcdDglap_zeroKernel_rhs [Fintype Flavor]
    (cf : QCD.ColorFactors)
    (lambdaQCD2 : ℝ)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ : ℝ) :
    dglapRhsLogScale (fun _ _ _ _ => 0) (qcdRunningCoupling cf lambdaQCD2) f i x τ = 0 := by
  simp [dglapRhsLogScale, dglapOperator_zero_kernel]

end Evolution
end Factorization
end QFT
end Physlib
