/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.OneLoopBetaFromScalars
public import Physlib.QFT.PerturbationTheory.DimensionalRegularization.TensorReduction
/-!

# One-Loop Numerator Contractions

This module records the explicit one-loop numerator contractions for the gauge,
ghost, and fermion sectors, using the tensor-reduction layer to attach the
expected color-factor coefficients to scalar master integrals.

The current implementation captures the standard one-loop beta-function weights:

* gluon loop: $(5/3) C_A$
* ghost loop: $2 C_A$
* fermion loop: $-(4/3) T_F n_f$

These are then converted into `PrimitivePoleAssumptions` for the existing
one-loop beta assembly theorem.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace OneLoopNumeratorContractions

open OneLoopBeta
open OneLoopBetaFromScalars
open Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars
open Physlib.QFT.PerturbationTheory.DimensionalRegularization.TensorReduction

/-- Tensor-reduced gluon-loop numerator contraction. -/
def gluonLoopReduction (cf : ColorFactors) : RankTwoReductionResult :=
  (gaugeBosonSelfEnergyTensorIntegrand ((5 / 3) * cf.cA)).reduce

/-- Tensor-reduced ghost-loop numerator contraction. -/
def ghostLoopReduction (cf : ColorFactors) : RankTwoReductionResult :=
  (ghostSelfEnergyTensorIntegrand (2 * cf.cA)).reduce

/-- Tensor-reduced fermion-loop numerator contraction. -/
def quarkLoopReduction (cf : ColorFactors) : RankTwoReductionResult :=
  (fermionSelfEnergyTensorIntegrand (-(4 / 3) * cf.tF * cf.nF)).reduce

/-- Primitive pole weights read off from the standard one-loop numerator contractions. -/
def primitivePoleWeightsOfContractions (cf : ColorFactors) : PrimitivePoleWeights where
  gluonCoeff := (gluonLoopReduction cf).metricCoeff
  ghostCoeff := (ghostLoopReduction cf).metricCoeff
  quarkCoeff := (quarkLoopReduction cf).metricCoeff

/-- Primitive poles obtained from the standard one-loop numerator contractions. -/
def primitivePolesOfContractions (cf : ColorFactors) : PrimitivePoles :=
  primitivePolesOfMasters
    (primitivePoleWeightsOfContractions cf)
    gaugeBosonSelfEnergyMaster
    ghostSelfEnergyMaster
    fermionSelfEnergyMaster

/-- The contraction-derived gluon pole equals the expected coefficient. -/
lemma primitivePolesOfContractions_gluon (cf : ColorFactors) :
    (primitivePolesOfContractions cf).gluon = (5 / 3) * cf.cA := by
  simp [primitivePolesOfContractions, primitivePolesOfMasters,
    primitivePoleWeightsOfContractions, gluonLoopReduction,
    gaugeBosonSelfEnergyMaster]

/-- The contraction-derived ghost pole equals the expected coefficient. -/
lemma primitivePolesOfContractions_ghost (cf : ColorFactors) :
    (primitivePolesOfContractions cf).ghost = 2 * cf.cA := by
  simp [primitivePolesOfContractions, primitivePolesOfMasters,
    primitivePoleWeightsOfContractions, ghostLoopReduction,
    ghostSelfEnergyMaster]

/-- The contraction-derived quark pole equals the expected coefficient. -/
lemma primitivePolesOfContractions_quark (cf : ColorFactors) :
    (primitivePolesOfContractions cf).quark = -(4 / 3) * cf.tF * cf.nF := by
  simp [primitivePolesOfContractions, primitivePolesOfMasters,
    primitivePoleWeightsOfContractions, quarkLoopReduction,
    fermionSelfEnergyMaster]

/-- Standard one-loop numerator contractions discharge the primitive pole contracts. -/
lemma primitivePoleAssumptions_of_standardContractions (cf : ColorFactors) :
    PrimitivePoleAssumptions cf (primitivePolesOfContractions cf) := by
  refine {
    gluon_eq := primitivePolesOfContractions_gluon cf
    ghost_eq := primitivePolesOfContractions_ghost cf
    quark_eq := primitivePolesOfContractions_quark cf
  }

/-- Beta-function theorem from the standard one-loop numerator contractions. -/
lemma beta0_from_standardContractions
    (cf : ColorFactors)
    (ms : Renormalization.MSLikeRenormalizationData)
    (hLink : OneLoopRenormalizationLink ms (primitivePolesOfContractions cf)) :
    beta0 cf = Renormalization.beta0FromCouplingPole ms.couplingPole := by
  exact beta0_from_oneLoopPoles cf ms (primitivePolesOfContractions cf)
    (primitivePoleAssumptions_of_standardContractions cf) hLink

/-- SU(N) specialization of the numerator-contraction theorem. -/
lemma beta0_suN_from_standardContractions
    (nC nF : ℝ)
    (ms : Renormalization.MSLikeRenormalizationData)
    (hLink : OneLoopRenormalizationLink ms
      (primitivePolesOfContractions (suNColorFactors nC nF))) :
    beta0 (suNColorFactors nC nF) = Renormalization.beta0FromCouplingPole ms.couplingPole := by
  exact beta0_from_standardContractions (suNColorFactors nC nF) ms hLink

end OneLoopNumeratorContractions
end QCD
end QFT
end Physlib
