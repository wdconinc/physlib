/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.OneLoopBeta
public import Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars
/-!

# One-Loop Beta Data from Scalar Masters

This module bridges scalar master integrals to the existing `PrimitivePoles`
interface used by the one-loop QCD beta-function assembly theorem.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace OneLoopBetaFromScalars

open OneLoopBeta
open Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars

/-- Weights used to read primitive pole contributions from scalar master integrals. -/
structure PrimitivePoleWeights : Type where
  gluonCoeff : ℝ
  ghostCoeff : ℝ
  quarkCoeff : ℝ

/-- Build primitive one-loop pole contributions from scalar master integrals. -/
def primitivePolesOfMasters
    (w : PrimitivePoleWeights)
    (gluonMaster ghostMaster quarkMaster : ScalarMasterIntegral) : PrimitivePoles where
  gluon := w.gluonCoeff * gluonMaster.poleCoeff
  ghost := w.ghostCoeff * ghostMaster.poleCoeff
  quark := w.quarkCoeff * quarkMaster.poleCoeff

/-- If the scalar masters have unit pole and the weights match the expected color coefficients,
then the resulting primitive poles satisfy the one-loop beta contracts. -/
lemma primitivePoleAssumptions_of_unitMasterPoles
    (cf : ColorFactors)
    (w : PrimitivePoleWeights)
    (gluonMaster ghostMaster quarkMaster : ScalarMasterIntegral)
    (hgMaster : gluonMaster.poleCoeff = 1)
    (hGhostMaster : ghostMaster.poleCoeff = 1)
    (hqMaster : quarkMaster.poleCoeff = 1)
    (hgCoeff : w.gluonCoeff = (5 / 3) * cf.cA)
    (hGhostCoeff : w.ghostCoeff = 2 * cf.cA)
    (hqCoeff : w.quarkCoeff = -(4 / 3) * cf.tF * cf.nF) :
    PrimitivePoleAssumptions cf (primitivePolesOfMasters w gluonMaster ghostMaster quarkMaster) := by
  refine {
    gluon_eq := ?_
    ghost_eq := ?_
    quark_eq := ?_
  }
  · simp [primitivePolesOfMasters, hgMaster, hgCoeff]
  · simp [primitivePolesOfMasters, hGhostMaster, hGhostCoeff]
  · simp [primitivePolesOfMasters, hqMaster, hqCoeff]

/-- Scalar-master version of the one-loop beta theorem.

Once scalar master poles and coefficient weights are known, the existing
`OneLoopBeta` assembly theorem delivers the reconstructed one-loop beta coefficient. -/
lemma beta0_fromScalarMasters
    (cf : ColorFactors)
    (ms : Renormalization.MSLikeRenormalizationData)
    (w : PrimitivePoleWeights)
    (gluonMaster ghostMaster quarkMaster : ScalarMasterIntegral)
    (hMasters : PrimitivePoleAssumptions cf
      (primitivePolesOfMasters w gluonMaster ghostMaster quarkMaster))
    (hLink : OneLoopRenormalizationLink ms
      (primitivePolesOfMasters w gluonMaster ghostMaster quarkMaster)) :
    beta0 cf = Renormalization.beta0FromCouplingPole ms.couplingPole := by
  exact beta0_from_oneLoopPoles cf ms
    (primitivePolesOfMasters w gluonMaster ghostMaster quarkMaster) hMasters hLink

end OneLoopBetaFromScalars
end QCD
end QFT
end Physlib
