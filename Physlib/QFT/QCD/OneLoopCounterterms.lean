/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.Renormalization
public import Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars
/-!

# One-Loop Counterterms from Scalar Masters

This module builds concrete one-loop renormalization-constant data from scalar
master integrals represented as Laurent expansions.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace OneLoopCounterterms

open Renormalization
open Physlib.QFT.PerturbationTheory.DimensionalRegularization
open Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars

/-- Weights used to assemble one-loop renormalization constants from a scalar master integral. -/
structure CountertermWeights : Type where
  zGCoeff : ℝ
  z3Coeff : ℝ
  z2Coeff : ℝ
  z1FCoeff : ℝ
  z1cCoeff : ℝ
  z3cCoeff : ℝ

/-- Scale a scalar master integral into a Laurent expansion contributing to a counterterm. -/
def weightedExpansion (a : ℝ) (I : ScalarMasterIntegral) : LaurentExpansionAtZero :=
  (smul a I).expansion

/-- Assemble renormalization constants from one scalar master integral and weight data. -/
def renormalizationConstantsOfMaster
    (w : CountertermWeights)
    (I : ScalarMasterIntegral) : RenormalizationConstants where
  zG := weightedExpansion w.zGCoeff I
  z3 := weightedExpansion w.z3Coeff I
  z2 := weightedExpansion w.z2Coeff I
  z1F := weightedExpansion w.z1FCoeff I
  z1c := weightedExpansion w.z1cCoeff I
  z3c := weightedExpansion w.z3cCoeff I

/-- Build MS-like renormalization data directly from a weighted scalar master integral. -/
def msLikeDataOfMaster
    (scheme : RenormalizationScheme)
    (w : CountertermWeights)
    (I : ScalarMasterIntegral) : MSLikeRenormalizationData where
  scheme := scheme
  Z := renormalizationConstantsOfMaster w I
  couplingPole := Renormalization.poleCoeff (weightedExpansion w.zGCoeff I)
  hCouplingPole := rfl

/-- The coupling pole extracted from a weighted master integral is the weight times the master pole. -/
lemma couplingPole_eq_weight_mul_masterPole
    (scheme : RenormalizationScheme)
    (w : CountertermWeights)
    (I : ScalarMasterIntegral) :
    (msLikeDataOfMaster scheme w I).couplingPole = w.zGCoeff * I.poleCoeff := by
  rfl

/-- If the scalar master has unit pole, the coupling pole equals the bare weight. -/
lemma couplingPole_eq_weight_of_unitMasterPole
    (scheme : RenormalizationScheme)
    (w : CountertermWeights)
    (I : ScalarMasterIntegral)
    (hI : I.poleCoeff = 1) :
    (msLikeDataOfMaster scheme w I).couplingPole = w.zGCoeff := by
  rw [couplingPole_eq_weight_mul_masterPole]
  simp [hI]

end OneLoopCounterterms
end QCD
end QFT
end Physlib
