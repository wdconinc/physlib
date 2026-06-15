/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.OneLoopNumeratorContractions
public import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.Basic
public import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.OneLoopEvaluation
public import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.TopologyEnumeration
/-!

# One-Loop Diagrammatic Bridge

This module connects concrete one-loop self-energy diagram classes from the
Feynman-diagram layer to the scalar-master and numerator-contraction beta
infrastructure.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace OneLoopDiagrammaticBridge

open OneLoopBeta
open OneLoopNumeratorContractions
open Physlib.QFT.PerturbationTheory.FeynmanDiagrams
open Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars

/-- One-loop topology classes used in the QCD beta-function decomposition. -/
inductive QCDOneLoopBetaDiagramClass where
  | gluonLoop
  | ghostLoop
  | quarkLoop
  deriving DecidableEq, Repr

/-- Canonical class order for one-loop QCD beta-function topology bookkeeping. -/
def qcdOneLoopBetaClassOrder : List QCDOneLoopBetaDiagramClass :=
  [QCDOneLoopBetaDiagramClass.gluonLoop,
   QCDOneLoopBetaDiagramClass.ghostLoop,
   QCDOneLoopBetaDiagramClass.quarkLoop]

/-- Map generic one-loop topology classes to QCD beta-function classes. -/
def qcdOneLoopBetaClassOfTopologyClass
    (cls : OneLoopTopologyClass) : QCDOneLoopBetaDiagramClass :=
  match cls with
  | .gaugeSelfEnergy => QCDOneLoopBetaDiagramClass.gluonLoop
  | .ghostSelfEnergy => QCDOneLoopBetaDiagramClass.ghostLoop
  | .fermionSelfEnergy => QCDOneLoopBetaDiagramClass.quarkLoop

/-- Classifier from generic one-loop candidates to QCD beta-function classes. -/
def qcdClassifyOneLoopTopologyCandidate
    (candidate : TopologyCandidate) : Option QCDOneLoopBetaDiagramClass :=
  (classifyOneLoopTopologyCandidate candidate).map qcdOneLoopBetaClassOfTopologyClass

/-- One-loop candidate enumeration used by QCD beta-function class bookkeeping. -/
def qcdOneLoopTopologyCandidateEnumeration : List TopologyCandidate :=
  oneLoopTopologyCandidates

/-- Grouped one-loop class enumeration for the QCD beta-function workflow. -/
def qcdOneLoopTopologyClassEnumeration :
    List (QCDOneLoopBetaDiagramClass × List TopologyCandidate) :=
  enumerateClassBlocks qcdOneLoopBetaClassOrder
    qcdClassifyOneLoopTopologyCandidate qcdOneLoopTopologyCandidateEnumeration

/-- QCD one-loop class enumeration preserves canonical class order. -/
theorem qcdOneLoopTopologyClassEnumeration_map_fst :
    qcdOneLoopTopologyClassEnumeration.map Prod.fst = qcdOneLoopBetaClassOrder := by
  simpa [qcdOneLoopTopologyClassEnumeration] using
    enumerateClassBlocks_map_fst
      (classOrder := qcdOneLoopBetaClassOrder)
      (classify := qcdClassifyOneLoopTopologyCandidate)
      (candidates := qcdOneLoopTopologyCandidateEnumeration)

/-- Normalized theorem name for one-loop class-order preservation. -/
theorem qcdOneLoopTopologyClassEnumeration_preserves_classOrder :
    qcdOneLoopTopologyClassEnumeration.map Prod.fst = qcdOneLoopBetaClassOrder :=
  qcdOneLoopTopologyClassEnumeration_map_fst

/-- Classified QCD one-loop labels from the shared topology candidate source. -/
def qcdOneLoopTopologyLabels : List QCDOneLoopBetaDiagramClass :=
  qcdOneLoopTopologyCandidateEnumeration.filterMap qcdClassifyOneLoopTopologyCandidate

/-- Contributing one-loop classes entering the QCD beta-function bookkeeping. -/
def qcdContributingOneLoopBetaDiagramClasses : Finset QCDOneLoopBetaDiagramClass :=
  qcdOneLoopBetaClassOrder.toFinset

/-- Classified QCD one-loop labels match canonical class order. -/
theorem qcdOneLoopTopologyLabels_eq_canonicalOrder :
    qcdOneLoopTopologyLabels = qcdOneLoopBetaClassOrder := by
  simp [qcdOneLoopTopologyLabels,
    qcdOneLoopTopologyCandidateEnumeration,
    oneLoopTopologyCandidates,
    classifyOneLoopTopologyCandidate,
    qcdClassifyOneLoopTopologyCandidate,
    qcdOneLoopBetaClassOfTopologyClass,
    enumerateCandidates,
    oneLoopTopologyConstraints,
    graphOfConstraint,
    candidateOfGraph,
    allListsOfLength,
    qcdOneLoopBetaClassOrder]

/-- Set-level completeness for QCD one-loop topology class labels. -/
theorem qcdOneLoopTopologyLabels_toFinset_eq_contributingSet :
    qcdOneLoopTopologyLabels.toFinset = qcdContributingOneLoopBetaDiagramClasses := by
  simp [qcdOneLoopTopologyLabels_eq_canonicalOrder,
    qcdContributingOneLoopBetaDiagramClasses,
    qcdOneLoopBetaClassOrder]

/-- Read the primitive pole contribution associated to a QCD one-loop class. -/
def primitivePoleOfClass
    (p : PrimitivePoles) (cls : QCDOneLoopBetaDiagramClass) : ℝ :=
  match cls with
  | .gluonLoop => p.gluon
  | .ghostLoop => p.ghost
  | .quarkLoop => p.quark

/-- The classwise primitive-pole sum reproduces the total one-loop pole. -/
lemma sum_primitivePoleOfClass_eq_total
    (p : PrimitivePoles) :
    (qcdOneLoopBetaClassOrder.map (primitivePoleOfClass p)).sum = p.total := by
  simp [qcdOneLoopBetaClassOrder, primitivePoleOfClass, PrimitivePoles.total]

/-- Extract primitive poles from a concrete one-loop self-energy diagram bundle by using
the standard numerator contractions and the canonical scalar-master identifications. -/
def primitivePolesOfDiagramBundle
    (cf : ColorFactors)
    {rules : GaugeFeynmanRules}
    (bundle : OneLoopSelfEnergyDiagramBundle rules)
    (_hEval : OneLoopSelfEnergyEvaluationAssumptions bundle) : PrimitivePoles :=
  primitivePolesOfContractions cf

/-- Concrete one-loop self-energy diagram evaluation discharges the primitive pole contracts. -/
lemma primitivePoleAssumptions_of_diagramBundle
    (cf : ColorFactors)
    {rules : GaugeFeynmanRules}
    (bundle : OneLoopSelfEnergyDiagramBundle rules)
    (hEval : OneLoopSelfEnergyEvaluationAssumptions bundle) :
    PrimitivePoleAssumptions cf (primitivePolesOfDiagramBundle cf bundle hEval) := by
  simpa [primitivePolesOfDiagramBundle] using primitivePoleAssumptions_of_standardContractions cf

/-- Diagrammatic version of the one-loop beta theorem. -/
lemma beta0_fromDiagramBundle
    (cf : ColorFactors)
    (ms : Renormalization.MSLikeRenormalizationData)
    {rules : GaugeFeynmanRules}
    (bundle : OneLoopSelfEnergyDiagramBundle rules)
    (hEval : OneLoopSelfEnergyEvaluationAssumptions bundle)
    (hLink : OneLoopRenormalizationLink ms (primitivePolesOfDiagramBundle cf bundle hEval)) :
    beta0 cf = Renormalization.beta0FromCouplingPole ms.couplingPole := by
  simpa [primitivePolesOfDiagramBundle] using
    beta0_from_standardContractions cf ms hLink

/-- SU(N) specialization of the diagrammatic one-loop beta theorem. -/
lemma beta0_suN_fromDiagramBundle
    (nC nF : ℝ)
    (ms : Renormalization.MSLikeRenormalizationData)
    {rules : GaugeFeynmanRules}
    (bundle : OneLoopSelfEnergyDiagramBundle rules)
    (hEval : OneLoopSelfEnergyEvaluationAssumptions bundle)
    (hLink : OneLoopRenormalizationLink ms
      (primitivePolesOfDiagramBundle (suNColorFactors nC nF) bundle hEval)) :
    beta0 (suNColorFactors nC nF) = Renormalization.beta0FromCouplingPole ms.couplingPole := by
  simpa [primitivePolesOfDiagramBundle] using
    beta0_suN_from_standardContractions nC nF ms hLink

/-- Group-level SU(N) corollary through the existing `beta0Of` interface. -/
lemma beta0Of_suN_fromDiagramBundle
    (nC nF : ℝ)
    (ms : Renormalization.MSLikeRenormalizationData)
    {rules : GaugeFeynmanRules}
    (bundle : OneLoopSelfEnergyDiagramBundle rules)
    (hEval : OneLoopSelfEnergyEvaluationAssumptions bundle)
    (hLink : OneLoopRenormalizationLink ms
      (primitivePolesOfDiagramBundle (suNColorFactors nC nF) bundle hEval)) :
    beta0Of (SUN nC) nF = Renormalization.beta0FromCouplingPole ms.couplingPole := by
  calc
    beta0Of (SUN nC) nF
        = beta0 (suNColorFactors nC nF) :=
          RepresentationColor.beta0Of_suN_eq_from_representation nC nF
    _ = Renormalization.beta0FromCouplingPole ms.couplingPole :=
          beta0_suN_fromDiagramBundle nC nF ms bundle hEval hLink

/-- Concrete loop-integral data discharge the primitive pole contracts for a diagram bundle. -/
lemma primitivePoleAssumptions_of_loopIntegralData
    (cf : ColorFactors)
    {rules : GaugeFeynmanRules}
    (bundle : OneLoopSelfEnergyDiagramBundle rules)
    (data : OneLoopSelfEnergyLoopIntegralDataBundle bundle) :
    PrimitivePoleAssumptions cf
      (primitivePolesOfDiagramBundle cf bundle
        (oneLoopSelfEnergyEvaluationAssumptionsOfLoopIntegralData data)) := by
  exact primitivePoleAssumptions_of_diagramBundle cf bundle
    (oneLoopSelfEnergyEvaluationAssumptionsOfLoopIntegralData data)

/-- Diagrammatic beta-function theorem using explicit loop-integral evaluation data. -/
lemma beta0_fromLoopIntegralData
    (cf : ColorFactors)
    (ms : Renormalization.MSLikeRenormalizationData)
    {rules : GaugeFeynmanRules}
    (bundle : OneLoopSelfEnergyDiagramBundle rules)
    (data : OneLoopSelfEnergyLoopIntegralDataBundle bundle)
    (hLink : OneLoopRenormalizationLink ms
      (primitivePolesOfDiagramBundle cf bundle
        (oneLoopSelfEnergyEvaluationAssumptionsOfLoopIntegralData data))) :
    beta0 cf = Renormalization.beta0FromCouplingPole ms.couplingPole := by
  exact beta0_fromDiagramBundle cf ms bundle
    (oneLoopSelfEnergyEvaluationAssumptionsOfLoopIntegralData data) hLink

/-- SU(N) specialization using explicit loop-integral evaluation data. -/
lemma beta0_suN_fromLoopIntegralData
    (nC nF : ℝ)
    (ms : Renormalization.MSLikeRenormalizationData)
    {rules : GaugeFeynmanRules}
    (bundle : OneLoopSelfEnergyDiagramBundle rules)
    (data : OneLoopSelfEnergyLoopIntegralDataBundle bundle)
    (hLink : OneLoopRenormalizationLink ms
      (primitivePolesOfDiagramBundle (suNColorFactors nC nF) bundle
        (oneLoopSelfEnergyEvaluationAssumptionsOfLoopIntegralData data))) :
    beta0 (suNColorFactors nC nF) = Renormalization.beta0FromCouplingPole ms.couplingPole := by
  exact beta0_suN_fromDiagramBundle nC nF ms bundle
    (oneLoopSelfEnergyEvaluationAssumptionsOfLoopIntegralData data) hLink

end OneLoopDiagrammaticBridge
end QCD
end QFT
end Physlib
