/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.Basic
public import Physlib.QFT.PerturbationTheory.DimensionalRegularization.TensorReduction
/-!

# One-Loop Self-Energy Evaluation

This module replaces the purely abstract scalar-master extraction step by
concrete loop-integral evaluation data for one-loop self-energy diagrams.

The present implementation keeps the loop-integral payload minimal while making
the evaluation step explicit and theorem-producing.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace PerturbationTheory
namespace FeynmanDiagrams

open Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars
open Physlib.QFT.PerturbationTheory.DimensionalRegularization.TensorReduction

/-- Concrete loop-integral data attached to a gauge-boson self-energy diagram. -/
structure GaugeBosonSelfEnergyLoopIntegralData
    {rules : GaugeFeynmanRules}
    (diag : GaugeBosonSelfEnergyDiagram rules) : Type where
  /-- Structured loop integrand for the evaluation. -/
  integrand : OneLoopScalarIntegrand
  /-- Structured rank-two tensor integrand before isotropic tensor reduction. -/
  tensorIntegrand : RankTwoTensorIntegrand
  /-- The scalar integrand is extracted from the tensor integrand. -/
  hScalarIntegrand : tensorIntegrand.scalarIntegrand = integrand
  /-- Tensor reduction evaluates to the canonical gauge-boson scalar master. -/
  hTensorReduction : tensorIntegrand.reduce.scalarMaster = gaugeBosonSelfEnergyMaster

/-- Concrete loop-integral data attached to a ghost self-energy diagram. -/
structure GhostSelfEnergyLoopIntegralData
    {rules : GaugeFeynmanRules}
    (diag : GhostSelfEnergyDiagram rules) : Type where
  /-- Structured loop integrand for the evaluation. -/
  integrand : OneLoopScalarIntegrand
  /-- Structured rank-two tensor integrand before isotropic tensor reduction. -/
  tensorIntegrand : RankTwoTensorIntegrand
  /-- The scalar integrand is extracted from the tensor integrand. -/
  hScalarIntegrand : tensorIntegrand.scalarIntegrand = integrand
  /-- Tensor reduction evaluates to the canonical ghost scalar master. -/
  hTensorReduction : tensorIntegrand.reduce.scalarMaster = ghostSelfEnergyMaster

/-- Concrete loop-integral data attached to a fermion self-energy diagram. -/
structure FermionSelfEnergyLoopIntegralData
    {rules : GaugeFeynmanRules}
    (diag : FermionSelfEnergyDiagram rules) : Type where
  /-- Structured loop integrand for the evaluation. -/
  integrand : OneLoopScalarIntegrand
  /-- Structured rank-two tensor integrand before isotropic tensor reduction. -/
  tensorIntegrand : RankTwoTensorIntegrand
  /-- The scalar integrand is extracted from the tensor integrand. -/
  hScalarIntegrand : tensorIntegrand.scalarIntegrand = integrand
  /-- Tensor reduction evaluates to the canonical fermion scalar master. -/
  hTensorReduction : tensorIntegrand.reduce.scalarMaster = fermionSelfEnergyMaster

/-- Bundled loop-integral evaluation data for the three one-loop self-energy classes. -/
structure OneLoopSelfEnergyLoopIntegralDataBundle
    {rules : GaugeFeynmanRules}
    (bundle : OneLoopSelfEnergyDiagramBundle rules) : Type where
  gaugeBoson : GaugeBosonSelfEnergyLoopIntegralData bundle.gaugeBoson
  ghost : GhostSelfEnergyLoopIntegralData bundle.ghost
  fermion : FermionSelfEnergyLoopIntegralData bundle.fermion

/-- Canonical evaluation data for a gauge-boson self-energy diagram. -/
def gaugeBosonSelfEnergyLoopIntegralDataOf
    {rules : GaugeFeynmanRules}
    (diag : GaugeBosonSelfEnergyDiagram rules) :
    GaugeBosonSelfEnergyLoopIntegralData diag where
  integrand := gaugeBosonSelfEnergyIntegrand
  tensorIntegrand := gaugeBosonSelfEnergyTensorIntegrand 1
  hScalarIntegrand := rfl
  hTensorReduction := by
    simp

/-- Canonical evaluation data for a ghost self-energy diagram. -/
def ghostSelfEnergyLoopIntegralDataOf
    {rules : GaugeFeynmanRules}
    (diag : GhostSelfEnergyDiagram rules) :
    GhostSelfEnergyLoopIntegralData diag where
  integrand := ghostSelfEnergyIntegrand
  tensorIntegrand := ghostSelfEnergyTensorIntegrand 1
  hScalarIntegrand := rfl
  hTensorReduction := by
    simp

/-- Canonical evaluation data for a fermion self-energy diagram. -/
def fermionSelfEnergyLoopIntegralDataOf
    {rules : GaugeFeynmanRules}
    (diag : FermionSelfEnergyDiagram rules) :
    FermionSelfEnergyLoopIntegralData diag where
  integrand := fermionSelfEnergyIntegrand
  tensorIntegrand := fermionSelfEnergyTensorIntegrand 1
  hScalarIntegrand := rfl
  hTensorReduction := by
    simp

/-- Canonical bundled loop-integral data for a one-loop self-energy diagram bundle. -/
def oneLoopSelfEnergyLoopIntegralDataOf
    {rules : GaugeFeynmanRules}
    (bundle : OneLoopSelfEnergyDiagramBundle rules) :
    OneLoopSelfEnergyLoopIntegralDataBundle bundle where
  gaugeBoson := gaugeBosonSelfEnergyLoopIntegralDataOf bundle.gaugeBoson
  ghost := ghostSelfEnergyLoopIntegralDataOf bundle.ghost
  fermion := fermionSelfEnergyLoopIntegralDataOf bundle.fermion

/-- Concrete evaluation theorem for the gauge-boson self-energy diagram. -/
lemma evaluateGaugeBosonSelfEnergyDiagram
    {rules : GaugeFeynmanRules}
    {diag : GaugeBosonSelfEnergyDiagram rules}
    (data : GaugeBosonSelfEnergyLoopIntegralData diag) :
    data.integrand.evaluate = gaugeBosonSelfEnergyMaster :=
by
  have hReduce : data.tensorIntegrand.scalarIntegrand.evaluate = gaugeBosonSelfEnergyMaster := by
    simpa [RankTwoTensorIntegrand.reduce_scalarMaster] using data.hTensorReduction
  simpa [data.hScalarIntegrand] using hReduce

/-- Concrete evaluation theorem for the ghost self-energy diagram. -/
lemma evaluateGhostSelfEnergyDiagram
    {rules : GaugeFeynmanRules}
    {diag : GhostSelfEnergyDiagram rules}
    (data : GhostSelfEnergyLoopIntegralData diag) :
    data.integrand.evaluate = ghostSelfEnergyMaster :=
by
  have hReduce : data.tensorIntegrand.scalarIntegrand.evaluate = ghostSelfEnergyMaster := by
    simpa [RankTwoTensorIntegrand.reduce_scalarMaster] using data.hTensorReduction
  simpa [data.hScalarIntegrand] using hReduce

/-- Concrete evaluation theorem for the fermion self-energy diagram. -/
lemma evaluateFermionSelfEnergyDiagram
    {rules : GaugeFeynmanRules}
    {diag : FermionSelfEnergyDiagram rules}
    (data : FermionSelfEnergyLoopIntegralData diag) :
    data.integrand.evaluate = fermionSelfEnergyMaster :=
by
  have hReduce : data.tensorIntegrand.scalarIntegrand.evaluate = fermionSelfEnergyMaster := by
    simpa [RankTwoTensorIntegrand.reduce_scalarMaster] using data.hTensorReduction
  simpa [data.hScalarIntegrand] using hReduce

/-- Explicit loop-integral data produce the scalar-master extraction assumptions used by
the one-loop beta-function bridge. -/
def oneLoopSelfEnergyEvaluationAssumptionsOfLoopIntegralData
    {rules : GaugeFeynmanRules}
    {bundle : OneLoopSelfEnergyDiagramBundle rules}
    (data : OneLoopSelfEnergyLoopIntegralDataBundle bundle) :
    OneLoopSelfEnergyEvaluationAssumptions bundle where
  gaugeBosonMaster := data.gaugeBoson.integrand.evaluate
  ghostMaster := data.ghost.integrand.evaluate
  fermionMaster := data.fermion.integrand.evaluate
  hGaugeBosonMaster := evaluateGaugeBosonSelfEnergyDiagram data.gaugeBoson
  hGhostMaster := evaluateGhostSelfEnergyDiagram data.ghost
  hFermionMaster := evaluateFermionSelfEnergyDiagram data.fermion

end FeynmanDiagrams
end PerturbationTheory
end QFT
end Physlib
