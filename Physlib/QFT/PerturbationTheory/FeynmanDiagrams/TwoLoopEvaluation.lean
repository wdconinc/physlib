/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.Basic
public import Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars
/-!

# Two-Loop Evaluation

This module packages a concrete two-loop evaluation layer mirroring the existing
one-loop evaluation interface. The present implementation is still abstract at
the analytic level, but it provides the diagram data structures, master-integral
wrapper, and evaluation objects needed for a future explicit two-loop derivation.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace PerturbationTheory
namespace FeynmanDiagrams

open Physlib.QFT.PerturbationTheory.DimensionalRegularization
open Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars

/-- Two-loop master integral data packaged as a Laurent expansion. -/
structure TwoLoopMasterIntegral : Type where
  /-- Laurent expansion of the integral around `ε = 0`. -/
  expansion : LaurentExpansionAtZero

/-- Extract the pole coefficient of a two-loop master integral. -/
def TwoLoopMasterIntegral.poleCoeff (I : TwoLoopMasterIntegral) : ℝ :=
  I.expansion.poleCoeff

/-- Extract the finite part of a two-loop master integral. -/
def TwoLoopMasterIntegral.finitePart (I : TwoLoopMasterIntegral) : ℂ :=
  I.expansion.finitePart

/-- Evaluate a two-loop master integral away from `ε = 0`. -/
def TwoLoopMasterIntegral.eval (I : TwoLoopMasterIntegral) (ε : ℝ) : ℂ :=
  I.expansion.eval ε

/-- Canonical regular two-loop master integral attached to a finite complex value. -/
def regularTwoLoopMaster (z : ℂ) : TwoLoopMasterIntegral where
  expansion := regularOfComplex z

/-- A simple placeholder two-loop bubble master. -/
def twoLoopBubble (coeff : ℝ) : TwoLoopMasterIntegral where
  expansion := {
    poleCoeff := coeff
    finitePart := 0
    regularPart := fun _ => 0
  }

/-- A simple placeholder two-loop sunset master. -/
def twoLoopSunset (coeff : ℝ) : TwoLoopMasterIntegral where
  expansion := {
    poleCoeff := coeff
    finitePart := 0
    regularPart := fun _ => 0
  }

/-- A simple placeholder two-loop vertex correction master. -/
def twoLoopVertexCorrection (coeff : ℝ) : TwoLoopMasterIntegral where
  expansion := {
    poleCoeff := coeff
    finitePart := 0
    regularPart := fun _ => 0
  }

/-- Structured two-loop scalar integrand data.

This records the two loop momenta, the external momentum, numerator terms,
denominator factors, a positive regulator, and the reduced two-loop master
integral produced by evaluation.
-/
structure TwoLoopScalarIntegrand : Type where
  /-- First loop momentum. -/
  loopMomentum1 : Momentum
  /-- Second loop momentum. -/
  loopMomentum2 : Momentum
  /-- External momentum entering the diagram. -/
  externalMomentum : Momentum
  /-- Monomial numerator terms before reduction. -/
  numeratorTerms : List ScalarNumeratorTerm
  /-- Propagator denominator factors before scalar reduction. -/
  denominators : List ScalarDenominatorFactor
  /-- Dimensional regulator used in the integrand. -/
  regulator : ℝ
  /-- Positivity of the regulator. -/
  hRegulator : 0 < regulator
  /-- Two-loop master produced by evaluation. -/
  reducedMaster : TwoLoopMasterIntegral

/-- Total denominator power carried by a structured two-loop scalar integrand. -/
def TwoLoopScalarIntegrand.totalDenominatorPower (I : TwoLoopScalarIntegrand) : ℕ :=
  (I.denominators.map ScalarDenominatorFactor.power).foldl (· + ·) 0

/-- Total numerator loop degree carried by a structured two-loop scalar integrand. -/
def TwoLoopScalarIntegrand.totalLoopDegree (I : TwoLoopScalarIntegrand) : ℕ :=
  (I.numeratorTerms.map ScalarNumeratorTerm.loopDegree).foldl (· + ·) 0

/-- Total numerator external-momentum degree carried by a structured two-loop scalar integrand. -/
def TwoLoopScalarIntegrand.totalExternalDegree (I : TwoLoopScalarIntegrand) : ℕ :=
  (I.numeratorTerms.map ScalarNumeratorTerm.externalDegree).foldl (· + ·) 0

/-- Evaluate a structured two-loop scalar integrand to its master integral. -/
def TwoLoopScalarIntegrand.evaluate (I : TwoLoopScalarIntegrand) : TwoLoopMasterIntegral :=
  I.reducedMaster

/-- The evaluation of a structured two-loop scalar integrand returns its recorded reduced master. -/
@[simp] lemma TwoLoopScalarIntegrand.evaluate_eq_reducedMaster
    (I : TwoLoopScalarIntegrand) :
    I.evaluate = I.reducedMaster :=
  rfl

/-- A reduction witness from an explicit two-loop integrand to a chosen master integral. -/
structure TwoLoopScalarIntegrandReduction
    (integrand : TwoLoopScalarIntegrand) (target : TwoLoopMasterIntegral) : Prop where
  /-- The regularized integrand evaluates to the chosen master integral. -/
  hEvaluate : integrand.evaluate = target

/-- Reduction witnesses expose the target master directly. -/
lemma TwoLoopScalarIntegrandReduction.evaluate_eq
    {integrand : TwoLoopScalarIntegrand} {target : TwoLoopMasterIntegral}
    (h : TwoLoopScalarIntegrandReduction integrand target) :
    integrand.evaluate = target :=
  h.hEvaluate

/-- Concrete two-loop diagram data packaged for downstream classification and evaluation. -/
structure TwoLoopDiagramData (Label : Type) : Type where
  /-- Curated diagram label. -/
  label : Label
  /-- First loop momentum. -/
  loopMomentum1 : Momentum
  /-- Second loop momentum. -/
  loopMomentum2 : Momentum
  /-- External momentum entering the diagram. -/
  externalMomentum : Momentum
  /-- Two-loop integrand data. -/
  integrand : TwoLoopScalarIntegrand

/-- Evaluate a concrete two-loop diagram to its reduced master integral. -/
def TwoLoopDiagramData.evaluate {Label : Type} (d : TwoLoopDiagramData Label) :
    TwoLoopMasterIntegral :=
  d.integrand.evaluate

/-- The evaluation of a concrete two-loop diagram returns its recorded reduced master. -/
@[simp] lemma TwoLoopDiagramData.evaluate_eq_reducedMaster
    {Label : Type} (d : TwoLoopDiagramData Label) :
    d.evaluate = d.integrand.reducedMaster :=
  rfl

/-- A concrete two-loop evaluation object packages a diagram together with its target master. -/
structure TwoLoopDiagramEvaluation (Label : Type) : Type where
  /-- Diagram being evaluated. -/
  diagram : TwoLoopDiagramData Label
  /-- Target two-loop master integral. -/
  target : TwoLoopMasterIntegral
  /-- Evaluation witness. -/
  hEvaluate : diagram.evaluate = target

/-- Evaluation objects expose the target master integral directly. -/
lemma TwoLoopDiagramEvaluation.evaluate_eq
    {Label : Type} (E : TwoLoopDiagramEvaluation Label) :
    E.diagram.evaluate = E.target :=
  E.hEvaluate

/-- A bundled collection of two-loop diagram evaluations. -/
structure TwoLoopDiagramEvaluationBundle (Label : Type) : Type where
  /-- Evaluations indexed by any finite label set chosen downstream. -/
  evaluations : List (TwoLoopDiagramEvaluation Label)

/-- Append a new evaluation to a bundle. -/
def TwoLoopDiagramEvaluationBundle.push
    {Label : Type}
    (B : TwoLoopDiagramEvaluationBundle Label)
    (E : TwoLoopDiagramEvaluation Label) :
    TwoLoopDiagramEvaluationBundle Label where
  evaluations := B.evaluations ++ [E]

/-- Convenience bundle for a single concrete evaluation. -/
def TwoLoopDiagramEvaluationBundle.singleton
    {Label : Type}
    (E : TwoLoopDiagramEvaluation Label) :
    TwoLoopDiagramEvaluationBundle Label where
  evaluations := [E]

end FeynmanDiagrams
end PerturbationTheory
end QFT
end Physlib
