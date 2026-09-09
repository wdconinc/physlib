/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.DimensionalRegularization.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
/-!

# One-Loop Scalar Master Integrals

This module records the minimal scalar one-loop master integrals needed by the
QCD beta-function pipeline, represented as Laurent expansions at
$\varepsilon = 0$.

The intent is to provide concrete pole-carrying analytic data before tensor
reduction and numerator algebra are introduced.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace PerturbationTheory
namespace DimensionalRegularization
namespace OneLoopScalars

/-- Lorentz index used by the explicit one-loop integrand payload. -/
abbrev LorentzIndex := Fin 4

/-- A symbolic loop or external four-momentum. -/
abbrev LoopMomentum := Lorentz.Vector 3

/-- The zero four-momentum. -/
def zeroLoopMomentum : LoopMomentum := 0

/-- A monomial numerator term in loop and external momentum components. -/
structure ScalarNumeratorTerm : Type where
  /-- Overall complex coefficient. -/
  coeff : ℂ
  /-- Powers of loop-momentum components. -/
  loopPowers : LorentzIndex → ℕ
  /-- Powers of external-momentum components. -/
  externalPowers : LorentzIndex → ℕ

/-- Total loop-momentum degree carried by a numerator term. -/
def ScalarNumeratorTerm.loopDegree (term : ScalarNumeratorTerm) : ℕ :=
  ((List.finRange 4).map (fun μ => term.loopPowers μ)).foldl (· + ·) 0

/-- Total external-momentum degree carried by a numerator term. -/
def ScalarNumeratorTerm.externalDegree (term : ScalarNumeratorTerm) : ℕ :=
  ((List.finRange 4).map (fun μ => term.externalPowers μ)).foldl (· + ·) 0

/-- A scalar propagator denominator factor in the loop integrand. -/
structure ScalarDenominatorFactor : Type where
  /-- Shift applied to the loop momentum before squaring. -/
  shift : LoopMomentum
  /-- Mass squared appearing in the shifted quadratic form. -/
  massSq : ℝ
  /-- Power of this denominator factor. -/
  power : ℕ

/-- Predicate recording that a denominator factor is massless. -/
def ScalarDenominatorFactor.IsMassless (D : ScalarDenominatorFactor) : Prop :=
  D.massSq = 0

/-- Unit scalar numerator term. -/
def unitNumeratorTerm : ScalarNumeratorTerm where
  coeff := 1
  loopPowers := fun _ => 0
  externalPowers := fun _ => 0

/-- A simple massless denominator factor. -/
def masslessDenominatorFactor : ScalarDenominatorFactor where
  shift := zeroLoopMomentum
  massSq := 0
  power := 1

/-- Scalar one-loop master integral data packaged as a Laurent expansion. -/
structure ScalarMasterIntegral : Type where
  /-- Laurent expansion of the integral around $\varepsilon = 0$. -/
  expansion : LaurentExpansionAtZero

/-- Minimal structured one-loop scalar integrand data.

This records the coefficient and denominator shape of a scalar one-loop integrand,
together with the Laurent expansion obtained after dimensional regularization and
integration. The `reducedMaster` field is the target scalar master reached by the
evaluation/reduction step.
-/
structure OneLoopScalarIntegrand : Type where
  /-- Symbolic loop momentum integrated over in the one-loop integral. -/
  loopMomentum : LoopMomentum
  /-- External momentum entering the self-energy graph. -/
  externalMomentum : LoopMomentum
  /-- Monomial numerator terms before tensor reduction. -/
  numeratorTerms : List ScalarNumeratorTerm
  /-- Propagator denominator factors before scalar reduction. -/
  denominators : List ScalarDenominatorFactor
  /-- Dimensional regulator value used in the integrand. -/
  regulator : ℝ
  /-- Positivity of the regulator. -/
  hRegulator : 0 < regulator
  /-- Scalar master produced by evaluating the regularized integral. -/
  reducedMaster : ScalarMasterIntegral

/-- Total denominator power carried by a structured scalar integrand. -/
def OneLoopScalarIntegrand.totalDenominatorPower (I : OneLoopScalarIntegrand) : ℕ :=
  (I.denominators.map ScalarDenominatorFactor.power).foldl (· + ·) 0

/-- Total numerator loop degree carried by a structured scalar integrand. -/
def OneLoopScalarIntegrand.totalLoopDegree (I : OneLoopScalarIntegrand) : ℕ :=
  (I.numeratorTerms.map ScalarNumeratorTerm.loopDegree).foldl (· + ·) 0

/-- Total numerator external-momentum degree carried by a structured scalar integrand. -/
def OneLoopScalarIntegrand.totalExternalDegree (I : OneLoopScalarIntegrand) : ℕ :=
  (I.numeratorTerms.map ScalarNumeratorTerm.externalDegree).foldl (· + ·) 0

/-- Evaluate a structured one-loop scalar integrand to its scalar master. -/
def OneLoopScalarIntegrand.evaluate (I : OneLoopScalarIntegrand) : ScalarMasterIntegral :=
  I.reducedMaster

/-- The evaluation of a structured scalar integrand returns its recorded reduced master. -/
@[simp] lemma OneLoopScalarIntegrand.evaluate_eq_reducedMaster (I : OneLoopScalarIntegrand) :
    I.evaluate = I.reducedMaster :=
  rfl

/-- A reduction witness from an explicit integrand to a chosen scalar master. -/
structure ScalarIntegrandReduction
    (integrand : OneLoopScalarIntegrand) (target : ScalarMasterIntegral) : Prop where
  /-- The regularized integrand evaluates to the chosen scalar master. -/
  hEvaluate : integrand.evaluate = target

/-- Reduction witnesses expose the target scalar master directly. -/
lemma ScalarIntegrandReduction.evaluate_eq
    {integrand : OneLoopScalarIntegrand} {target : ScalarMasterIntegral}
    (h : ScalarIntegrandReduction integrand target) :
    integrand.evaluate = target :=
  h.hEvaluate

/-- Pole coefficient of a scalar master integral. -/
def ScalarMasterIntegral.poleCoeff (I : ScalarMasterIntegral) : ℝ :=
  DimensionalRegularization.poleCoeff I.expansion

/-- Finite part of a scalar master integral. -/
def ScalarMasterIntegral.finitePart (I : ScalarMasterIntegral) : ℂ :=
  I.expansion.finitePart

/-- Evaluate a scalar master integral away from $\varepsilon = 0$. -/
def ScalarMasterIntegral.eval (I : ScalarMasterIntegral) (ε : ℝ) : ℂ :=
  I.expansion.eval ε

/-- A massless one-loop two-point integral with a prescribed simple pole.

The coefficient parameter isolates the normalization conventions coming from the
integration measure and tensor reduction. -/
def masslessBubble (coeff : ℝ) : ScalarMasterIntegral where
  expansion := {
    poleCoeff := coeff
    finitePart := 0
    regularPart := fun _ => 0
  }

/-- A massive one-loop two-point integral with a prescribed simple pole. -/
def massiveBubble (coeff : ℝ) (massScale : ℂ) : ScalarMasterIntegral where
  expansion := {
    poleCoeff := coeff
    finitePart := massScale
    regularPart := fun _ => 0
  }

/-- A one-loop tadpole integral with a prescribed simple pole. -/
def tadpole (coeff : ℝ) (finite : ℂ) : ScalarMasterIntegral where
  expansion := {
    poleCoeff := coeff
    finitePart := finite
    regularPart := fun _ => 0
  }

/-- Pole extraction from the massless bubble returns the chosen coefficient. -/
@[simp] lemma poleCoeff_masslessBubble (coeff : ℝ) :
    (masslessBubble coeff).poleCoeff = coeff :=
  rfl

/-- Pole extraction from the massive bubble returns the chosen coefficient. -/
@[simp] lemma poleCoeff_massiveBubble (coeff : ℝ) (massScale : ℂ) :
    (massiveBubble coeff massScale).poleCoeff = coeff :=
  rfl

/-- Pole extraction from the tadpole returns the chosen coefficient. -/
@[simp] lemma poleCoeff_tadpole (coeff : ℝ) (finite : ℂ) :
    (tadpole coeff finite).poleCoeff = coeff :=
  rfl

/-- A regular scalar integral has zero pole coefficient. -/
def regularIntegral (finite : ℂ) : ScalarMasterIntegral where
  expansion := regularOfComplex finite

/-- Pole extraction vanishes on regular scalar integrals. -/
@[simp] lemma poleCoeff_regularIntegral (finite : ℂ) :
    (regularIntegral finite).poleCoeff = 0 :=
  rfl

/-- Linear combination of scalar master integrals at the level of pole data.

This is the simplest combination operation needed to assemble one-loop diagram
classes from scalar masters. The regular parts are combined pointwise. -/
def add (I J : ScalarMasterIntegral) : ScalarMasterIntegral where
  expansion := {
    poleCoeff := I.poleCoeff + J.poleCoeff
    finitePart := I.finitePart + J.finitePart
    regularPart := fun ε => I.expansion.regularPart ε + J.expansion.regularPart ε
  }

/-- Scalar multiplication of a master integral. -/
def smul (a : ℝ) (I : ScalarMasterIntegral) : ScalarMasterIntegral where
  expansion := {
    poleCoeff := a * I.poleCoeff
    finitePart := (a : ℂ) * I.finitePart
    regularPart := fun ε => (a : ℂ) * I.expansion.regularPart ε
  }

/-- Pole coefficients add under scalar-master addition. -/
@[simp] lemma poleCoeff_add (I J : ScalarMasterIntegral) :
    (add I J).poleCoeff = I.poleCoeff + J.poleCoeff :=
  rfl

/-- Pole coefficients scale linearly under real scalar multiplication. -/
@[simp] lemma poleCoeff_smul (a : ℝ) (I : ScalarMasterIntegral) :
    (smul a I).poleCoeff = a * I.poleCoeff :=
  rfl

/-- Prototype massless one-loop gauge-boson self-energy master. -/
def gaugeBosonSelfEnergyMaster : ScalarMasterIntegral :=
  masslessBubble 1

/-- Prototype ghost self-energy master. -/
def ghostSelfEnergyMaster : ScalarMasterIntegral :=
  masslessBubble 1

/-- Prototype fermion self-energy master. -/
def fermionSelfEnergyMaster : ScalarMasterIntegral :=
  masslessBubble 1

/-- Structured scalar integrand for the one-loop gauge-boson self-energy master. -/
def gaugeBosonSelfEnergyIntegrand : OneLoopScalarIntegrand where
  loopMomentum := zeroLoopMomentum
  externalMomentum := zeroLoopMomentum
  numeratorTerms := [unitNumeratorTerm]
  denominators := [masslessDenominatorFactor, masslessDenominatorFactor]
  regulator := 1
  hRegulator := by norm_num
  reducedMaster := gaugeBosonSelfEnergyMaster

/-- Structured scalar integrand for the one-loop ghost self-energy master. -/
def ghostSelfEnergyIntegrand : OneLoopScalarIntegrand where
  loopMomentum := zeroLoopMomentum
  externalMomentum := zeroLoopMomentum
  numeratorTerms := [unitNumeratorTerm]
  denominators := [masslessDenominatorFactor, masslessDenominatorFactor]
  regulator := 1
  hRegulator := by norm_num
  reducedMaster := ghostSelfEnergyMaster

/-- Structured scalar integrand for the one-loop fermion self-energy master. -/
def fermionSelfEnergyIntegrand : OneLoopScalarIntegrand where
  loopMomentum := zeroLoopMomentum
  externalMomentum := zeroLoopMomentum
  numeratorTerms := [unitNumeratorTerm]
  denominators := [masslessDenominatorFactor, masslessDenominatorFactor]
  regulator := 1
  hRegulator := by norm_num
  reducedMaster := fermionSelfEnergyMaster

/-- The canonical one-loop self-energy scalar integrands have total denominator power two. -/
@[simp] lemma gaugeBosonSelfEnergyIntegrand_totalDenominatorPower :
    gaugeBosonSelfEnergyIntegrand.totalDenominatorPower = 2 :=
  rfl

/-- The canonical ghost scalar integrand has total denominator power two. -/
@[simp] lemma ghostSelfEnergyIntegrand_totalDenominatorPower :
    ghostSelfEnergyIntegrand.totalDenominatorPower = 2 :=
  rfl

/-- The canonical fermion scalar integrand has total denominator power two. -/
@[simp] lemma fermionSelfEnergyIntegrand_totalDenominatorPower :
    fermionSelfEnergyIntegrand.totalDenominatorPower = 2 :=
  rfl

/-- The gauge-boson self-energy integrand reduces to the canonical scalar master. -/
@[simp] lemma evaluate_gaugeBosonSelfEnergyIntegrand :
    gaugeBosonSelfEnergyIntegrand.evaluate = gaugeBosonSelfEnergyMaster :=
  rfl

/-- The ghost self-energy integrand reduces to the canonical scalar master. -/
@[simp] lemma evaluate_ghostSelfEnergyIntegrand :
    ghostSelfEnergyIntegrand.evaluate = ghostSelfEnergyMaster :=
  rfl

/-- The fermion self-energy integrand reduces to the canonical scalar master. -/
@[simp] lemma evaluate_fermionSelfEnergyIntegrand :
    fermionSelfEnergyIntegrand.evaluate = fermionSelfEnergyMaster :=
  rfl

/-- Canonical reduction witness for the gauge-boson self-energy scalar integrand. -/
def reduction_gaugeBosonSelfEnergyIntegrand :
    ScalarIntegrandReduction gaugeBosonSelfEnergyIntegrand gaugeBosonSelfEnergyMaster where
  hEvaluate := evaluate_gaugeBosonSelfEnergyIntegrand

/-- Canonical reduction witness for the ghost self-energy scalar integrand. -/
def reduction_ghostSelfEnergyIntegrand :
    ScalarIntegrandReduction ghostSelfEnergyIntegrand ghostSelfEnergyMaster where
  hEvaluate := evaluate_ghostSelfEnergyIntegrand

/-- Canonical reduction witness for the fermion self-energy scalar integrand. -/
def reduction_fermionSelfEnergyIntegrand :
    ScalarIntegrandReduction fermionSelfEnergyIntegrand fermionSelfEnergyMaster where
  hEvaluate := evaluate_fermionSelfEnergyIntegrand

end OneLoopScalars
end DimensionalRegularization
end PerturbationTheory
end QFT
end Physlib
