/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars
/-!

# One-Loop Tensor Reduction

This module packages the minimal tensor-reduction layer needed for the one-loop
beta-function pipeline.

The current scope is restricted to isotropic rank-two reductions of the form

$$
  \int k_\mu k_\nu f(k^2)
  \rightsquigarrow
  g_{\mu\nu} \cdot C \cdot I,
$$

where $I$ is a scalar master integral carrying the Laurent-pole information.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace PerturbationTheory
namespace DimensionalRegularization
namespace TensorReduction

open OneLoopScalars

/-- Lorentz index used in tensor-reduction formulas. -/
abbrev LorentzIndex := Fin 4

/-- Minkowski metric entry in signature $(+,-,-,-)$. -/
def minkowskiMetricEntry (μ ν : LorentzIndex) : ℝ :=
  if μ = ν then
    if μ.1 = 0 then 1 else -1
  else
    0

/-- Rank-two Lorentz tensor with complex coefficients. -/
abbrev RankTwoLorentzTensor := LorentzIndex → LorentzIndex → ℂ

/-- Result of reducing a rank-two tensor integral to a scalar master. -/
structure RankTwoReductionResult : Type where
  /-- Scalar prefactor multiplying the metric tensor. -/
  metricCoeff : ℝ
  /-- Underlying scalar master integral. -/
  scalarMaster : ScalarMasterIntegral

/-- A structured rank-two tensor integrand before tensor reduction. -/
structure RankTwoTensorIntegrand : Type where
  /-- Scalar coefficient multiplying the Lorentz tensor numerator. -/
  metricCoeff : ℝ
  /-- Underlying scalar loop integrand after numerator simplification. -/
  scalarIntegrand : OneLoopScalarIntegrand

/-- Pole contribution carried by a reduced rank-two tensor integral. -/
def RankTwoReductionResult.poleContribution (R : RankTwoReductionResult) : ℝ :=
  R.metricCoeff * R.scalarMaster.poleCoeff

/-- Reconstruct the reduced tensor from a rank-two reduction result. -/
def RankTwoReductionResult.toTensor (R : RankTwoReductionResult) : RankTwoLorentzTensor :=
  fun μ ν =>
    ((R.metricCoeff : ℂ) * (minkowskiMetricEntry μ ν : ℂ)) * (R.scalarMaster.poleCoeff : ℂ)

/-- Canonical isotropic rank-two reduction against a scalar master integral. -/
def isotropicRankTwoReduction (coeff : ℝ) (I : ScalarMasterIntegral) : RankTwoReductionResult where
  metricCoeff := coeff
  scalarMaster := I

/-- The isotropic reduction keeps the input tensor coefficient. -/
@[simp] lemma isotropicRankTwoReduction_metricCoeff (coeff : ℝ) (I : ScalarMasterIntegral) :
    (isotropicRankTwoReduction coeff I).metricCoeff = coeff :=
  rfl

/-- The isotropic reduction keeps the input scalar master integral. -/
@[simp] lemma isotropicRankTwoReduction_scalarMaster (coeff : ℝ) (I : ScalarMasterIntegral) :
    (isotropicRankTwoReduction coeff I).scalarMaster = I :=
  rfl

/-- Reduce a structured rank-two tensor integrand by evaluating its scalar part first. -/
def RankTwoTensorIntegrand.reduce (I : RankTwoTensorIntegrand) : RankTwoReductionResult :=
  isotropicRankTwoReduction I.metricCoeff I.scalarIntegrand.evaluate

/-- The reduced scalar master is the evaluation of the scalar integrand. -/
@[simp] lemma RankTwoTensorIntegrand.reduce_scalarMaster (I : RankTwoTensorIntegrand) :
    I.reduce.scalarMaster = I.scalarIntegrand.evaluate :=
  rfl

/-- The reduced metric coefficient is inherited from the tensor integrand. -/
@[simp] lemma RankTwoTensorIntegrand.reduce_metricCoeff (I : RankTwoTensorIntegrand) :
    I.reduce.metricCoeff = I.metricCoeff :=
  rfl

/-- Canonical rank-two tensor integrand built from the gauge-boson scalar integrand. -/
def gaugeBosonSelfEnergyTensorIntegrand (coeff : ℝ) : RankTwoTensorIntegrand where
  metricCoeff := coeff
  scalarIntegrand := gaugeBosonSelfEnergyIntegrand

/-- Canonical rank-two tensor integrand built from the ghost scalar integrand. -/
def ghostSelfEnergyTensorIntegrand (coeff : ℝ) : RankTwoTensorIntegrand where
  metricCoeff := coeff
  scalarIntegrand := ghostSelfEnergyIntegrand

/-- Canonical rank-two tensor integrand built from the fermion scalar integrand. -/
def fermionSelfEnergyTensorIntegrand (coeff : ℝ) : RankTwoTensorIntegrand where
  metricCoeff := coeff
  scalarIntegrand := fermionSelfEnergyIntegrand

/-- Reduction of the canonical gauge-boson tensor integrand lands on the gauge-boson master. -/
@[simp] lemma gaugeBosonSelfEnergyTensorIntegrand_reduce (coeff : ℝ) :
    (gaugeBosonSelfEnergyTensorIntegrand coeff).reduce =
      isotropicRankTwoReduction coeff gaugeBosonSelfEnergyMaster :=
  rfl

/-- Reduction of the canonical ghost tensor integrand lands on the ghost master. -/
@[simp] lemma ghostSelfEnergyTensorIntegrand_reduce (coeff : ℝ) :
    (ghostSelfEnergyTensorIntegrand coeff).reduce =
      isotropicRankTwoReduction coeff ghostSelfEnergyMaster :=
  rfl

/-- Reduction of the canonical fermion tensor integrand lands on the fermion master. -/
@[simp] lemma fermionSelfEnergyTensorIntegrand_reduce (coeff : ℝ) :
    (fermionSelfEnergyTensorIntegrand coeff).reduce =
      isotropicRankTwoReduction coeff fermionSelfEnergyMaster :=
  rfl

/-- Pole contribution of an isotropic reduction is the coefficient times the master pole. -/
@[simp] lemma poleContribution_isotropicRankTwoReduction (coeff : ℝ) (I : ScalarMasterIntegral) :
    (isotropicRankTwoReduction coeff I).poleContribution = coeff * I.poleCoeff :=
  rfl

/-- Time-time component of the reduced tensor picks out the positive metric sign. -/
lemma isotropicRankTwoReduction_time_time (coeff : ℝ) (I : ScalarMasterIntegral) :
    (isotropicRankTwoReduction coeff I).toTensor 0 0 = (coeff * I.poleCoeff : ℝ) := by
  simp [RankTwoReductionResult.toTensor, isotropicRankTwoReduction, minkowskiMetricEntry]

/-- Spatial diagonal components of the reduced tensor pick out the negative metric sign. -/
lemma isotropicRankTwoReduction_space_space
    (coeff : ℝ) (I : ScalarMasterIntegral) (i : Fin 3) :
    (isotropicRankTwoReduction coeff I).toTensor i.succ i.succ = (-(coeff * I.poleCoeff) : ℝ) := by
  simp [RankTwoReductionResult.toTensor, isotropicRankTwoReduction, minkowskiMetricEntry]

/-- Off-diagonal components vanish under isotropic tensor reduction. -/
lemma isotropicRankTwoReduction_offDiagonal
    (coeff : ℝ) (I : ScalarMasterIntegral)
    (μ ν : LorentzIndex) (h : μ ≠ ν) :
    (isotropicRankTwoReduction coeff I).toTensor μ ν = 0 := by
  simp [RankTwoReductionResult.toTensor, isotropicRankTwoReduction, minkowskiMetricEntry, h]

/-- Combine two reduced rank-two tensor integrals by adding their coefficients and masters. -/
def add (R S : RankTwoReductionResult) : RankTwoReductionResult where
  metricCoeff := R.metricCoeff + S.metricCoeff
  scalarMaster := OneLoopScalars.add R.scalarMaster S.scalarMaster

/-- Scalar multiplication of a reduced rank-two tensor integral. -/
def smul (a : ℝ) (R : RankTwoReductionResult) : RankTwoReductionResult where
  metricCoeff := a * R.metricCoeff
  scalarMaster := R.scalarMaster

/-- Pole bookkeeping for added rank-two reductions. -/
lemma poleContribution_add (R S : RankTwoReductionResult) :
    (add R S).poleContribution =
      (R.metricCoeff + S.metricCoeff) * (R.scalarMaster.poleCoeff + S.scalarMaster.poleCoeff) := by
  rfl

/-- Pole bookkeeping for scalar-multiplied rank-two reductions. -/
lemma poleContribution_smul (a : ℝ) (R : RankTwoReductionResult) :
    (smul a R).poleContribution = a * (R.metricCoeff * R.scalarMaster.poleCoeff) := by
  simp [smul, RankTwoReductionResult.poleContribution, mul_assoc]

end TensorReduction
end DimensionalRegularization
end PerturbationTheory
end QFT
end Physlib
