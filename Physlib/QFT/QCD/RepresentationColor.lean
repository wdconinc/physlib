/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.Basic
/-!

# Representation-Theoretic Color Derivation Interfaces

This module provides scaffolding for deriving QCD color invariants from
representation-theoretic inputs instead of hardcoding coefficients.

It implements:

- Step 1: a dedicated representation-level color-derivation module;
- Step 2: a proof-carrying normalized-generator package.

The package is intentionally interface-first: heavy Lie/representation proofs are
factored as explicit contracts that later modules can discharge.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace RepresentationColor

/-- Proof-carrying normalized generator package.

This structure records representation-theoretic input data and the associated
proof obligations needed to extract color invariants.

`AdjIndex` indexes adjoint generators, and `FundIndex` indexes the fundamental
representation basis. Matrix entries are encoded as real-valued maps for
interface purposes.
-/
structure NormalizedGeneratorData : Type 2 where
  /-- Index type for adjoint generators. -/
  AdjIndex : Type
  /-- Index type for basis vectors in the fundamental representation. -/
  FundIndex : Type
  /-- Generator matrix entries `(T^a)_i_j`. -/
  genEntry : AdjIndex → FundIndex → FundIndex → ℝ
  /-- Adjoint Kronecker delta placeholder. -/
  deltaAdj : AdjIndex → AdjIndex → ℝ
  /-- Fundamental Kronecker delta placeholder. -/
  deltaFund : FundIndex → FundIndex → ℝ
  /-- Trace normalization coefficient `T_F`. -/
  tF : ℝ
  /-- Fundamental Casimir coefficient `C_F`. -/
  cF : ℝ
  /-- Adjoint Casimir coefficient `C_A`. -/
  cA : ℝ
  /-- Trace normalization contract (e.g. `Tr(T^a T^b) = T_F δ^{ab}`). -/
  traceNormalization : Prop
  /-- Witness for trace normalization. -/
  hTraceNormalization : traceNormalization
  /-- Fundamental Casimir contract (e.g. `Σ_a T^a T^a = C_F I`). -/
  fundamentalCasimir : Prop
  /-- Witness for fundamental Casimir contract. -/
  hFundamentalCasimir : fundamentalCasimir
  /-- Adjoint Casimir contract (e.g. `f^{acd} f^{bcd} = C_A δ^{ab}`). -/
  adjointCasimir : Prop
  /-- Witness for adjoint Casimir contract. -/
  hAdjointCasimir : adjointCasimir

/-- Extract color invariants from normalized-generator representation data. -/
def colorInvariantsOf (D : NormalizedGeneratorData) : ColorInvariants where
  cF := D.cF
  cA := D.cA
  tF := D.tF

/-- Extract flavor-aware color factors from representation data. -/
def colorFactorsOfData (D : NormalizedGeneratorData) (nF : ℝ) : ColorFactors :=
  (colorInvariantsOf D).toColorFactors nF

/-- Typeclass for gauge groups equipped with proof-carrying normalized generators. -/
class HasNormalizedGeneratorData (G : Type) : Type 3 where
  data : NormalizedGeneratorData

/-- Color invariants induced from representation-theoretic generator data. -/
def invariantsFromRepresentation (G : Type) [HasNormalizedGeneratorData G] : ColorInvariants :=
  colorInvariantsOf (HasNormalizedGeneratorData.data (G := G))

/-- Derived `HasColorInvariants` instance from proof-carrying generator data. -/
instance instHasColorInvariantsFromRepresentation (G : Type) [HasNormalizedGeneratorData G] :
    HasColorInvariants G where
  invariants := invariantsFromRepresentation G

/-- Coherence: color factors from class-level invariants and directly from stored
representation data coincide. -/
lemma colorFactorsOf_eq_colorFactorsOfData
    (G : Type) [HasNormalizedGeneratorData G] (nF : ℝ) :
    colorFactorsOf G nF = colorFactorsOfData (HasNormalizedGeneratorData.data (G := G)) nF := by
  rfl

/-- Coherence for one-loop beta coefficient through representation extraction. -/
lemma beta0Of_eq_beta0OfData
    (G : Type) [HasNormalizedGeneratorData G] (nF : ℝ) :
    beta0Of G nF = beta0 (colorFactorsOfData (HasNormalizedGeneratorData.data (G := G)) nF) := by
  rfl

/-- Coherence for two-loop beta coefficient through representation extraction. -/
lemma beta1Of_eq_beta1OfData
    (G : Type) [HasNormalizedGeneratorData G] (nF : ℝ) :
    beta1Of G nF = beta1 (colorFactorsOfData (HasNormalizedGeneratorData.data (G := G)) nF) := by
  rfl

/-- Access to proof witnesses in the normalized-generator package. -/
lemma traceNormalization_holds
    (G : Type) [HasNormalizedGeneratorData G] :
    (HasNormalizedGeneratorData.data (G := G)).traceNormalization :=
  (HasNormalizedGeneratorData.data (G := G)).hTraceNormalization

/-- Access to the fundamental Casimir witness in the normalized-generator package. -/
lemma fundamentalCasimir_holds
    (G : Type) [HasNormalizedGeneratorData G] :
    (HasNormalizedGeneratorData.data (G := G)).fundamentalCasimir :=
  (HasNormalizedGeneratorData.data (G := G)).hFundamentalCasimir

/-- Access to the adjoint Casimir witness in the normalized-generator package. -/
lemma adjointCasimir_holds
    (G : Type) [HasNormalizedGeneratorData G] :
    (HasNormalizedGeneratorData.data (G := G)).adjointCasimir :=
  (HasNormalizedGeneratorData.data (G := G)).hAdjointCasimir

end RepresentationColor
end QCD
end QFT
end Physlib
