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
  /-- The adjoint index set is finite, so that sums over generators are defined. -/
  adjFintype : Fintype AdjIndex
  /-- The fundamental index set is finite, so that matrix traces are defined. -/
  fundFintype : Fintype FundIndex
  /-- Generator matrix entries `(T^a)_i_j`. -/
  genEntry : AdjIndex → FundIndex → FundIndex → ℝ
  /-- Structure constants `f^{abc}` of the gauge algebra. -/
  structConst : AdjIndex → AdjIndex → AdjIndex → ℝ
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
  /-- Trace normalization contract.  This is a `Prop`-valued *parameter*, not the
  identity `Tr(T^a T^b) = T_F δ^{ab}` itself; see `NormalizedGeneratorData.TraceIdentity`
  for the statement it stands for. -/
  traceNormalization : Prop
  /-- Witness for trace normalization. -/
  hTraceNormalization : traceNormalization
  /-- Fundamental Casimir contract.  A `Prop`-valued parameter; the intended statement is
  `NormalizedGeneratorData.FundamentalCasimirIdentity`. -/
  fundamentalCasimir : Prop
  /-- Witness for fundamental Casimir contract. -/
  hFundamentalCasimir : fundamentalCasimir
  /-- Adjoint Casimir contract.  A `Prop`-valued parameter; the intended statement is
  `NormalizedGeneratorData.AdjointCasimirIdentity`. -/
  adjointCasimir : Prop
  /-- Witness for adjoint Casimir contract. -/
  hAdjointCasimir : adjointCasimir

/-! ### Representation-level identities

The three `Prop` fields above (`traceNormalization`, `fundamentalCasimir`,
`adjointCasimir`) are *parameters ranging over propositions*: instantiating them with
`True` satisfies the package, so on their own they assert nothing.  The definitions in
this section write down what those names are meant to say, as equations in the data the
package already carries.  They are consumed by `CasimirDerivationAssumptions`. -/

/-- The trace-normalization identity `Tr(T^a T^b) = T_F δ^{ab}`, written out in the
stored generator entries. -/
def NormalizedGeneratorData.TraceIdentity (D : NormalizedGeneratorData) : Prop :=
  letI := D.fundFintype
  ∀ a b : D.AdjIndex,
    (∑ i : D.FundIndex, ∑ j : D.FundIndex, D.genEntry a i j * D.genEntry b j i)
      = D.tF * D.deltaAdj a b

/-- The fundamental Casimir identity `Σ_a T^a T^a = C_F I`, written out in the stored
generator entries. -/
def NormalizedGeneratorData.FundamentalCasimirIdentity (D : NormalizedGeneratorData) :
    Prop :=
  letI := D.adjFintype
  letI := D.fundFintype
  ∀ i j : D.FundIndex,
    (∑ a : D.AdjIndex, ∑ k : D.FundIndex, D.genEntry a i k * D.genEntry a k j)
      = D.cF * D.deltaFund i j

/-- The adjoint Casimir identity `f^{acd} f^{bcd} = C_A δ^{ab}`, written out in the
stored structure constants. -/
def NormalizedGeneratorData.AdjointCasimirIdentity (D : NormalizedGeneratorData) : Prop :=
  letI := D.adjFintype
  ∀ a b : D.AdjIndex,
    (∑ c : D.AdjIndex, ∑ d : D.AdjIndex, D.structConst a c d * D.structConst b c d)
      = D.cA * D.deltaAdj a b

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
