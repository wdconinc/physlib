/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.RepresentationColor
/-!

# Casimir Derivation Targets

This module introduces theorem targets for deriving color invariants from
representation-level operator identities.

The design remains interface-first: we encode the identity layer as explicit
contracts and provide bridge lemmas to the normalized-generator package.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace RepresentationColor

/-- Representation-level identity targets used to justify Casimir coefficients. -/
structure CasimirDerivationAssumptions (D : NormalizedGeneratorData) : Type where
  /-- Target statement for trace normalization, e.g. `Tr(T^a T^b) = T_F \delta^{ab}`. -/
  traceIdentity : Prop
  /-- Target statement for the fundamental Casimir operator, e.g. `\sum_a T^a T^a = C_F I`. -/
  fundamentalIdentity : Prop
  /-- Target statement for the adjoint Casimir operator, e.g. `f^{acd} f^{bcd} = C_A \delta^{ab}`. -/
  adjointIdentity : Prop
  /-- Proof of the trace identity target. -/
  hTraceIdentity : traceIdentity
  /-- Proof of the fundamental Casimir target. -/
  hFundamentalIdentity : fundamentalIdentity
  /-- Proof of the adjoint Casimir target. -/
  hAdjointIdentity : adjointIdentity
  /-- Bridge from the target trace identity into the normalized-generator contract. -/
  traceImpliesContract : traceIdentity → D.traceNormalization
  /-- Bridge from the target fundamental identity into the normalized-generator contract. -/
  fundamentalImpliesContract : fundamentalIdentity → D.fundamentalCasimir
  /-- Bridge from the target adjoint identity into the normalized-generator contract. -/
  adjointImpliesContract : adjointIdentity → D.adjointCasimir

/-- Build a full derivation package from identity witnesses and equivalence bridges.

This is the first nontrivial transport theorem in step 3: once concrete
representation-level identities are proven and shown equivalent to the
normalized-generator contracts, the complete `CasimirDerivationAssumptions`
record is synthesized automatically.
-/
def casimirDerivationAssumptions_of_iff
    (D : NormalizedGeneratorData)
    (traceIdentity fundamentalIdentity adjointIdentity : Prop)
    (hTrace : traceIdentity)
    (hFundamental : fundamentalIdentity)
    (hAdjoint : adjointIdentity)
    (hTraceIff : traceIdentity ↔ D.traceNormalization)
    (hFundamentalIff : fundamentalIdentity ↔ D.fundamentalCasimir)
    (hAdjointIff : adjointIdentity ↔ D.adjointCasimir) :
    CasimirDerivationAssumptions D := by
  refine {
    traceIdentity := traceIdentity
    fundamentalIdentity := fundamentalIdentity
    adjointIdentity := adjointIdentity
    hTraceIdentity := hTrace
    hFundamentalIdentity := hFundamental
    hAdjointIdentity := hAdjoint
    traceImpliesContract := ?_
    fundamentalImpliesContract := ?_
    adjointImpliesContract := ?_
  }
  · intro h
    exact hTraceIff.mp h
  · intro h
    exact hFundamentalIff.mp h
  · intro h
    exact hAdjointIff.mp h

/-- Directly derive all normalized-generator contracts from iff-bridged
representation identities.

This convenience theorem packages
`casimirDerivationAssumptions_of_iff` and `normalizedContracts_of_derivation`
into a single reusable result for downstream modules.
-/
lemma normalizedContracts_of_iff
    (D : NormalizedGeneratorData)
    (traceIdentity fundamentalIdentity adjointIdentity : Prop)
    (hTrace : traceIdentity)
    (hFundamental : fundamentalIdentity)
    (hAdjoint : adjointIdentity)
    (hTraceIff : traceIdentity ↔ D.traceNormalization)
    (hFundamentalIff : fundamentalIdentity ↔ D.fundamentalCasimir)
    (hAdjointIff : adjointIdentity ↔ D.adjointCasimir) :
    D.traceNormalization ∧ D.fundamentalCasimir ∧ D.adjointCasimir := by
  exact ⟨hTraceIff.mp hTrace, hFundamentalIff.mp hFundamental, hAdjointIff.mp hAdjoint⟩

/-- Any derivation contract package implies the normalized-generator contracts. -/
lemma normalizedContracts_of_derivation
    (D : NormalizedGeneratorData)
    (hDeriv : CasimirDerivationAssumptions D) :
    D.traceNormalization ∧ D.fundamentalCasimir ∧ D.adjointCasimir := by
  refine ⟨hDeriv.traceImpliesContract hDeriv.hTraceIdentity, ?_, ?_⟩
  · exact hDeriv.fundamentalImpliesContract hDeriv.hFundamentalIdentity
  · exact hDeriv.adjointImpliesContract hDeriv.hAdjointIdentity

/-- Color-factor extraction from derived identities agrees with direct data extraction. -/
lemma colorFactorsOfData_eq_colorFactors_from_derivation
    (D : NormalizedGeneratorData)
    (nF : ℝ)
    (_hDeriv : CasimirDerivationAssumptions D) :
    colorFactorsOfData D nF = (colorInvariantsOf D).toColorFactors nF := by
  rfl

/-- Group-level extraction path from derived identities through stored representation data. -/
lemma colorFactorsOf_eq_colorFactors_from_derivation
    (G : Type) [HasNormalizedGeneratorData G]
    (nF : ℝ)
    (_hDeriv : CasimirDerivationAssumptions (HasNormalizedGeneratorData.data (G := G))) :
    colorFactorsOf G nF =
      (colorInvariantsOf (HasNormalizedGeneratorData.data (G := G))).toColorFactors nF := by
  rfl

/-- One-loop coefficient extracted from a derivation package agrees with class-level extraction. -/
lemma beta0Of_eq_beta0_from_derivation
    (G : Type) [HasNormalizedGeneratorData G]
    (nF : ℝ)
  (_hDeriv : CasimirDerivationAssumptions (HasNormalizedGeneratorData.data (G := G))) :
    beta0Of G nF =
      beta0 ((colorInvariantsOf (HasNormalizedGeneratorData.data (G := G))).toColorFactors nF) := by
  simpa using beta0Of_eq_beta0OfData G nF

/-- Two-loop coefficient extracted from a derivation package agrees with class-level extraction. -/
lemma beta1Of_eq_beta1_from_derivation
    (G : Type) [HasNormalizedGeneratorData G]
    (nF : ℝ)
  (_hDeriv : CasimirDerivationAssumptions (HasNormalizedGeneratorData.data (G := G))) :
    beta1Of G nF =
      beta1 ((colorInvariantsOf (HasNormalizedGeneratorData.data (G := G))).toColorFactors nF) := by
  simpa using beta1Of_eq_beta1OfData G nF

end RepresentationColor
end QCD
end QFT
end Physlib
