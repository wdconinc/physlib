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

/-- Representation-level identity targets used to justify Casimir coefficients.

The three identities are the actual equations
`Tr(T^a T^b) = T_F δ^{ab}`, `Σ_a T^a T^a = C_F I` and `f^{acd} f^{bcd} = C_A δ^{ab}`
in the generator entries and structure constants stored by `D`; see
`NormalizedGeneratorData.TraceIdentity` and friends.  Supplying this record is therefore
a genuine obligation on `D`, not a choice of proposition. -/
structure CasimirDerivationAssumptions (D : NormalizedGeneratorData) : Type where
  /-- Proof of the trace-normalization identity `Tr(T^a T^b) = T_F δ^{ab}` for `D`. -/
  hTraceIdentity : D.TraceIdentity
  /-- Proof of the fundamental Casimir identity `Σ_a T^a T^a = C_F I` for `D`. -/
  hFundamentalIdentity : D.FundamentalCasimirIdentity
  /-- Proof of the adjoint Casimir identity `f^{acd} f^{bcd} = C_A δ^{ab}` for `D`. -/
  hAdjointIdentity : D.AdjointCasimirIdentity
  /-- Bridge from the trace identity into the normalized-generator contract. -/
  traceImpliesContract : D.TraceIdentity → D.traceNormalization
  /-- Bridge from the fundamental Casimir identity into the normalized-generator contract. -/
  fundamentalImpliesContract : D.FundamentalCasimirIdentity → D.fundamentalCasimir
  /-- Bridge from the adjoint Casimir identity into the normalized-generator contract. -/
  adjointImpliesContract : D.AdjointCasimirIdentity → D.adjointCasimir

/-- Build a full derivation package from identity witnesses and equivalence bridges.

This is the first nontrivial transport theorem in step 3: once concrete
representation-level identities are proven and shown equivalent to the
normalized-generator contracts, the complete `CasimirDerivationAssumptions`
record is synthesized automatically.
-/
def casimirDerivationAssumptions_of_iff
    (D : NormalizedGeneratorData)
    (hTrace : D.TraceIdentity)
    (hFundamental : D.FundamentalCasimirIdentity)
    (hAdjoint : D.AdjointCasimirIdentity)
    (hTraceIff : D.TraceIdentity ↔ D.traceNormalization)
    (hFundamentalIff : D.FundamentalCasimirIdentity ↔ D.fundamentalCasimir)
    (hAdjointIff : D.AdjointCasimirIdentity ↔ D.adjointCasimir) :
    CasimirDerivationAssumptions D := by
  refine {
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
  exact beta0Of_eq_beta0OfData G nF

/-- Two-loop coefficient extracted from a derivation package agrees with class-level extraction. -/
lemma beta1Of_eq_beta1_from_derivation
    (G : Type) [HasNormalizedGeneratorData G]
    (nF : ℝ)
  (_hDeriv : CasimirDerivationAssumptions (HasNormalizedGeneratorData.data (G := G))) :
    beta1Of G nF =
      beta1 ((colorInvariantsOf (HasNormalizedGeneratorData.data (G := G))).toColorFactors nF) := by
  exact beta1Of_eq_beta1OfData G nF

/-! ### A model that actually satisfies the identities: the U(1) sector -/

/-- Normalized-generator data for a U(1) gauge sector of charge `Y`.

There is a single generator `T = Y` acting on a one-dimensional charge representation,
and no structure constants.  Both index sets are singletons, so the Kronecker deltas are
identically `1`.  Unlike `sunNormalizedData`, the generator entries here are the genuine
ones (the real charge `Y`, coerced into the complex `genEntry` field), and the three
representation-level identities below are theorems about them. -/
def u1NormalizedData (Y : ℝ) : NormalizedGeneratorData where
  AdjIndex := Fin 1
  FundIndex := Fin 1
  adjFintype := inferInstance
  fundFintype := inferInstance
  genEntry := fun _ _ _ => (Y : ℂ)
  structConst := fun _ _ _ => 0
  deltaAdj := fun _ _ => 1
  deltaFund := fun _ _ => 1
  tF := Y ^ 2
  cF := Y ^ 2
  cA := 0
  traceNormalization := (Y * Y : ℝ) = Y ^ 2 * 1
  hTraceNormalization := by ring
  fundamentalCasimir := (Y * Y : ℝ) = Y ^ 2 * 1
  hFundamentalCasimir := by ring
  adjointCasimir := ((0 : ℝ) * 0 : ℝ) = 0 * 1
  hAdjointCasimir := by ring

/-- The U(1) generator satisfies `Tr(T^a T^b) = T_F δ^{ab}` with `T_F = Y²`. -/
lemma u1NormalizedData_traceIdentity (Y : ℝ) :
    (u1NormalizedData Y).TraceIdentity := by
  intro a b
  show (∑ _i : Fin 1, ∑ _j : Fin 1, (Y : ℂ) * (Y : ℂ)) = ((Y ^ 2 : ℝ) : ℂ) * ((1 : ℝ) : ℂ)
  simp only [Fin.sum_univ_one]
  push_cast
  ring

/-- The U(1) generator satisfies `Σ_a T^a T^a = C_F I` with `C_F = Y²`. -/
lemma u1NormalizedData_fundamentalIdentity (Y : ℝ) :
    (u1NormalizedData Y).FundamentalCasimirIdentity := by
  intro i j
  show (∑ _a : Fin 1, ∑ _k : Fin 1, (Y : ℂ) * (Y : ℂ)) = ((Y ^ 2 : ℝ) : ℂ) * ((1 : ℝ) : ℂ)
  simp only [Fin.sum_univ_one]
  push_cast
  ring

/-- U(1) is abelian: its structure constants vanish, so `f^{acd} f^{bcd} = C_A δ^{ab}`
holds with `C_A = 0`. -/
lemma u1NormalizedData_adjointIdentity (Y : ℝ) :
    (u1NormalizedData Y).AdjointCasimirIdentity := by
  intro a b
  show (∑ _c : Fin 1, ∑ _d : Fin 1, (0 : ℝ) * 0) = 0 * 1
  simp only [Fin.sum_univ_one]
  ring

/-- The U(1) sector carries a full derivation package: all three representation-level
identities are proved, not assumed. -/
def u1CasimirDerivationAssumptions (Y : ℝ) :
    CasimirDerivationAssumptions (u1NormalizedData Y) where
  hTraceIdentity := u1NormalizedData_traceIdentity Y
  hFundamentalIdentity := u1NormalizedData_fundamentalIdentity Y
  hAdjointIdentity := u1NormalizedData_adjointIdentity Y
  traceImpliesContract := fun _ => (u1NormalizedData Y).hTraceNormalization
  fundamentalImpliesContract := fun _ => (u1NormalizedData Y).hFundamentalCasimir
  adjointImpliesContract := fun _ => (u1NormalizedData Y).hAdjointCasimir

/-- The U(1) color invariants extracted from the derived package: `C_F = T_F = Y²`
and `C_A = 0`. -/
lemma u1NormalizedData_colorInvariants (Y : ℝ) :
    colorInvariantsOf (u1NormalizedData Y) = { cF := Y ^ 2, cA := 0, tF := Y ^ 2 } := by
  rfl

end RepresentationColor
end QCD
end QFT
end Physlib
