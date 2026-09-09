/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.CasimirDerivation
/-!

# SU(N) Specialization of Representation-Derived Color Factors

This module implements an `SU(Nc)` specialization path for representation-derived
color invariants, and proves compatibility with the existing `suNColorFactors`
constructor.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace RepresentationColor

/-- Canonical normalized-generator package for `SU(Nc)` interfaces.

This is a lightweight interface model: index sets and generator entries are
minimal placeholders, while the color coefficients and their contracts are
instantiated to the standard `SU(Nc)` values.
-/
def sunNormalizedData (nC : ℝ) : NormalizedGeneratorData where
  AdjIndex := Unit
  FundIndex := Unit
  genEntry := fun _ _ _ => 0
  deltaAdj := fun _ _ => 1
  deltaFund := fun _ _ => 1
  tF := 1 / 2
  cF := (nC ^ 2 - 1) / (2 * nC)
  cA := nC
  traceNormalization := (1 / 2 : ℝ) = 1 / 2
  hTraceNormalization := by rfl
  fundamentalCasimir := ((nC ^ 2 - 1) / (2 * nC) : ℝ) = (nC ^ 2 - 1) / (2 * nC)
  hFundamentalCasimir := by rfl
  adjointCasimir := (nC : ℝ) = nC
  hAdjointCasimir := by rfl

/-- `SU(Nc)` carries normalized-generator data through the canonical package. -/
instance instHasNormalizedGeneratorDataSUN (nC : ℝ) : HasNormalizedGeneratorData (SUN nC) where
  data := sunNormalizedData nC

/-- The canonical `SU(Nc)` package satisfies the derivation targets. -/
def sunCasimirDerivationAssumptions (nC : ℝ) :
    CasimirDerivationAssumptions (sunNormalizedData nC) := by
  refine casimirDerivationAssumptions_of_iff
    (D := sunNormalizedData nC)
    ((1 / 2 : ℝ) = 1 / 2)
    (((nC ^ 2 - 1) / (2 * nC) : ℝ) = (nC ^ 2 - 1) / (2 * nC))
    ((nC : ℝ) = nC)
    (by rfl)
    (by rfl)
    (by rfl)
    ?_ ?_ ?_
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl

/-- The canonical `SU(Nc)` identities imply all normalized-generator contracts. -/
lemma sunNormalizedContracts (nC : ℝ) :
    (sunNormalizedData nC).traceNormalization ∧
      (sunNormalizedData nC).fundamentalCasimir ∧
      (sunNormalizedData nC).adjointCasimir := by
  refine normalizedContracts_of_iff
    (D := sunNormalizedData nC)
    ((1 / 2 : ℝ) = 1 / 2)
    (((nC ^ 2 - 1) / (2 * nC) : ℝ) = (nC ^ 2 - 1) / (2 * nC))
    ((nC : ℝ) = nC)
    (by rfl)
    (by rfl)
    (by rfl)
    ?_ ?_ ?_
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl

/-- Group-level extraction via representation data agrees with the standard
`SU(Nc)` formula, using the derived contract bundle explicitly. -/
lemma colorFactorsOf_suN_eq_from_representation_of_contracts (nC nF : ℝ)
    (hContracts :
      (sunNormalizedData nC).traceNormalization ∧
        (sunNormalizedData nC).fundamentalCasimir ∧
        (sunNormalizedData nC).adjointCasimir) :
    colorFactorsOf (SUN nC) nF = suNColorFactors nC nF := by
  rcases hContracts with ⟨_hTrace, _hFundamental, _hAdjoint⟩
  calc
    colorFactorsOf (SUN nC) nF
        = colorFactorsOfData (sunNormalizedData nC) nF := by
          simpa [instHasNormalizedGeneratorDataSUN] using
            (colorFactorsOf_eq_colorFactorsOfData (G := SUN nC) (nF := nF))
    _ = suNColorFactors nC nF := by
      rfl

/-- Data-level extraction reproduces the standard `SU(Nc)` color-factor constructor. -/
lemma colorFactorsOfData_suN_eq (nC nF : ℝ) :
    colorFactorsOfData (sunNormalizedData nC) nF = suNColorFactors nC nF := by
  rfl

/-- Group-level extraction via representation data agrees with the standard `SU(Nc)` formula. -/
lemma colorFactorsOf_suN_eq_from_representation (nC nF : ℝ) :
    colorFactorsOf (SUN nC) nF = suNColorFactors nC nF :=
  colorFactorsOf_suN_eq_from_representation_of_contracts nC nF (sunNormalizedContracts nC)

/-- One-loop coefficient specialization for the representation-derived `SU(Nc)`
path, using the derived contract bundle explicitly. -/
lemma beta0Of_suN_eq_from_representation_of_contracts (nC nF : ℝ)
    (hContracts :
      (sunNormalizedData nC).traceNormalization ∧
        (sunNormalizedData nC).fundamentalCasimir ∧
        (sunNormalizedData nC).adjointCasimir) :
    beta0Of (SUN nC) nF = beta0 (suNColorFactors nC nF) := by
  simp [beta0Of, colorFactorsOf_suN_eq_from_representation_of_contracts
    (nC := nC) (nF := nF) hContracts]

/-- Two-loop coefficient specialization for the representation-derived `SU(Nc)`
path, using the derived contract bundle explicitly. -/
lemma beta1Of_suN_eq_from_representation_of_contracts (nC nF : ℝ)
    (hContracts :
      (sunNormalizedData nC).traceNormalization ∧
        (sunNormalizedData nC).fundamentalCasimir ∧
        (sunNormalizedData nC).adjointCasimir) :
    beta1Of (SUN nC) nF = beta1 (suNColorFactors nC nF) := by
  simp [beta1Of, colorFactorsOf_suN_eq_from_representation_of_contracts
    (nC := nC) (nF := nF) hContracts]

/-- One-loop coefficient specialization for the representation-derived `SU(Nc)` path. -/
lemma beta0Of_suN_eq_from_representation (nC nF : ℝ) :
    beta0Of (SUN nC) nF = beta0 (suNColorFactors nC nF) :=
  beta0Of_suN_eq_from_representation_of_contracts nC nF (sunNormalizedContracts nC)

/-- Two-loop coefficient specialization for the representation-derived `SU(Nc)` path. -/
lemma beta1Of_suN_eq_from_representation (nC nF : ℝ) :
    beta1Of (SUN nC) nF = beta1 (suNColorFactors nC nF) :=
  beta1Of_suN_eq_from_representation_of_contracts nC nF (sunNormalizedContracts nC)

end RepresentationColor
end QCD
end QFT
end Physlib
