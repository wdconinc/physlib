/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.PVES.Electroweak.NeutralCurrent
/-!

# PVES Interference Decomposition Interfaces

This module introduces helicity-resolved parity-even/parity-odd decomposition
interfaces for PVES and bridges that isolate helicity-odd dependence to the
`gamma-Z` interference contribution.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace PVES
namespace Interference

open Electroweak

/-- Helicity sign convention for right/left polarized beam labels. -/
def helicitySign (h : Bool) : ℝ :=
  if h then 1 else -1

lemma helicitySign_sq (h : Bool) : helicitySign h ^ 2 = 1 := by
  by_cases hh : h
  · simp [helicitySign, hh]
  · simp [helicitySign, hh]

/-- Helicity-resolved matrix-element decomposition with EM, weak, and
`gamma-Z` interference pieces. -/
structure HelicitySquaredDecomposition where
  /-- Pure electromagnetic contribution. -/
  em : ℝ → ℝ → ℝ
  /-- Pure weak neutral-current contribution. -/
  weak : ℝ → ℝ → ℝ
  /-- `gamma-Z` interference contribution. -/
  interference : ℝ → ℝ → ℝ

/-- Helicity-resolved total from decomposition pieces. -/
def helicityResolvedTotal
    (D : HelicitySquaredDecomposition)
    (h : Bool)
    (x y : ℝ) : ℝ :=
  D.em x y + D.weak x y + helicitySign h * D.interference x y

/-- Parity-even part extracted from opposite beam helicities. -/
def parityEvenPart
    (sigmaPlus sigmaMinus : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  (sigmaPlus x y + sigmaMinus x y) / 2

/-- Parity-odd part extracted from opposite beam helicities. -/
def parityOddPart
    (sigmaPlus sigmaMinus : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  (sigmaPlus x y - sigmaMinus x y) / 2

/-- Bridge assumptions isolating helicity dependence in the interference term. -/
structure HelicityInterferenceIsolationAssumptions
    (D : NeutralCurrentDecomposition)
    (sigmaPlus sigmaMinus : ℝ → ℝ → ℝ) : Prop where
  /-- Positive-helicity observable decomposition. -/
  plus_eq : ∀ x y,
    sigmaPlus x y = D.photon x y + D.zBoson x y + D.gammaZInterference x y
  /-- Negative-helicity observable decomposition. -/
  minus_eq : ∀ x y,
    sigmaMinus x y = D.photon x y + D.zBoson x y - D.gammaZInterference x y

lemma parityEven_eq_photon_plus_z_of_isolation
    (D : NeutralCurrentDecomposition)
    (sigmaPlus sigmaMinus : ℝ → ℝ → ℝ)
    (hIso : HelicityInterferenceIsolationAssumptions D sigmaPlus sigmaMinus)
    (x y : ℝ) :
    parityEvenPart sigmaPlus sigmaMinus x y = D.photon x y + D.zBoson x y := by
  have hPlus := hIso.plus_eq x y
  have hMinus := hIso.minus_eq x y
  unfold parityEvenPart
  linarith

lemma parityOdd_eq_gammaZInterference_of_isolation
    (D : NeutralCurrentDecomposition)
    (sigmaPlus sigmaMinus : ℝ → ℝ → ℝ)
    (hIso : HelicityInterferenceIsolationAssumptions D sigmaPlus sigmaMinus)
    (x y : ℝ) :
    parityOddPart sigmaPlus sigmaMinus x y = D.gammaZInterference x y := by
  have hPlus := hIso.plus_eq x y
  have hMinus := hIso.minus_eq x y
  unfold parityOddPart
  linarith

/-- Canonical helicity-resolved realization from a neutral-current decomposition. -/
def canonicalHelicityModel
    (D : NeutralCurrentDecomposition) : HelicitySquaredDecomposition where
  em := D.photon
  weak := D.zBoson
  interference := D.gammaZInterference

lemma canonicalPlus_eq_total
    (D : NeutralCurrentDecomposition)
    (x y : ℝ) :
    helicityResolvedTotal (canonicalHelicityModel D) true x y
      = D.photon x y + D.zBoson x y + D.gammaZInterference x y := by
  simp [helicityResolvedTotal, canonicalHelicityModel, helicitySign]

lemma canonicalMinus_eq_total
    (D : NeutralCurrentDecomposition)
    (x y : ℝ) :
    helicityResolvedTotal (canonicalHelicityModel D) false x y
      = D.photon x y + D.zBoson x y - D.gammaZInterference x y := by
  simp [helicityResolvedTotal, canonicalHelicityModel, helicitySign, sub_eq_add_neg]

lemma canonicalIsolationAssumptions
    (D : NeutralCurrentDecomposition) :
    HelicityInterferenceIsolationAssumptions
      D
      (helicityResolvedTotal (canonicalHelicityModel D) true)
      (helicityResolvedTotal (canonicalHelicityModel D) false) := by
  refine ⟨?_, ?_⟩
  · intro x y
    simpa using canonicalPlus_eq_total D x y
  · intro x y
    simpa using canonicalMinus_eq_total D x y

lemma canonicalParityOdd_eq_gammaZInterference
    (D : NeutralCurrentDecomposition)
    (x y : ℝ) :
    parityOddPart
      (helicityResolvedTotal (canonicalHelicityModel D) true)
      (helicityResolvedTotal (canonicalHelicityModel D) false)
      x y = D.gammaZInterference x y := by
  exact parityOdd_eq_gammaZInterference_of_isolation
    D
    (helicityResolvedTotal (canonicalHelicityModel D) true)
    (helicityResolvedTotal (canonicalHelicityModel D) false)
    (canonicalIsolationAssumptions D)
    x y

end Interference
end PVES
end DIS
end Scattering
end QFT
end Physlib
