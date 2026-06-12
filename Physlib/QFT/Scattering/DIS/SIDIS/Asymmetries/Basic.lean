/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.SIDIS.Asymmetries.Harmonics
/-!

# SIDIS Spin-Azimuthal Asymmetry Interfaces

This module defines Sivers/Collins asymmetry records and projection contracts.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace SIDIS
namespace Asymmetries

/-- Spin-dependent SIDIS structure-function placeholders. -/
structure SpinStructureFunctions where
  FUU : ℝ → ℝ → ℝ → ℝ → ℝ
  FUT_sivers : ℝ → ℝ → ℝ → ℝ → ℝ
  FUT_collins : ℝ → ℝ → ℝ → ℝ → ℝ

/-- Sivers asymmetry ratio interface with default positive denominator regularization. -/
def siversAsymmetry
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ) : ℝ :=
  F.FUT_sivers x zHad Q2 pT / (|F.FUU x zHad Q2 pT| + 1)

/-- Angle-resolved observable whose Sivers coefficient is extracted by `sin(phi_h - phi_S)`. -/
def siversAngularObservable
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ) : ℝ → ℝ → ℝ :=
  fun phiH phiS => 2 * F.FUT_sivers x zHad Q2 pT * Harmonics.sinPhiDiff phiH phiS

/-- Collins asymmetry ratio interface with default positive denominator regularization. -/
def collinsAsymmetry
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ) : ℝ :=
  F.FUT_collins x zHad Q2 pT / (|F.FUU x zHad Q2 pT| + 1)

/-- Angle-resolved observable whose Collins coefficient is extracted by `sin(phi_h + phi_S)`. -/
def collinsAngularObservable
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ) : ℝ → ℝ → ℝ :=
  fun phiH phiS => 2 * F.FUT_collins x zHad Q2 pT * Harmonics.sinPhiSum phiH phiS

/-- Angle-independent unpolarized observable used in asymmetry denominators. -/
def unpolarizedAngularObservable
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ) : ℝ → ℝ → ℝ :=
  fun _phiH _phiS => F.FUU x zHad Q2 pT

/-- Pointwise nonnegativity of the regularized denominator used in asymmetries. -/
lemma asymmetry_den_nonneg
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ) :
    0 ≤ |F.FUU x zHad Q2 pT| + 1 := by
  have hAbs : 0 ≤ |F.FUU x zHad Q2 pT| := abs_nonneg _
  nlinarith

/-- Projection assumptions needed to identify projected Sivers moments with model entries. -/
structure SiversProjectionAssumptions
    (P : Harmonics.Projector)
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ) : Prop where
  den_proj : Harmonics.projectedMoment P Harmonics.oneWeight
      (fun _phiH _phiS => F.FUU x zHad Q2 pT) = F.FUU x zHad Q2 pT
  num_proj : Harmonics.projectedMoment P Harmonics.sinPhiDiff
      (fun _phiH _phiS => F.FUT_sivers x zHad Q2 pT) = F.FUT_sivers x zHad Q2 pT

/-- Derive the Sivers projection assumptions from explicit projected equalities. -/
lemma siversProjectionAssumptions_of_equalities
  (P : Harmonics.Projector)
  (F : SpinStructureFunctions)
  (x zHad Q2 pT : ℝ)
  (hDen : Harmonics.projectedMoment P Harmonics.oneWeight
    (fun _phiH _phiS => F.FUU x zHad Q2 pT) = F.FUU x zHad Q2 pT)
  (hNum : Harmonics.projectedMoment P Harmonics.sinPhiDiff
    (fun _phiH _phiS => F.FUT_sivers x zHad Q2 pT) = F.FUT_sivers x zHad Q2 pT) :
  SiversProjectionAssumptions P F x zHad Q2 pT := by
  exact ⟨hDen, hNum⟩

/--
Concrete Sivers projection theorem derived from harmonic normalization rather
than a raw projection-assumption bundle.
-/
lemma siversAsymmetry_eq_projectedRatio_of_harmonicDecomposition
    (P : Harmonics.Projector)
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ)
    (hLin : Harmonics.ProjectorAssumptions P)
    (hOrth : Harmonics.HarmonicOrthogonalityAssumptions P) :
    siversAsymmetry F x zHad Q2 pT
      = Harmonics.projectedMoment P Harmonics.sinPhiDiff
          (siversAngularObservable F x zHad Q2 pT)
          / (|Harmonics.projectedMoment P Harmonics.oneWeight
              (unpolarizedAngularObservable F x zHad Q2 pT)| + 1) := by
  have hScale := Harmonics.projectedMoment_smul_obs
      P hLin (2 * F.FUT_sivers x zHad Q2 pT) Harmonics.sinPhiDiff Harmonics.sinPhiDiff
  have hNum :
      Harmonics.projectedMoment P Harmonics.sinPhiDiff
        (siversAngularObservable F x zHad Q2 pT) = F.FUT_sivers x zHad Q2 pT := by
    calc
      Harmonics.projectedMoment P Harmonics.sinPhiDiff
          (siversAngularObservable F x zHad Q2 pT)
        = (2 * F.FUT_sivers x zHad Q2 pT) *
            Harmonics.projectedMoment P Harmonics.sinPhiDiff Harmonics.sinPhiDiff := by
              simpa [siversAngularObservable] using hScale
      _ = F.FUT_sivers x zHad Q2 pT := by
              rw [hOrth.sinPhiDiff_self]
              ring
  have hDen :
      Harmonics.projectedMoment P Harmonics.oneWeight
        (unpolarizedAngularObservable F x zHad Q2 pT) = F.FUU x zHad Q2 pT := by
    simpa [unpolarizedAngularObservable] using hOrth.oneWeight_const (F.FUU x zHad Q2 pT)
  simp [siversAsymmetry, hNum, hDen]

/-- Projection assumptions needed to identify projected Collins moments with model entries. -/
structure CollinsProjectionAssumptions
    (P : Harmonics.Projector)
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ) : Prop where
  den_proj : Harmonics.projectedMoment P Harmonics.oneWeight
      (fun _phiH _phiS => F.FUU x zHad Q2 pT) = F.FUU x zHad Q2 pT
  num_proj : Harmonics.projectedMoment P Harmonics.sinPhiSum
      (fun _phiH _phiS => F.FUT_collins x zHad Q2 pT) = F.FUT_collins x zHad Q2 pT

  /-- Derive the Collins projection assumptions from explicit projected equalities. -/
  lemma collinsProjectionAssumptions_of_equalities
    (P : Harmonics.Projector)
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ)
    (hDen : Harmonics.projectedMoment P Harmonics.oneWeight
      (fun _phiH _phiS => F.FUU x zHad Q2 pT) = F.FUU x zHad Q2 pT)
    (hNum : Harmonics.projectedMoment P Harmonics.sinPhiSum
      (fun _phiH _phiS => F.FUT_collins x zHad Q2 pT) = F.FUT_collins x zHad Q2 pT) :
    CollinsProjectionAssumptions P F x zHad Q2 pT := by
    exact ⟨hDen, hNum⟩

/--
Concrete Collins projection theorem derived from harmonic normalization rather
than a raw projection-assumption bundle.
-/
lemma collinsAsymmetry_eq_projectedRatio_of_harmonicDecomposition
    (P : Harmonics.Projector)
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ)
    (hLin : Harmonics.ProjectorAssumptions P)
    (hOrth : Harmonics.HarmonicOrthogonalityAssumptions P) :
    collinsAsymmetry F x zHad Q2 pT
      = Harmonics.projectedMoment P Harmonics.sinPhiSum
          (collinsAngularObservable F x zHad Q2 pT)
          / (|Harmonics.projectedMoment P Harmonics.oneWeight
              (unpolarizedAngularObservable F x zHad Q2 pT)| + 1) := by
  have hScale := Harmonics.projectedMoment_smul_obs
      P hLin (2 * F.FUT_collins x zHad Q2 pT) Harmonics.sinPhiSum Harmonics.sinPhiSum
  have hNum :
      Harmonics.projectedMoment P Harmonics.sinPhiSum
        (collinsAngularObservable F x zHad Q2 pT) = F.FUT_collins x zHad Q2 pT := by
    calc
      Harmonics.projectedMoment P Harmonics.sinPhiSum
          (collinsAngularObservable F x zHad Q2 pT)
        = (2 * F.FUT_collins x zHad Q2 pT) *
            Harmonics.projectedMoment P Harmonics.sinPhiSum Harmonics.sinPhiSum := by
              simpa [collinsAngularObservable] using hScale
      _ = F.FUT_collins x zHad Q2 pT := by
              rw [hOrth.sinPhiSum_self]
              ring
  have hDen :
      Harmonics.projectedMoment P Harmonics.oneWeight
        (unpolarizedAngularObservable F x zHad Q2 pT) = F.FUU x zHad Q2 pT := by
    simpa [unpolarizedAngularObservable] using hOrth.oneWeight_const (F.FUU x zHad Q2 pT)
  simp [collinsAsymmetry, hNum, hDen]

/-- Sivers projection theorem: asymmetry equals the corresponding projected-moment ratio. -/
lemma siversAsymmetry_eq_projectedRatio
    (P : Harmonics.Projector)
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ)
    (hProj : SiversProjectionAssumptions P F x zHad Q2 pT) :
    siversAsymmetry F x zHad Q2 pT
      = Harmonics.projectedMoment P Harmonics.sinPhiDiff
          (fun _phiH _phiS => F.FUT_sivers x zHad Q2 pT)
          / (|Harmonics.projectedMoment P Harmonics.oneWeight
              (fun _phiH _phiS => F.FUU x zHad Q2 pT)| + 1) := by
  simp [siversAsymmetry, hProj.num_proj, hProj.den_proj]

/-- Collins projection theorem: asymmetry equals the corresponding projected-moment ratio. -/
lemma collinsAsymmetry_eq_projectedRatio
    (P : Harmonics.Projector)
    (F : SpinStructureFunctions)
    (x zHad Q2 pT : ℝ)
    (hProj : CollinsProjectionAssumptions P F x zHad Q2 pT) :
    collinsAsymmetry F x zHad Q2 pT
      = Harmonics.projectedMoment P Harmonics.sinPhiSum
          (fun _phiH _phiS => F.FUT_collins x zHad Q2 pT)
          / (|Harmonics.projectedMoment P Harmonics.oneWeight
              (fun _phiH _phiS => F.FUU x zHad Q2 pT)| + 1) := by
  simp [collinsAsymmetry, hProj.num_proj, hProj.den_proj]

end Asymmetries
end SIDIS
end DIS
end Scattering
end QFT
end Physlib
