/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Exclusive.DVCS.Basic
public import Physlib.QFT.Scattering.DIS.SIDIS.Asymmetries.Harmonics
/-!

# DVCS/BH Interference Interfaces

This module defines BH/DVCS/interference decomposition templates and
projection-style asymmetry interfaces.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Exclusive
namespace DVCS

/-- Decomposition of exclusive observables into BH, DVCS, and interference pieces. -/
structure Decomposition where
  bh : ℝ → ℝ → ℝ → ℝ
  dvcs : ℝ → ℝ → ℝ → ℝ
  inter : ℝ → ℝ → ℝ → ℝ

/-- Total observable from decomposition pieces. -/
def totalObservable (D : Decomposition) (xi t Q2 : ℝ) : ℝ :=
  D.bh xi t Q2 + D.dvcs xi t Q2 + D.inter xi t Q2

lemma totalObservable_decompose (D : Decomposition) (xi t Q2 : ℝ) :
    totalObservable D xi t Q2 = D.bh xi t Q2 + D.dvcs xi t Q2 + D.inter xi t Q2 :=
  rfl

/-- Beam-spin asymmetry template with regularized denominator. -/
def beamSpinAsymmetry (D : Decomposition) (xi t Q2 : ℝ) : ℝ :=
  D.inter xi t Q2 / (|totalObservable D xi t Q2| + 1)

lemma beamSpinAsymmetry_den_nonneg (D : Decomposition) (xi t Q2 : ℝ) :
    0 ≤ |totalObservable D xi t Q2| + 1 := by
  have hAbs : 0 ≤ |totalObservable D xi t Q2| := abs_nonneg _
  nlinarith

/-- Harmonic-projected interference moment interface. -/
def projectedInterference
    (P : SIDIS.Asymmetries.Harmonics.Projector)
    (D : Decomposition)
    (xi t Q2 : ℝ) : ℝ :=
  SIDIS.Asymmetries.Harmonics.projectedMoment
    P
    SIDIS.Asymmetries.Harmonics.sinPhiDiff
    (fun _phiH _phiS => D.inter xi t Q2)

/-- Angle-resolved interference observable whose coefficient is extracted by `sin(phi_h - phi_S)`. -/
def interferenceAngularObservable
    (D : Decomposition)
    (xi t Q2 : ℝ) : ℝ → ℝ → ℝ :=
  fun phiH phiS => 2 * D.inter xi t Q2 * SIDIS.Asymmetries.Harmonics.sinPhiDiff phiH phiS

/-- Angle-independent total observable used in the beam-spin asymmetry denominator. -/
def totalAngularObservable
    (D : Decomposition)
    (xi t Q2 : ℝ) : ℝ → ℝ → ℝ :=
  fun _phiH _phiS => totalObservable D xi t Q2

/-- Projection assumptions used to identify projected interference with model entries. -/
structure InterferenceProjectionAssumptions
    (P : SIDIS.Asymmetries.Harmonics.Projector)
    (D : Decomposition)
    (xi t Q2 : ℝ) : Prop where
  den_proj : SIDIS.Asymmetries.Harmonics.projectedMoment
      P
      SIDIS.Asymmetries.Harmonics.oneWeight
      (fun _phiH _phiS => totalObservable D xi t Q2)
      = totalObservable D xi t Q2
  num_proj : projectedInterference P D xi t Q2 = D.inter xi t Q2

/-- Derive the DVCS interference projection assumptions from explicit projected equalities. -/
lemma interferenceProjectionAssumptions_of_equalities
    (P : SIDIS.Asymmetries.Harmonics.Projector)
    (D : Decomposition)
    (xi t Q2 : ℝ)
    (hDen : SIDIS.Asymmetries.Harmonics.projectedMoment
        P
        SIDIS.Asymmetries.Harmonics.oneWeight
        (fun _phiH _phiS => totalObservable D xi t Q2)
        = totalObservable D xi t Q2)
    (hNum : projectedInterference P D xi t Q2 = D.inter xi t Q2) :
    InterferenceProjectionAssumptions P D xi t Q2 := by
  exact ⟨hDen, hNum⟩

/--
Concrete beam-spin projection theorem derived from harmonic normalization rather
than a raw interference-projection assumption bundle.
-/
lemma beamSpinAsymmetry_eq_projectedRatio_of_harmonicDecomposition
    (P : SIDIS.Asymmetries.Harmonics.Projector)
    (D : Decomposition)
    (xi t Q2 : ℝ)
  (hLin : SIDIS.Asymmetries.Harmonics.ProjectorAssumptions P)
  (hOrth : SIDIS.Asymmetries.Harmonics.HarmonicOrthogonalityAssumptions P) :
    beamSpinAsymmetry D xi t Q2
      = SIDIS.Asymmetries.Harmonics.projectedMoment
          P
          SIDIS.Asymmetries.Harmonics.sinPhiDiff
          (interferenceAngularObservable D xi t Q2)
          / (|SIDIS.Asymmetries.Harmonics.projectedMoment
              P
              SIDIS.Asymmetries.Harmonics.oneWeight
              (totalAngularObservable D xi t Q2)| + 1) := by
  have hScale := SIDIS.Asymmetries.Harmonics.projectedMoment_smul_obs
      P hLin (2 * D.inter xi t Q2)
      SIDIS.Asymmetries.Harmonics.sinPhiDiff
      SIDIS.Asymmetries.Harmonics.sinPhiDiff
  have hNum :
      SIDIS.Asymmetries.Harmonics.projectedMoment
          P
          SIDIS.Asymmetries.Harmonics.sinPhiDiff
          (interferenceAngularObservable D xi t Q2)
        = D.inter xi t Q2 := by
    calc
      SIDIS.Asymmetries.Harmonics.projectedMoment
          P
          SIDIS.Asymmetries.Harmonics.sinPhiDiff
          (interferenceAngularObservable D xi t Q2)
        = (2 * D.inter xi t Q2) *
            SIDIS.Asymmetries.Harmonics.projectedMoment
              P SIDIS.Asymmetries.Harmonics.sinPhiDiff SIDIS.Asymmetries.Harmonics.sinPhiDiff := by
              simpa [interferenceAngularObservable] using hScale
      _ = D.inter xi t Q2 := by
              rw [hOrth.sinPhiDiff_self]
              ring
  have hDen :
      SIDIS.Asymmetries.Harmonics.projectedMoment
          P
          SIDIS.Asymmetries.Harmonics.oneWeight
          (totalAngularObservable D xi t Q2)
        = totalObservable D xi t Q2 := by
    simpa [totalAngularObservable] using hOrth.oneWeight_const (totalObservable D xi t Q2)
  simp [beamSpinAsymmetry, hNum, hDen]

/-- Projected-ratio theorem for beam-spin asymmetry interface. -/
lemma beamSpinAsymmetry_eq_projectedRatio
    (P : SIDIS.Asymmetries.Harmonics.Projector)
    (D : Decomposition)
    (xi t Q2 : ℝ)
    (hProj : InterferenceProjectionAssumptions P D xi t Q2) :
    beamSpinAsymmetry D xi t Q2
      = projectedInterference P D xi t Q2
          / (|SIDIS.Asymmetries.Harmonics.projectedMoment
              P
              SIDIS.Asymmetries.Harmonics.oneWeight
              (fun _phiH _phiS => totalObservable D xi t Q2)| + 1) := by
  simp [beamSpinAsymmetry, hProj.num_proj, hProj.den_proj]

end DVCS
end Exclusive
end DIS
end Scattering
end QFT
end Physlib
