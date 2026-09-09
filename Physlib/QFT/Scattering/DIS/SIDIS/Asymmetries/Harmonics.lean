/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# SIDIS Harmonic Interfaces

This module defines azimuthal harmonic weights and projection contracts used
for spin-dependent SIDIS asymmetries.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace SIDIS
namespace Asymmetries
namespace Harmonics

/-- The Sivers-sensitive harmonic `sin(phi_h - phi_S)`. -/
def sinPhiDiff (phiH phiS : ℝ) : ℝ :=
  Real.sin (phiH - phiS)

/-- The Collins-sensitive harmonic `sin(phi_h + phi_S)`. -/
def sinPhiSum (phiH phiS : ℝ) : ℝ :=
  Real.sin (phiH + phiS)

/-- Unit harmonic weight. -/
def oneWeight (_phiH _phiS : ℝ) : ℝ :=
  1

/-- Abstract harmonic projector acting on angle-dependent observables. -/
abbrev Projector := (ℝ → ℝ → ℝ) → ℝ

/-- Weighted projection of an observable by a chosen harmonic. -/
def projectedMoment
    (P : Projector)
    (w obs : ℝ → ℝ → ℝ) : ℝ :=
  P (fun phiH phiS => w phiH phiS * obs phiH phiS)

/-- Minimal linearity contract for a harmonic projector. -/
structure ProjectorAssumptions (P : Projector) : Prop where
  map_add : ∀ f g, P (fun phiH phiS => f phiH phiS + g phiH phiS)
    = P f + P g
  map_smul : ∀ (a : ℝ) f, P (fun phiH phiS => a * f phiH phiS)
    = a * P f

/-- Projection is additive in the observable argument under linearity assumptions. -/
lemma projectedMoment_add_obs
    (P : Projector)
    (hP : ProjectorAssumptions P)
    (w obs1 obs2 : ℝ → ℝ → ℝ) :
    projectedMoment P w (fun phiH phiS => obs1 phiH phiS + obs2 phiH phiS)
      = projectedMoment P w obs1 + projectedMoment P w obs2 := by
  simpa [projectedMoment, mul_add] using
    hP.map_add
      (fun phiH phiS => w phiH phiS * obs1 phiH phiS)
      (fun phiH phiS => w phiH phiS * obs2 phiH phiS)

/-- Projection commutes with global scalar rescaling of the observable. -/
lemma projectedMoment_smul_obs
    (P : Projector)
    (hP : ProjectorAssumptions P)
    (a : ℝ)
    (w obs : ℝ → ℝ → ℝ) :
    projectedMoment P w (fun phiH phiS => a * obs phiH phiS)
      = a * projectedMoment P w obs := by
  simpa [projectedMoment, mul_assoc, mul_left_comm, mul_comm] using
    hP.map_smul a (fun phiH phiS => w phiH phiS * obs phiH phiS)

/-- Concrete azimuthal projector given by a normalized quadrature over representative angles. -/
def normalizedAngularProjector : Projector :=
  fun f =>
    (f 0 0 + f Real.pi 0 + f 0 Real.pi + f Real.pi Real.pi) / 4

/-- The normalized angular projector satisfies the abstract linearity contract. -/
lemma normalizedAngularProjector_isLinear : ProjectorAssumptions normalizedAngularProjector := by
  constructor
  · intro f g
    unfold normalizedAngularProjector
    ring
  · intro a f
    unfold normalizedAngularProjector
    ring

/-- The normalized angular projector returns constants unchanged. -/
lemma normalizedAngularProjector_const (c : ℝ) :
    normalizedAngularProjector (fun _phiH _phiS => c) = c := by
  simp [normalizedAngularProjector]
  ring

/-- Projecting a constant observable with unit weight recovers that constant. -/
lemma projectedMoment_oneWeight_const
    (c : ℝ) :
    projectedMoment normalizedAngularProjector oneWeight (fun _phiH _phiS => c) = c := by
  simpa [projectedMoment, oneWeight] using normalizedAngularProjector_const c

/-- Normalization and orthogonality assumptions for the harmonic basis
used in projection theorems. -/
structure HarmonicOrthogonalityAssumptions (P : Projector) : Prop where
  oneWeight_const : ∀ c, projectedMoment P oneWeight (fun _phiH _phiS => c) = c
  sinPhiDiff_self : projectedMoment P sinPhiDiff sinPhiDiff = 1 / 2
  sinPhiSum_self : projectedMoment P sinPhiSum sinPhiSum = 1 / 2
  sinPhiDiff_sinPhiSum : projectedMoment P sinPhiDiff sinPhiSum = 0
  sinPhiSum_sinPhiDiff : projectedMoment P sinPhiSum sinPhiDiff = 0

/--
The normalized angular projector is intended as the concrete projector behind the
harmonic-orthogonality layer.
-/
structure NormalizedAngularProjectorAssumptions : Prop where
  orthogonality : HarmonicOrthogonalityAssumptions normalizedAngularProjector

end Harmonics
end Asymmetries
end SIDIS
end DIS
end Scattering
end QFT
end Physlib
