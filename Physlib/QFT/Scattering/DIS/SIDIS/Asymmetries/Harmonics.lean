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

/-- The normalized angular projector does **not** satisfy the harmonic-orthogonality
contract.

Its four quadrature nodes are `(phi_h, phi_S) ∈ {0, π} × {0, π}`, and both
`sin(phi_h - phi_S)` and `sin(phi_h + phi_S)` vanish at every one of them. The projector
therefore returns `0` for the self-moment of each harmonic, where the contract demands
`1 / 2`.

This replaces a `NormalizedAngularProjectorAssumptions` bundle that asserted the contract
*did* hold for this projector. That bundle had no dependent declarations, which is the only
reason nothing downstream was proved from a false hypothesis. -/
lemma not_harmonicOrthogonality_normalizedAngularProjector :
    ¬ HarmonicOrthogonalityAssumptions normalizedAngularProjector := by
  intro h
  have hz : projectedMoment normalizedAngularProjector sinPhiDiff sinPhiDiff = 0 := by
    simp only [projectedMoment, normalizedAngularProjector, sinPhiDiff]
    rw [show (0 : ℝ) - 0 = 0 by ring, show Real.pi - 0 = Real.pi by ring,
      show (0 : ℝ) - Real.pi = -Real.pi by ring, show Real.pi - Real.pi = 0 by ring]
    simp
  rw [h.sinPhiDiff_self] at hz
  -- `hz : (1 : ℝ) / 2 = 0`; make the contradiction explicit rather than relying on
  -- `norm_num` closing the goal as a side effect of simplifying the hypothesis.
  exact absurd hz (by norm_num)

/-- A four-node azimuthal quadrature projector with nodes
`(phi_h, phi_S) ∈ {π/4, 3π/4} × {π/4, -π/4}`.

Unlike `normalizedAngularProjector`, these nodes avoid the common zeros of the two sine
harmonics: `phi_h - phi_S` and `phi_h + phi_S` each take the value `π/2` at exactly two of
the four nodes and a zero of `sin` at the other two. -/
def harmonicQuadratureProjector : Projector :=
  fun f =>
    (f (Real.pi / 4) (Real.pi / 4) + f (3 * Real.pi / 4) (Real.pi / 4)
      + f (Real.pi / 4) (-(Real.pi / 4)) + f (3 * Real.pi / 4) (-(Real.pi / 4))) / 4

/-- The quadrature projector satisfies the abstract linearity contract. -/
lemma harmonicQuadratureProjector_isLinear :
    ProjectorAssumptions harmonicQuadratureProjector := by
  constructor
  · intro f g
    unfold harmonicQuadratureProjector
    ring
  · intro a f
    unfold harmonicQuadratureProjector
    ring

/-- The quadrature projector satisfies the harmonic-orthogonality contract.

This discharges `HarmonicOrthogonalityAssumptions` at a concrete projector, so the
downstream asymmetry and interference theorems that take it as a hypothesis have an
exhibited model. -/
lemma harmonicQuadratureProjector_orthogonality :
    HarmonicOrthogonalityAssumptions harmonicQuadratureProjector := by
  have d1 : Real.pi / 4 - Real.pi / 4 = 0 := by ring
  have d2 : 3 * Real.pi / 4 - Real.pi / 4 = Real.pi / 2 := by ring
  have d3 : Real.pi / 4 - -(Real.pi / 4) = Real.pi / 2 := by ring
  have d4 : 3 * Real.pi / 4 - -(Real.pi / 4) = Real.pi := by ring
  have s1 : Real.pi / 4 + Real.pi / 4 = Real.pi / 2 := by ring
  have s2 : 3 * Real.pi / 4 + Real.pi / 4 = Real.pi := by ring
  have s3 : Real.pi / 4 + -(Real.pi / 4) = 0 := by ring
  have s4 : 3 * Real.pi / 4 + -(Real.pi / 4) = Real.pi / 2 := by ring
  refine ⟨fun c => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [projectedMoment, harmonicQuadratureProjector, oneWeight]
    ring
  · simp only [projectedMoment, harmonicQuadratureProjector, sinPhiDiff]
    rw [d1, d2, d3, d4]
    norm_num [Real.sin_pi_div_two]
  · simp only [projectedMoment, harmonicQuadratureProjector, sinPhiSum]
    rw [s1, s2, s3, s4]
    norm_num [Real.sin_pi_div_two]
  · simp only [projectedMoment, harmonicQuadratureProjector, sinPhiDiff, sinPhiSum]
    rw [d1, d2, d3, d4, s1, s2, s3, s4]
    norm_num [Real.sin_pi_div_two]
  · simp only [projectedMoment, harmonicQuadratureProjector, sinPhiDiff, sinPhiSum]
    rw [d1, d2, d3, d4, s1, s2, s3, s4]
    norm_num [Real.sin_pi_div_two]

end Harmonics
end Asymmetries
end SIDIS
end DIS
end Scattering
end QFT
end Physlib
