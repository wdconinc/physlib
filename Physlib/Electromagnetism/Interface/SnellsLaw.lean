/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Interface.Basic
public import Physlib.Electromagnetism.Dynamics.Basic
/-!

# Snell's law and the law of reflection

## i. Overview

A monochromatic plane wave of wavenumber `κ` travelling in direction `s` in a medium `𝓕`
(a `FreeSpace`, i.e. a linear, homogeneous, isotropic medium with characteristic speed
`𝓕.c = 1/√(ε₀μ₀)`) has wavevector `κ • s.unit` and angular frequency `κ * 𝓕.c`; both are
forced by Maxwell's equations, since `IsPlaneWave 𝓕 A s` (`Electromagnetism.Vacuum.IsPlaneWave`)
already parametrizes solutions of Maxwell's equations by exactly this phase convention.

At a planar interface between two such media, continuity of the tangential components of
the electric and magnetic fields (Maxwell's boundary conditions, in the absence of free
surface charge or current) forces, for monochromatic waves, the incident, reflected and
transmitted waves to share a common angular frequency and a common tangential wavevector.
This module takes that fact — `PhaseMatchedAtInterface` — as a named hypothesis (it is *not*
re-derived here from a discontinuous-medium formulation of Maxwell's equations, which would
require the distributional machinery of `Electromagnetism.Distributional`; see the module
docstring of `PhaseMatchedAtInterface` for the precise scope note) and derives from it the law
of reflection and Snell's law, using only the geometry of `Electromagnetism.Interface.Basic`.

## ii. Key results

- `PhaseMatchedAtInterface` : the hypothesis that incident, reflected and transmitted
  monochromatic plane waves share a common frequency and tangential wavevector at the
  interface.
- `lawOfReflection` : the angle of incidence and the angle of reflection have equal sine.
- `snellsLaw` : `|κ_i| * sin θ_i = |κ_t| * sin θ_t`, the vector/wavenumber form of Snell's law.
- `snellsLaw_refractiveIndex` : `n₁ * sin θ_i = n₂ * sin θ_t`, the textbook form of Snell's law,
  where `n₁, n₂` are the refractive indices of the two media relative to a reference medium.

## iii. Table of contents

- A. Phase matching at an interface
- B. The law of reflection
- C. Snell's law

## iv. References

* None.
-/

@[expose] public section

namespace Electromagnetism
namespace Interface

open Space

/-!

## A. Phase matching at an interface

-/

/-- The hypothesis that an incident wave (wavenumber `κ_i`, direction `s_i`, medium `𝓕₁`), a
  reflected wave (`κ_r`, `s_r`, same medium `𝓕₁`) and a transmitted wave (`κ_t`, `s_t`, medium
  `𝓕₂`) are phase-matched at the interface with normal `n̂`: they share a common angular
  frequency, and their wavevectors have a common projection onto the interface.

  Physically, this is what continuity of the tangential electric and magnetic fields at the
  interface forces for monochromatic plane waves (Maxwell's boundary conditions, with no free
  surface charge or current). It is taken here as a hypothesis rather than derived from a
  discontinuous-medium Maxwell formulation — matching the scope note in
  `Electromagnetism.ThreeDimension.MaxwellEquations`, which already excludes boundary
  conditions and constitutive laws for material media. -/
def PhaseMatchedAtInterface {d : ℕ} (n̂ : Direction d) (𝓕₁ : FreeSpace) (κ_i : ℝ)
    (s_i : Direction d) (κ_r : ℝ) (s_r : Direction d) (𝓕₂ : FreeSpace) (κ_t : ℝ)
    (s_t : Direction d) : Prop :=
  κ_i * (𝓕₁.c : ℝ) = κ_r * (𝓕₁.c : ℝ) ∧
  κ_r * (𝓕₁.c : ℝ) = κ_t * (𝓕₂.c : ℝ) ∧
  tangentialPart n̂ (κ_i • s_i.unit) = tangentialPart n̂ (κ_r • s_r.unit) ∧
  tangentialPart n̂ (κ_i • s_i.unit) = tangentialPart n̂ (κ_t • s_t.unit)

/-!

## B. The law of reflection

-/

/-- The angle of incidence and the angle of reflection have equal sine.

  This does not by itself rule out `angleFromNormal n̂ s_r = π - angleFromNormal n̂ s_i`, the
  other root of `sin θ_r = sin θ_i` on `[0, π]`: distinguishing it from the physical
  `angleFromNormal n̂ s_r = angleFromNormal n̂ s_i` requires a sign convention for which side of
  the interface the reflected wave travels into, which is not fixed by phase matching alone
  (phase matching only constrains the tangential wavevector, not the sign of its normal
  component). Left as a documented gap for a follow-up. -/
theorem lawOfReflection {d : ℕ} (n̂ : Direction d) (𝓕 𝓕₂ : FreeSpace) (κ_i : ℝ) (hκ_i : κ_i ≠ 0)
    (s_i : Direction d) (κ_r : ℝ) (s_r : Direction d) (κ_t : ℝ) (s_t : Direction d)
    (h : PhaseMatchedAtInterface n̂ 𝓕 κ_i s_i κ_r s_r 𝓕₂ κ_t s_t) :
    Real.sin (angleFromNormal n̂ s_i) = Real.sin (angleFromNormal n̂ s_r) := by
  obtain ⟨hfreq, -, htan, -⟩ := h
  have hκr : κ_i = κ_r := mul_right_cancel₀ 𝓕.c.val_ne_zero hfreq
  have hnorm := congrArg norm htan
  rw [norm_tangentialPart_smul_unit, norm_tangentialPart_smul_unit, ← hκr] at hnorm
  exact mul_left_cancel₀ (abs_ne_zero.mpr hκ_i) hnorm

/-!

## C. Snell's law

-/

/-- Snell's law in wavenumber form: `|κ_i| * sin θ_i = |κ_t| * sin θ_t`. Unlike
  `lawOfReflection`, no sign convention is needed here — the statement is purely about norms
  of tangential wavevectors, which phase matching determines directly. -/
theorem snellsLaw {d : ℕ} (n̂ : Direction d) (𝓕₁ 𝓕₂ : FreeSpace) (κ_i : ℝ) (s_i : Direction d)
    (κ_r : ℝ) (s_r : Direction d) (κ_t : ℝ) (s_t : Direction d)
    (h : PhaseMatchedAtInterface n̂ 𝓕₁ κ_i s_i κ_r s_r 𝓕₂ κ_t s_t) :
    |κ_i| * Real.sin (angleFromNormal n̂ s_i) = |κ_t| * Real.sin (angleFromNormal n̂ s_t) := by
  have hnorm := congrArg norm h.2.2.2
  rwa [norm_tangentialPart_smul_unit, norm_tangentialPart_smul_unit] at hnorm

/-- The refractive index of a medium `𝓕` relative to a reference medium `𝓕₀`. -/
noncomputable def refractiveIndex (𝓕₀ 𝓕 : FreeSpace) : ℝ := (𝓕₀.c : ℝ) / (𝓕.c : ℝ)

/-- Snell's law in the textbook form `n₁ * sin θ_i = n₂ * sin θ_t`, where `n₁, n₂` are the
  refractive indices of the incidence and transmission media relative to any common reference
  medium `𝓕₀` (e.g. vacuum). -/
theorem snellsLaw_refractiveIndex {d : ℕ} (n̂ : Direction d) (𝓕₀ 𝓕₁ 𝓕₂ : FreeSpace) (κ_i : ℝ)
    (hκ_i : 0 < κ_i) (s_i : Direction d) (κ_r : ℝ) (s_r : Direction d) (κ_t : ℝ)
    (s_t : Direction d) (h : PhaseMatchedAtInterface n̂ 𝓕₁ κ_i s_i κ_r s_r 𝓕₂ κ_t s_t) :
    refractiveIndex 𝓕₀ 𝓕₁ * Real.sin (angleFromNormal n̂ s_i) =
    refractiveIndex 𝓕₀ 𝓕₂ * Real.sin (angleFromNormal n̂ s_t) := by
  obtain ⟨hfreq_ir, hfreq_rt, -, htan_it⟩ := h
  have hfreq : κ_i * (𝓕₁.c : ℝ) = κ_t * (𝓕₂.c : ℝ) := hfreq_ir.trans hfreq_rt
  have hκt : 0 < κ_t := by
    by_contra hle
    push_neg at hle
    have hnn : 0 ≤ (-κ_t) * (𝓕₂.c : ℝ) := mul_nonneg (neg_nonneg.mpr hle) 𝓕₂.c.pos.le
    nlinarith [hfreq, mul_pos hκ_i 𝓕₁.c.pos, hnn]
  have hsin : κ_i * Real.sin (angleFromNormal n̂ s_i) = κ_t * Real.sin (angleFromNormal n̂ s_t) := by
    have hnorm := congrArg norm htan_it
    rwa [norm_tangentialPart_smul_unit, norm_tangentialPart_smul_unit, abs_of_pos hκ_i,
      abs_of_pos hκt] at hnorm
  have key : Real.sin (angleFromNormal n̂ s_i) * (𝓕₂.c : ℝ) =
      (𝓕₁.c : ℝ) * Real.sin (angleFromNormal n̂ s_t) := by
    apply mul_left_cancel₀ (ne_of_gt hκ_i)
    linear_combination (𝓕₂.c : ℝ) * hsin - Real.sin (angleFromNormal n̂ s_t) * hfreq
  unfold refractiveIndex
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_div_iff 𝓕₁.c.val_ne_zero 𝓕₂.c.val_ne_zero]
  linear_combination (𝓕₀.c : ℝ) * key

end Interface
end Electromagnetism
