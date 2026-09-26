/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Interface.SnellsLaw
public import Physlib.Electromagnetism.Vacuum.HarmonicWaveDirection
public import Physlib.Mathematics.Trigonometry.CharacterIndependence
/-!

# Frequency matching from field continuity

## i. Overview

`PhaseMatchedAtInterface` (`Electromagnetism.Interface.SnellsLaw`) is taken there as a
hypothesis, documented as what continuity of the tangential electric field forces for
monochromatic plane waves at an interface. This module derives its *frequency* clause —
`κ_i * 𝓕₁.c = κ_r * 𝓕₁.c = κ_t * 𝓕₂.c` — from literal continuity of the tangential electric
field at the origin of the interface (a point common to any planar interface through it).

The argument: projecting the continuity equation onto a tangential test direction `w` at the
spatial origin `x = 0` (where every wave's spatial phase `⟪0, s.unit⟫_ℝ` vanishes) turns it into
an identity between three real-frequency cosines in the time variable `τ = t`,
`A cos (ω_i τ + φ_i) + A' cos (ω_r τ + φ_r) = A'' cos (ω_t τ + φ_t)` for every `τ : ℝ`, with
`ω_i = κ_i * 𝓕₁.c`, etc.; `Real.eq_of_forall_cos_add_cos_eq_cos`
(`Physlib.Mathematics.Trigonometry.CharacterIndependence`) forces the three frequencies to
coincide, provided the projected amplitudes `A, A', A''` are nonzero for `w` — a nondegeneracy
hypothesis on the wave amplitudes, since a generic choice of the three amplitude vectors admits
some tangential `w` making all three projections nonzero, but this module takes the existence of
such a `w` as a hypothesis rather than proving it.

This derives only the frequency clause of `PhaseMatchedAtInterface`, not the tangential
wavevector clause: the analogous argument along a tangential spatial direction produces
cosines whose frequencies `κ * ⟪w.unit, s.unit⟫_ℝ` can be zero or of either sign depending on
`w`, and `Real.eq_of_forall_cos_add_cos_eq_cos` (stated for positive frequencies, to keep its
case analysis tractable) does not apply to that signed, possibly-vanishing case without further
work. Left as a documented gap for a future extension.

## ii. Key results

- `freq_eq_of_tangentialE_continuity_at_origin` : equal angular frequency for the incident,
  reflected and transmitted waves, from continuity of the tangential electric field at the
  spatial origin of the interface, for every time `t`.

## iii. Table of contents

- A. Frequency matching from field continuity

## iv. References

* None.
-/

@[expose] public section

namespace Electromagnetism
namespace Interface

open Space ElectromagneticPotential

/-!

## A. Frequency matching from field continuity

-/

/-- Equal angular frequency for the incident, reflected and transmitted waves
  (`κ_i * 𝓕₁.c = κ_r * 𝓕₁.c` and `κ_r * 𝓕₁.c = κ_t * 𝓕₂.c`, the frequency clause of
  `PhaseMatchedAtInterface`), derived from continuity of the tangential electric field at the
  spatial origin of the interface with normal `n`, for every time `t`, given a tangential
  direction `w` (`⟪w.unit, n.unit⟫_ℝ = 0`) along which all three waves have nonzero amplitude
  (a nondegeneracy hypothesis: it holds, e.g., whenever `E₀_i, E₀_r, E₀_t` are not all
  orthogonal to some common tangential direction). -/
theorem freq_eq_of_tangentialE_continuity_at_origin {d : ℕ} (n : Direction d)
    (𝓕₁ 𝓕₂ : FreeSpace) (κ_i : ℝ) (hκ_i : 0 < κ_i) (s_i : Direction d)
    (E₀_i : EuclideanSpace ℝ (Fin d)) (φ_i : ℝ)
    (κ_r : ℝ) (hκ_r : 0 < κ_r) (s_r : Direction d)
    (E₀_r : EuclideanSpace ℝ (Fin d)) (φ_r : ℝ)
    (κ_t : ℝ) (hκ_t : 0 < κ_t) (s_t : Direction d)
    (E₀_t : EuclideanSpace ℝ (Fin d)) (φ_t : ℝ)
    (w : Direction d) (hw : ⟪w.unit, n.unit⟫_ℝ = 0)
    (hAi : (∑ k, w.unit k * E₀_i k) ≠ 0) (hAr : (∑ k, w.unit k * E₀_r k) ≠ 0)
    (hAt : (∑ k, w.unit k * E₀_t k) ≠ 0)
    (hcont : ∀ t : Time,
      (∑ k, w.unit k * (harmonicWave 𝓕₁ κ_i s_i E₀_i φ_i).electricField 𝓕₁.c t 0 k) +
      (∑ k, w.unit k * (harmonicWave 𝓕₁ κ_r s_r E₀_r φ_r).electricField 𝓕₁.c t 0 k) =
      ∑ k, w.unit k * (harmonicWave 𝓕₂ κ_t s_t E₀_t φ_t).electricField 𝓕₂.c t 0 k) :
    κ_i * 𝓕₁.c.val = κ_r * 𝓕₁.c.val ∧ κ_r * 𝓕₁.c.val = κ_t * 𝓕₂.c.val := by
  have hcos : ∀ t : Time,
      (∑ k, w.unit k * E₀_i k) * Real.cos (κ_i * 𝓕₁.c.val * t + φ_i) +
      (∑ k, w.unit k * E₀_r k) * Real.cos (κ_r * 𝓕₁.c.val * t + φ_r) =
      (∑ k, w.unit k * E₀_t k) * Real.cos (κ_t * 𝓕₂.c.val * t + φ_t) := by
    intro t
    have e1 := hcont t
    rw [harmonicWave_electricField 𝓕₁ κ_i hκ_i.ne' s_i E₀_i φ_i,
      harmonicWave_electricField 𝓕₁ κ_r hκ_r.ne' s_r E₀_r φ_r,
      harmonicWave_electricField 𝓕₂ κ_t hκ_t.ne' s_t E₀_t φ_t] at e1
    simp only [planeWave_eq, inner_zero_left, zero_sub, Pi.smul_apply, PiLp.smul_apply,
      smul_eq_mul, ← Finset.mul_sum] at e1
    unfold harmonicWaveEAmp at e1
    rw [show (-κ_i * (0 - 𝓕₁.c.val * t.val) + φ_i) = κ_i * 𝓕₁.c.val * t.val + φ_i from by ring,
      show (-κ_r * (0 - 𝓕₁.c.val * t.val) + φ_r) = κ_r * 𝓕₁.c.val * t.val + φ_r from by ring,
      show (-κ_t * (0 - 𝓕₂.c.val * t.val) + φ_t) = κ_t * 𝓕₂.c.val * t.val + φ_t from by ring] at e1
    linarith [e1, mul_comm (∑ k, w.unit k * E₀_i k) (Real.cos (κ_i * 𝓕₁.c.val * t.val + φ_i)),
      mul_comm (∑ k, w.unit k * E₀_r k) (Real.cos (κ_r * 𝓕₁.c.val * t.val + φ_r)),
      mul_comm (∑ k, w.unit k * E₀_t k) (Real.cos (κ_t * 𝓕₂.c.val * t.val + φ_t))]
  have main := Real.eq_of_forall_cos_add_cos_eq_cos hAi hAr hAt
    (mul_pos hκ_i 𝓕₁.c.pos) (mul_pos hκ_r 𝓕₁.c.pos) (mul_pos hκ_t 𝓕₂.c.pos) hcos
  exact ⟨main.1.trans main.2.symm, main.2⟩

end Interface
end Electromagnetism
