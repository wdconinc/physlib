/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
/-!

# Linear independence of real-frequency exponentials

This file may eventually be upstreamed to Mathlib.

## i. Overview

For pairwise distinct real numbers `ω i`, the functions `τ ↦ exp (I * ω i * τ)` are linearly
independent over `ℂ`: a vanishing `ℂ`-linear combination of them, holding for every real `τ`,
forces every coefficient to vanish. This is Dedekind's linear independence of characters
(`linearIndependent_monoidHom`), applied to the characters `Multiplicative ℝ →* ℂ` given by
`ω ↦ (τ ↦ exp (I * ω * τ))`, together with the elementary fact that distinct real `ω` give
distinct characters.

Physlib uses this to derive `Electromagnetism.Interface.PhaseMatchedAtInterface` from literal
continuity of monochromatic fields across a planar interface: continuity, projected onto a test
direction, becomes an identity between finitely many real-frequency cosines holding for every
real parameter, and this file's machinery is what forces the frequencies appearing in that
identity to coincide.

## ii. Key results

- `Real.eq_of_forall_exp_I_mul_eq` : if `exp (I * ω₁ * τ) = exp (I * ω₂ * τ)` for every `τ : ℝ`,
  then `ω₁ = ω₂`.
- `Real.eq_zero_of_forall_sum_exp_I_mul_eq_zero` : if `∑ i, c i * exp (I * ω i * τ) = 0` for
  every `τ : ℝ`, with the `ω i` pairwise distinct, then every `c i = 0`.

## iii. Table of contents

- A. Real frequencies are determined by their exponential
- B. Linear independence of finitely many real-frequency exponentials

## iv. References

* Keith Conrad, "Linear independence of characters",
  <https://kconrad.math.uconn.edu/blurbs/galoistheory/linearchar.pdf>. [ref: conrad_linearchar]
-/

@[expose] public section

namespace Real

/-!

## A. Real frequencies are determined by their exponential

-/

/-- If `exp (I * ω₁ * τ) = exp (I * ω₂ * τ)` for every real `τ`, then `ω₁ = ω₂`. Distinct
  frequencies give exponentials agreeing only on a discrete set of `τ` (where their difference's
  phase happens to be a multiple of `2π`), never on all of `ℝ`. -/
theorem eq_of_forall_exp_I_mul_eq {ω₁ ω₂ : ℝ}
    (h : ∀ τ : ℝ, Complex.exp (Complex.I * ω₁ * τ) = Complex.exp (Complex.I * ω₂ * τ)) :
    ω₁ = ω₂ := by
  by_contra hne
  have hsub : ω₁ - ω₂ ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (h (Real.pi / (ω₁ - ω₂)))
  have hcancel : ((ω₁ : ℂ) - ω₂) * (Real.pi / (ω₁ - ω₂) : ℝ) = (n : ℂ) * (2 * Real.pi) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    push_cast
    linear_combination hn
  rw [show ((Real.pi / (ω₁ - ω₂) : ℝ) : ℂ) = (Real.pi : ℂ) / ((ω₁ : ℂ) - ω₂) by push_cast; ring,
    mul_div_cancel₀ (Real.pi : ℂ) (by exact_mod_cast hsub)] at hcancel
  have hreal : Real.pi = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast hcancel
  have : (1 : ℝ) = n * 2 := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp at hreal
    linarith [hreal]
  have hn2 : (n : ℝ) * 2 ≠ 1 := by
    have : ∃ m : ℤ, (n : ℝ) * 2 = (2 * m : ℤ) := ⟨n, by push_cast; ring⟩
    obtain ⟨m, hm⟩ := this
    rw [hm]
    intro hcontra
    have : (2 * m : ℤ) = 1 := by exact_mod_cast hcontra
    omega
  exact hn2 this

/-!

## B. Linear independence of finitely many real-frequency exponentials

-/

/-- If `∑ i, c i * exp (I * ω i * τ) = 0` for every real `τ`, with the `ω i` pairwise distinct,
  then every coefficient `c i` vanishes. This is Dedekind's linear independence of characters
  (`linearIndependent_monoidHom`), applied to the characters of `(ℝ, +)` given by the `ω i`. -/
theorem eq_zero_of_forall_sum_exp_I_mul_eq_zero {ι : Type*} [Fintype ι]
    {ω : ι → ℝ} (hω : Function.Injective ω) {c : ι → ℂ}
    (h : ∀ τ : ℝ, ∑ i, c i * Complex.exp (Complex.I * ω i * τ) = 0) :
    ∀ i, c i = 0 := by
  let χ : ι → AddChar ℝ ℂ := fun i =>
    { toFun := fun τ => Complex.exp (Complex.I * ω i * τ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun x y => by push_cast; rw [mul_add, Complex.exp_add] }
  have hinj : Function.Injective (fun i => (χ i).toMonoidHom) := by
    intro i j hij
    apply hω
    apply eq_of_forall_exp_I_mul_eq (ω₁ := ω i) (ω₂ := ω j)
    intro τ
    have := DFunLike.congr_fun hij (Multiplicative.ofAdd τ)
    simpa [χ, AddChar.toMonoidHom_apply] using this
  have hli : LinearIndependent ℂ (fun i => ((χ i).toMonoidHom : Multiplicative ℝ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  apply hli c
  funext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, AddChar.toMonoidHom_apply,
    Pi.zero_apply]
  simpa [χ] using h a.toAdd

end Real
