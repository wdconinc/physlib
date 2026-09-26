/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Complex.Trigonometric
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

Section C derives, from this, the "distinct sinusoids can't sum to a third" fact used to
recover `Electromagnetism.Interface.PhaseMatchedAtInterface` from literal field continuity:
if `A cos (ω₁τ+φ₁) + B cos (ω₂τ+φ₂) = C cos (ω₃τ+φ₃)` for every real `τ`, with `A, B, C ≠ 0`
and `ω₁, ω₂, ω₃ > 0`, then `ω₁ = ω₂ = ω₃`.

## ii. Key results
- `Real.eq_of_forall_cos_add_cos_eq_cos` : distinct positive-frequency sinusoids can't sum to a
  third.

## iii. Table of contents

- A. Real frequencies are determined by their exponential
- B. Linear independence of finitely many real-frequency exponentials
- C. Distinct sinusoids can't sum to a third

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
    push_cast at hn ⊢
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
  exact hn2 this.symm

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

/-!

## C. Distinct sinusoids can't sum to a third

-/

/-- Twice `D * cos (ω*τ+φ)`, as a complex number, splits into a sum of two exponentials at
  frequencies `ω` and `-ω` (Euler's formula). -/
private lemma two_mul_cos_eq_exp_add_exp (D ω φ τ : ℝ) :
    (2 : ℂ) * (D : ℂ) * (Real.cos (ω * τ + φ) : ℂ) =
    (D : ℂ) * Complex.exp (Complex.I * φ) * Complex.exp (Complex.I * ω * τ) +
    (D : ℂ) * Complex.exp (-Complex.I * φ) * Complex.exp (Complex.I * (-ω) * τ) := by
  have e1 : Complex.exp (((ω * τ + φ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * φ) * Complex.exp (Complex.I * ω * τ) := by
    rw [show (((ω * τ + φ : ℝ) : ℂ) * Complex.I) = (Complex.I * (φ : ℂ)) + (Complex.I * ω * τ)
      from by push_cast; ring, Complex.exp_add]
  have e2 : Complex.exp ((-((ω * τ + φ : ℝ) : ℂ)) * Complex.I) =
      Complex.exp (-Complex.I * φ) * Complex.exp (Complex.I * (-ω) * τ) := by
    rw [show ((-((ω * τ + φ : ℝ) : ℂ)) * Complex.I) =
      (-Complex.I * (φ : ℂ)) + (Complex.I * (-ω) * τ) from by push_cast; ring, Complex.exp_add]
  have hcos : (2 : ℂ) * Complex.cos ((ω * τ + φ : ℝ) : ℂ) =
      Complex.exp (((ω * τ + φ : ℝ) : ℂ) * Complex.I) +
      Complex.exp ((-((ω * τ + φ : ℝ) : ℂ)) * Complex.I) := Complex.two_cos _
  rw [e1, e2] at hcos
  rw [Complex.ofReal_cos]
  linear_combination (D : ℂ) * hcos

/-- Two positive, distinct frequencies `v₀ ≠ v₁` give four pairwise distinct signed frequencies
  `v₀, -v₀, v₁, -v₁`: a positive value never equals the negative of another positive value. -/
private lemma injective_two_signed {v₀ v₁ : ℝ} (h₀ : 0 < v₀) (h₁ : 0 < v₁) (hne : v₀ ≠ v₁) :
    Function.Injective (![v₀, -v₀, v₁, -v₁] : Fin 4 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first | rfl | (exfalso; nlinarith [h₀, h₁])

/-- Three pairwise distinct positive frequencies give six pairwise distinct signed frequencies. -/
private lemma injective_three_signed {v₀ v₁ v₂ : ℝ} (h₀ : 0 < v₀) (h₁ : 0 < v₁) (h₂ : 0 < v₂)
    (h01 : v₀ ≠ v₁) (h02 : v₀ ≠ v₂) (h12 : v₁ ≠ v₂) :
    Function.Injective (![v₀, -v₀, v₁, -v₁, v₂, -v₂] : Fin 6 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first | rfl | (exfalso; nlinarith [h₀, h₁, h₂])

/-- If `A cos (ω₁τ+φ₁) + B cos (ω₂τ+φ₂) = C cos (ω₃τ+φ₃)` for every real `τ`, with `A, B, C ≠ 0`
  and `ω₁, ω₂, ω₃ > 0`, then `ω₁ = ω₃` and `ω₂ = ω₃`. Two positive-frequency sinusoids can only
  sum to a third if all three frequencies coincide: expanded via Euler's formula, the identity
  becomes a vanishing `ℂ`-linear combination of exponentials at frequencies `±ω₁, ±ω₂, ±ω₃`; since
  `A, B, C ≠ 0` every one of the six exponential coefficients is nonzero, so
  `eq_zero_of_forall_sum_exp_I_mul_eq_zero` forces at least two of these six frequencies to
  coincide, and positivity rules out any sign-crossed coincidence. Each of the three ways exactly
  two of `ω₁, ω₂, ω₃` could coincide is then ruled out in turn: the frequency not involved in the
  coincidence is isolated from every other frequency in the (regrouped) exponential sum, so its
  own nonzero coefficient would be forced to vanish — a contradiction. -/
theorem eq_of_forall_cos_add_cos_eq_cos {A B C ω₁ ω₂ ω₃ φ₁ φ₂ φ₃ : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (hω₃ : 0 < ω₃)
    (h : ∀ τ : ℝ, A * Real.cos (ω₁ * τ + φ₁) + B * Real.cos (ω₂ * τ + φ₂) =
      C * Real.cos (ω₃ * τ + φ₃)) :
    ω₁ = ω₃ ∧ ω₂ = ω₃ := by
  have hsum : ∀ τ : ℝ,
      (A : ℂ) * Complex.exp (Complex.I * φ₁) * Complex.exp (Complex.I * ω₁ * τ) +
      (A : ℂ) * Complex.exp (-Complex.I * φ₁) * Complex.exp (Complex.I * (-ω₁) * τ) +
      ((B : ℂ) * Complex.exp (Complex.I * φ₂) * Complex.exp (Complex.I * ω₂ * τ) +
      (B : ℂ) * Complex.exp (-Complex.I * φ₂) * Complex.exp (Complex.I * (-ω₂) * τ)) -
      ((C : ℂ) * Complex.exp (Complex.I * φ₃) * Complex.exp (Complex.I * ω₃ * τ) +
      (C : ℂ) * Complex.exp (-Complex.I * φ₃) * Complex.exp (Complex.I * (-ω₃) * τ)) = 0 := by
    intro τ
    have hreal : A * Real.cos (ω₁ * τ + φ₁) + B * Real.cos (ω₂ * τ + φ₂) -
        C * Real.cos (ω₃ * τ + φ₃) = 0 := by linarith [h τ]
    have hcplx : (A : ℂ) * (Real.cos (ω₁ * τ + φ₁) : ℂ) + (B : ℂ) * (Real.cos (ω₂ * τ + φ₂) : ℂ) -
        (C : ℂ) * (Real.cos (ω₃ * τ + φ₃) : ℂ) = 0 := by exact_mod_cast hreal
    linear_combination - two_mul_cos_eq_exp_add_exp A ω₁ φ₁ τ -
      two_mul_cos_eq_exp_add_exp B ω₂ φ₂ τ + two_mul_cos_eq_exp_add_exp C ω₃ φ₃ τ + 2 * hcplx
  by_cases h12 : ω₁ = ω₂
  · by_cases h13 : ω₁ = ω₃
    · exact ⟨h13, h12.symm.trans h13⟩
    · exfalso
      subst h12
      have hsum4 : ∀ τ : ℝ, ∑ i : Fin 4,
          (![(A : ℂ) * Complex.exp (Complex.I * φ₁) + (B : ℂ) * Complex.exp (Complex.I * φ₂),
             (A : ℂ) * Complex.exp (-Complex.I * φ₁) + (B : ℂ) * Complex.exp (-Complex.I * φ₂),
             -(C : ℂ) * Complex.exp (Complex.I * φ₃),
             -(C : ℂ) * Complex.exp (-Complex.I * φ₃)] : Fin 4 → ℂ) i *
          Complex.exp (Complex.I * (![ω₁, -ω₁, ω₃, -ω₃] : Fin 4 → ℝ) i * τ) = 0 := by
        intro τ
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Fin.val_succ, add_zero]
        push_cast
        linear_combination hsum τ
      have hz := eq_zero_of_forall_sum_exp_I_mul_eq_zero
        (injective_two_signed hω₁ hω₃ h13) hsum4 2
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hz
      rw [mul_eq_zero] at hz
      rcases hz with hz | hz
      · exact hC (by exact_mod_cast neg_eq_zero.mp hz)
      · exact absurd hz (Complex.exp_ne_zero _)
  · by_cases h13 : ω₁ = ω₃
    · by_cases h23 : ω₂ = ω₃
      · exact ⟨h13, h23⟩
      · exfalso
        subst h13
        have hsum4 : ∀ τ : ℝ, ∑ i : Fin 4,
            (![(A : ℂ) * Complex.exp (Complex.I * φ₁) - (C : ℂ) * Complex.exp (Complex.I * φ₃),
               (A : ℂ) * Complex.exp (-Complex.I * φ₁) - (C : ℂ) * Complex.exp (-Complex.I * φ₃),
               (B : ℂ) * Complex.exp (Complex.I * φ₂),
               (B : ℂ) * Complex.exp (-Complex.I * φ₂)] : Fin 4 → ℂ) i *
            Complex.exp (Complex.I * (![ω₁, -ω₁, ω₂, -ω₂] : Fin 4 → ℝ) i * τ) = 0 := by
          intro τ
          simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Fin.val_succ, add_zero]
          push_cast
          linear_combination hsum τ
        have hz := eq_zero_of_forall_sum_exp_I_mul_eq_zero
          (injective_two_signed hω₁ hω₂ h12) hsum4 2
        simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hz
        rw [mul_eq_zero] at hz
        rcases hz with hz | hz
        · exact hB (by exact_mod_cast hz)
        · exact absurd hz (Complex.exp_ne_zero _)
    · by_cases h23 : ω₂ = ω₃
      · exfalso
        subst h23
        have hsum4 : ∀ τ : ℝ, ∑ i : Fin 4,
            (![(B : ℂ) * Complex.exp (Complex.I * φ₂) - (C : ℂ) * Complex.exp (Complex.I * φ₃),
               (B : ℂ) * Complex.exp (-Complex.I * φ₂) - (C : ℂ) * Complex.exp (-Complex.I * φ₃),
               (A : ℂ) * Complex.exp (Complex.I * φ₁),
               (A : ℂ) * Complex.exp (-Complex.I * φ₁)] : Fin 4 → ℂ) i *
            Complex.exp (Complex.I * (![ω₂, -ω₂, ω₁, -ω₁] : Fin 4 → ℝ) i * τ) = 0 := by
          intro τ
          simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Fin.val_succ, add_zero]
          push_cast
          linear_combination hsum τ
        have hz := eq_zero_of_forall_sum_exp_I_mul_eq_zero
          (injective_two_signed hω₂ hω₁ (Ne.symm h12)) hsum4 2
        simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hz
        rw [mul_eq_zero] at hz
        rcases hz with hz | hz
        · exact hA (by exact_mod_cast hz)
        · exact absurd hz (Complex.exp_ne_zero _)
      · exfalso
        have hsum6 : ∀ τ : ℝ, ∑ i : Fin 6,
            (![(A : ℂ) * Complex.exp (Complex.I * φ₁),
               (A : ℂ) * Complex.exp (-Complex.I * φ₁),
               (B : ℂ) * Complex.exp (Complex.I * φ₂),
               (B : ℂ) * Complex.exp (-Complex.I * φ₂),
               -(C : ℂ) * Complex.exp (Complex.I * φ₃),
               -(C : ℂ) * Complex.exp (-Complex.I * φ₃)] : Fin 6 → ℂ) i *
            Complex.exp (Complex.I * (![ω₁, -ω₁, ω₂, -ω₂, ω₃, -ω₃] : Fin 6 → ℝ) i * τ) = 0 := by
          intro τ
          simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Fin.val_succ, add_zero]
          push_cast
          linear_combination hsum τ
        have hz := eq_zero_of_forall_sum_exp_I_mul_eq_zero
          (injective_three_signed hω₁ hω₂ hω₃ h12 h13 h23) hsum6 4
        simp only [Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons] at hz
        rw [mul_eq_zero] at hz
        rcases hz with hz | hz
        · exact hC (by exact_mod_cast neg_eq_zero.mp hz)
        · exact absurd hz (Complex.exp_ne_zero _)

end Real
