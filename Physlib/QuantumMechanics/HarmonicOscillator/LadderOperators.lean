/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.HarmonicOscillator.Basic
public import Physlib.QuantumMechanics.Operators.Commutation
/-!

# Ladder operators

## i. Overview

The ladder operators of the `d`-dimensional quantum harmonic oscillator, acting on Schwartz maps:
the lowering (annihilation) operators `aᵢ = (xᵢ/ξᵢ + i ξᵢ pᵢ/ℏ)/√2`, the raising (creation)
operators `aᵢ† = (xᵢ/ξᵢ - i ξᵢ pᵢ/ℏ)/√2` and the number operators `Nᵢ = aᵢ† aᵢ`, together with
their commutation relations, which all follow from the canonical commutation relations
`position_commutation_momentum`. The adjointness of `aᵢ` and `aᵢ†`, the Hamiltonian in terms of the
number operators and its relation to the Hamiltonian of `Basic.lean` are still TODO items.

## ii. Key results

- `lowering_commutation_raising`: `[aᵢ, aⱼ†] = δᵢⱼ 𝟙`; `lowering_commutation_lowering`,
  `raising_commutation_raising`: `[aᵢ, aⱼ] = 0`, `[aᵢ†, aⱼ†] = 0`.
- `position_eq_lowering_add_raising`, `momentum_eq_raising_sub_lowering`: the position and
  momentum operators in terms of the ladder operators.
- `number_commutation_number`: `[Nᵢ, Nⱼ] = 0`; `number_commutation_lowering`,
  `number_commutation_raising`: `[Nᵢ, aⱼ] = -δᵢⱼ aⱼ`, `[Nᵢ, aⱼ†] = δᵢⱼ aⱼ†`.
- `lowering_comp_raising`: `aᵢ aᵢ† = Nᵢ + 𝟙`.

## iii. Table of contents

- A. Ladder operators
  - A.1. Definitions
  - A.2. Commutation relations
  - A.3. Position and momentum in terms of the ladder operators
- B. Number operators
  - B.1. Definition
  - B.2. Commutation relations
- C. Hamiltonian

## iv. References

* None.

-/

@[expose] public section

noncomputable section
namespace QuantumMechanics.HarmonicOscillator

open Complex Constants KroneckerDelta Bracket SchwartzMap ContinuousLinearMap

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra

variable {d : ℕ} (Q : HarmonicOscillator d) (i j : Fin d)

/-!

## A. Ladder operators

-/

/-!

### A.1. Definitions

-/

/-- The lowering (annihilation) operator `aᵢ = (xᵢ/ξᵢ + i ξᵢ pᵢ/ℏ)/√2`, as a continuous linear
  map on Schwartz maps. -/
def loweringCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (Real.sqrt 2 : ℂ)⁻¹ • (((Q.ξ i : ℝ) : ℂ)⁻¹ • 𝐱 i + (I * ((Q.ξ i : ℝ) : ℂ) / (ℏ : ℂ)) • 𝐩 i)

/-- The raising (creation) operator `aᵢ† = (xᵢ/ξᵢ - i ξᵢ pᵢ/ℏ)/√2`, as a continuous linear
  map on Schwartz maps. -/
def raisingCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (Real.sqrt 2 : ℂ)⁻¹ • (((Q.ξ i : ℝ) : ℂ)⁻¹ • 𝐱 i - (I * ((Q.ξ i : ℝ) : ℂ) / (ℏ : ℂ)) • 𝐩 i)

lemma loweringCLM_eq : Q.loweringCLM i =
    (Real.sqrt 2 : ℂ)⁻¹ • (((Q.ξ i : ℝ) : ℂ)⁻¹ • 𝐱 i + (I * ((Q.ξ i : ℝ) : ℂ) / (ℏ : ℂ)) • 𝐩 i) :=
  rfl

lemma raisingCLM_eq : Q.raisingCLM i =
    (Real.sqrt 2 : ℂ)⁻¹ • (((Q.ξ i : ℝ) : ℂ)⁻¹ • 𝐱 i - (I * ((Q.ξ i : ℝ) : ℂ) / (ℏ : ℂ)) • 𝐩 i) :=
  rfl

/-- `(√2)² = 2` as complex numbers. -/
lemma sqrt_two_sq_ofReal : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-!

### A.2. Commutation relations

-/

/-- `[aᵢ, aⱼ†] = δᵢⱼ 𝟙`. -/
lemma lowering_commutation_raising :
    ⁅Q.loweringCLM i, Q.raisingCLM j⁆ = δ[i,j] • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  simp only [loweringCLM, raisingCLM, lie_smul, smul_lie, add_lie, lie_sub,
    position_commutation_position, momentum_commutation_momentum, position_commutation_momentum,
    ← lie_skew (𝐩 i) (𝐱 j), smul_zero, zero_add, smul_neg, smul_smul, KroneckerDelta.symm j i]
  rcases eq_or_ne i j with rfl | hne
  · simp only [eq_one_of_same, one_nsmul, add_zero]
    ext ψ x
    simp only [smul_apply, neg_apply, sub_apply, id_apply, smul_eq_mul]
    have hξ := Q.ξ_ofReal_ne_zero i
    have hℏ := ℏ_ofReal_ne_zero
    ring_nf
    rw [I_sq, inv_pow, sqrt_two_sq_ofReal]
    field_simp
  · simp only [eq_zero_of_ne hne, zero_smul, smul_zero, sub_zero, neg_zero, add_zero]

/-- `[aᵢ, aⱼ] = 0`. -/
lemma lowering_commutation_lowering : ⁅Q.loweringCLM i, Q.loweringCLM j⁆ = 0 := by
  simp only [loweringCLM, lie_smul, smul_lie, lie_add, add_lie,
    position_commutation_position, momentum_commutation_momentum, position_commutation_momentum,
    ← lie_skew (𝐩 i) (𝐱 j), smul_zero, zero_add, smul_neg, smul_smul, KroneckerDelta.symm j i]
  rcases eq_or_ne i j with rfl | hne
  · ext ψ x
    simp only [eq_one_of_same, one_smul, add_zero, smul_add, smul_neg, add_apply, neg_apply,
      smul_apply, id_apply, smul_eq_mul, zero_apply]
    have hξ := Q.ξ_ofReal_ne_zero i
    have hℏ := ℏ_ofReal_ne_zero
    field_simp
    ring
  · simp [eq_zero_of_ne hne]

/-- `[aᵢ†, aⱼ†] = 0`. -/
lemma raising_commutation_raising : ⁅Q.raisingCLM i, Q.raisingCLM j⁆ = 0 := by
  simp only [raisingCLM, lie_smul, smul_lie, lie_sub, sub_lie,
    position_commutation_position, momentum_commutation_momentum, position_commutation_momentum,
    ← lie_skew (𝐩 i) (𝐱 j), smul_zero, zero_sub, smul_neg, smul_smul, KroneckerDelta.symm j i]
  rcases eq_or_ne i j with rfl | hne
  · ext ψ x
    simp only [eq_one_of_same, one_smul, neg_neg, sub_zero, smul_apply, sub_apply, id_apply,
      smul_eq_mul, zero_apply, mul_eq_zero, inv_eq_zero, ofReal_eq_zero, Nat.ofNat_nonneg,
      Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, false_or]
    have hξ := Q.ξ_ofReal_ne_zero i
    have hℏ := ℏ_ofReal_ne_zero
    field_simp
    ring
  · simp [eq_zero_of_ne hne]

/-- `[aᵢ†, aⱼ] = -δᵢⱼ 𝟙`. -/
lemma raising_commutation_lowering :
    ⁅Q.raisingCLM i, Q.loweringCLM j⁆ = -(δ[i,j] • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ)) := by
  rw [← lie_skew, lowering_commutation_raising, KroneckerDelta.symm j i]

/-!

### A.3. Position and momentum in terms of the ladder operators

-/

/-- `xᵢ = (ξᵢ/√2) (aᵢ + aᵢ†)`. -/
lemma position_eq_lowering_add_raising :
    𝐱 i = (((Q.ξ i : ℝ) : ℂ) / (Real.sqrt 2 : ℂ)) • (Q.loweringCLM i + Q.raisingCLM i) := by
  ext ψ x
  simp [loweringCLM, raisingCLM]
  have hξ := Q.ξ_ofReal_ne_zero i
  have hℏ := ℏ_ofReal_ne_zero
  ring_nf
  rw [inv_pow, sqrt_two_sq_ofReal]
  field_simp

/-- `pᵢ = (i ℏ/(√2 ξᵢ)) (aᵢ† - aᵢ)`. -/
lemma momentum_eq_raising_sub_lowering :
    𝐩 i = (I * (ℏ : ℂ) / ((Real.sqrt 2 : ℂ) * ((Q.ξ i : ℝ) : ℂ))) •
      (Q.raisingCLM i - Q.loweringCLM i) := by
  ext ψ x
  simp [loweringCLM, raisingCLM]
  have hξ := Q.ξ_ofReal_ne_zero i
  have hℏ := ℏ_ofReal_ne_zero
  ring_nf
  rw [I_pow_three, inv_pow, sqrt_two_sq_ofReal]
  field_simp

TODO "Prove that the raising/lowering operators are adjoints of one another (tag as simp?)."

/-!

## B. Number operators

-/

/-!

### B.1. Definition

-/

/-- The number operator `Nᵢ = aᵢ† aᵢ`. -/
def numberCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := Q.raisingCLM i ∘L Q.loweringCLM i

lemma numberCLM_eq : Q.numberCLM i = Q.raisingCLM i ∘L Q.loweringCLM i := rfl

TODO "Prove that the number operators are symmetric/self-adjoint."

/-!

### B.2. Commutation relations

-/

/-- `[Nᵢ, aⱼ] = -δᵢⱼ aⱼ`. -/
lemma number_commutation_lowering :
    ⁅Q.numberCLM i, Q.loweringCLM j⁆ = -(δ[i,j] • Q.loweringCLM j) := by
  rw [numberCLM_eq, leibniz_lie, lowering_commutation_lowering, raising_commutation_lowering,
    comp_zero, zero_add, neg_comp, smul_comp, id_comp]
  rcases eq_or_ne i j with rfl | hne
  · rfl
  · simp [eq_zero_of_ne hne]

/-- `[Nᵢ, aⱼ†] = δᵢⱼ aⱼ†`. -/
lemma number_commutation_raising :
    ⁅Q.numberCLM i, Q.raisingCLM j⁆ = δ[i,j] • Q.raisingCLM j := by
  rw [numberCLM_eq, leibniz_lie, lowering_commutation_raising, raising_commutation_raising,
    zero_comp, add_zero, comp_smul, comp_id]
  rcases eq_or_ne i j with rfl | hne
  · rfl
  · simp [eq_zero_of_ne hne]

/-- `[Nᵢ, Nⱼ] = 0`. -/
lemma number_commutation_number : ⁅Q.numberCLM i, Q.numberCLM j⁆ = 0 := by
  simp only [numberCLM_eq]
  rw [leibniz_lie, lie_leibniz, lie_leibniz, lowering_commutation_lowering,
    lowering_commutation_raising, raising_commutation_lowering, raising_commutation_raising]
  rcases eq_or_ne i j with rfl | hne
  · simp only [eq_one_of_same, one_nsmul, comp_zero, zero_add, id_comp, comp_id, neg_comp,
      comp_neg, zero_comp, add_zero]
    abel
  · simp [eq_zero_of_ne hne]

/-- `aᵢ aᵢ† = Nᵢ + 𝟙`. -/
lemma lowering_comp_raising :
    Q.loweringCLM i ∘L Q.raisingCLM i =
      Q.numberCLM i + ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  have h := Q.lowering_commutation_raising i i
  rw [eq_one_of_same, one_nsmul, Ring.lie_def, mul_def, mul_def] at h
  rw [numberCLM_eq, add_comm]
  exact sub_eq_iff_eq_add.mp h

/-!

## C. Hamiltonian

-/

TODO "Define a Hamiltonian in terms of the number operators."

TODO "Prove the commutation relations between the Hamiltonian and ladder/number operators."

TODO "Relate the 'number operator' Hamiltonian to the 'K + T' Hamiltonian
  (=/≤/≥ depending on their domains)."

TODO "Prove that the two Hamiltonians define the same quantum system."

end QuantumMechanics.HarmonicOscillator

end
