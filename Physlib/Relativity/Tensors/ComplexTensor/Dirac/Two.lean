/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Dirac.Basic
/-!

# Two-spinor decomposition for Dirac modules

This file packages split and block-decomposition results for Dirac representations.

-/

@[expose] public section

namespace Fermion
noncomputable section

lemma dirac_decompose (ψ : DiracModule) :
    ψ = leftToDirac (diracToLeft ψ) + rightToDirac (diracToRight ψ) := by
  ext <;> simp

lemma leftToDirac_comp_diracToLeft_add_rightToDirac_comp_diracToRight :
    leftToDirac.toLinearMap.comp diracToLeft.toLinearMap
      + rightToDirac.toLinearMap.comp diracToRight.toLinearMap = LinearMap.id := by
  ext ψ <;> simp [LinearMap.add_apply]

lemma range_leftProjector_eq_range_leftToDirac :
    LinearMap.range leftProjector.toLinearMap = LinearMap.range leftToDirac.toLinearMap := by
  ext ψ
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨diracToLeft x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨leftToDirac x, rfl⟩

lemma range_rightProjector_eq_range_rightToDirac :
    LinearMap.range rightProjector.toLinearMap = LinearMap.range rightToDirac.toLinearMap := by
  ext ψ
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨diracToRight x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨rightToDirac x, rfl⟩

lemma ker_leftProjector_eq_range_rightToDirac :
    LinearMap.ker leftProjector.toLinearMap = LinearMap.range rightToDirac.toLinearMap := by
  ext ψ
  constructor
  · intro hψ
    refine ⟨ψ.right, ?_⟩
    apply DiracModule.ext
    ·
      have hψ' : leftProjector ψ = 0 := by simpa [LinearMap.mem_ker] using hψ
      have hleft : ψ.left = 0 := by simpa [leftProjector] using congrArg DiracModule.left hψ'
      simp [rightToDirac, hleft]
    · simp [rightToDirac]
  · rintro ⟨x, rfl⟩
    simp [LinearMap.mem_ker, leftProjector, rightToDirac, DiracModule.ext_iff]

lemma ker_rightProjector_eq_range_leftToDirac :
    LinearMap.ker rightProjector.toLinearMap = LinearMap.range leftToDirac.toLinearMap := by
  ext ψ
  constructor
  · intro hψ
    refine ⟨ψ.left, ?_⟩
    apply DiracModule.ext
    · simp [leftToDirac]
    ·
      have hψ' : rightProjector ψ = 0 := by simpa [LinearMap.mem_ker] using hψ
      have hright : ψ.right = 0 := by simpa [rightProjector] using congrArg DiracModule.right hψ'
      simp [leftToDirac, hright]
  · rintro ⟨x, rfl⟩
    simp [LinearMap.mem_ker, rightProjector, leftToDirac, DiracModule.ext_iff]

section UniversalProperty

variable {V : Type*} [AddCommMonoid V] [Module ℂ V]
  (ρ : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V)

/-- Build a Dirac-valued intertwiner from its left and right Weyl components. -/
def diracLift (fL : ρ.IntertwiningMap leftHandedRep) (fR : ρ.IntertwiningMap rightHandedRep) :
    ρ.IntertwiningMap diracRep where
  toFun v := ⟨fL v, fR v⟩
  map_add' := by
    intro v w
    ext <;> simp
  map_smul' := by
    intro a v
    ext <;> simp
  isIntertwining' := by
    intro M
    ext v <;> simp [fL.isIntertwining, fR.isIntertwining]

@[simp]
lemma diracToLeft_comp_diracLift
    (fL : ρ.IntertwiningMap leftHandedRep) (fR : ρ.IntertwiningMap rightHandedRep) :
    diracToLeft.comp (diracLift ρ fL fR) = fL := by
  ext v
  rfl

@[simp]
lemma diracToRight_comp_diracLift
    (fL : ρ.IntertwiningMap leftHandedRep) (fR : ρ.IntertwiningMap rightHandedRep) :
    diracToRight.comp (diracLift ρ fL fR) = fR := by
  ext v
  rfl

/-- Universal property of the split Dirac representation. -/
def diracLiftEquiv :
    (ρ.IntertwiningMap diracRep) ≃
      ((ρ.IntertwiningMap leftHandedRep) × (ρ.IntertwiningMap rightHandedRep)) where
  toFun F := ⟨diracToLeft.comp F, diracToRight.comp F⟩
  invFun p := diracLift ρ p.1 p.2
  left_inv F := by
    rfl
  right_inv p := by
    rcases p with ⟨fL, fR⟩
    ext v <;> rfl

end UniversalProperty

/-- The left-left block of an equivariant Dirac endomorphism. -/
def blockLL (F : diracRep.IntertwiningMap diracRep) :
    leftHandedRep.IntertwiningMap leftHandedRep :=
  diracToLeft.comp (F.comp leftToDirac)

/-- The right-to-left block of an equivariant Dirac endomorphism. -/
def blockLR (F : diracRep.IntertwiningMap diracRep) :
    rightHandedRep.IntertwiningMap leftHandedRep :=
  diracToLeft.comp (F.comp rightToDirac)

/-- The left-to-right block of an equivariant Dirac endomorphism. -/
def blockRL (F : diracRep.IntertwiningMap diracRep) :
    leftHandedRep.IntertwiningMap rightHandedRep :=
  diracToRight.comp (F.comp leftToDirac)

/-- The right-right block of an equivariant Dirac endomorphism. -/
def blockRR (F : diracRep.IntertwiningMap diracRep) :
    rightHandedRep.IntertwiningMap rightHandedRep :=
  diracToRight.comp (F.comp rightToDirac)

/-- Block decomposition of an equivariant Dirac endomorphism. -/
lemma dirac_endomorphism_block_decompose
    (F : diracRep.IntertwiningMap diracRep) (ψ : DiracModule) :
    F ψ =
      leftToDirac (blockLL F ψ.left + blockLR F ψ.right) +
      rightToDirac (blockRL F ψ.left + blockRR F ψ.right) := by
  have hψ : leftToDirac ψ.left + rightToDirac ψ.right = ψ := (dirac_decompose ψ).symm
  have hL :
      Pₗ (F (leftToDirac ψ.left)) + Pᵣ (F (leftToDirac ψ.left)) = F (leftToDirac ψ.left) :=
    leftProjector_add_rightProjector (ψ := F (leftToDirac ψ.left))
  have hR :
      Pₗ (F (rightToDirac ψ.right)) + Pᵣ (F (rightToDirac ψ.right)) = F (rightToDirac ψ.right) :=
    leftProjector_add_rightProjector (ψ := F (rightToDirac ψ.right))
  conv_lhs => rw [← hψ]
  calc
    F (leftToDirac ψ.left + rightToDirac ψ.right) =
        F (leftToDirac ψ.left) + F (rightToDirac ψ.right) := by rw [map_add]
    _ = (Pₗ (F (leftToDirac ψ.left)) + Pᵣ (F (leftToDirac ψ.left))) +
          (Pₗ (F (rightToDirac ψ.right)) + Pᵣ (F (rightToDirac ψ.right))) := by rw [hL, hR]
    _ = leftToDirac (blockLL F ψ.left + blockLR F ψ.right) +
          rightToDirac (blockRL F ψ.left + blockRR F ψ.right) := by
        apply DiracModule.ext <;>
          simp [-leftProjector_add_rightProjector, blockLL, blockLR, blockRL, blockRR,
            leftProjector, rightProjector, add_assoc, add_left_comm, add_comm]

/-- Left-handed spinors are canonically equivalent to the range of `leftToDirac`. -/
def leftToDiracRangeEquiv : LeftHandedModule ≃ₗ[ℂ] LinearMap.range leftToDirac.toLinearMap :=
  LinearEquiv.ofInjective leftToDirac.toLinearMap <| by
    intro ψ φ h
    simpa [leftToDirac] using congrArg DiracModule.left h

/-- Right-handed spinors are canonically equivalent to the range of `rightToDirac`. -/
def rightToDiracRangeEquiv : RightHandedModule ≃ₗ[ℂ] LinearMap.range rightToDirac.toLinearMap :=
  LinearEquiv.ofInjective rightToDirac.toLinearMap <| by
    intro ψ φ h
    simpa [rightToDirac] using congrArg DiracModule.right h

/-- The range of the left projector is canonically equivalent to left-handed spinors. -/
def leftProjectorRangeEquivLeft : LinearMap.range leftProjector.toLinearMap ≃ₗ[ℂ] LeftHandedModule :=
  (LinearEquiv.ofEq _ _ range_leftProjector_eq_range_leftToDirac).trans leftToDiracRangeEquiv.symm

/-- The range of the right projector is canonically equivalent to right-handed spinors. -/
def rightProjectorRangeEquivRight : LinearMap.range rightProjector.toLinearMap ≃ₗ[ℂ] RightHandedModule :=
  (LinearEquiv.ofEq _ _ range_rightProjector_eq_range_rightToDirac).trans rightToDiracRangeEquiv.symm

end

end Fermion
