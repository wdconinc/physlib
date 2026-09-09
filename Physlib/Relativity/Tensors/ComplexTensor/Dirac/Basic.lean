/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Dirac.Modules
public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Basic
/-!

# Dirac fermions

This file defines Dirac and dual-Dirac representations from Weyl representations.

-/

@[expose] public section

namespace Fermion
noncomputable section

open MatrixGroups

/-- Alias used in Dirac files for the dual-left-handed representation. -/
abbrev altLeftHandedRep := dualLeftHandedRep

/-- Alias used in Dirac files for the dual-right-handed representation. -/
abbrev altRightHandedRep := dualRightHandedRep

/-- The representation of `SL(2, ℂ)` on Dirac fermions induced from
left- and right-handed Weyl representations. -/
def diracRep : Representation ℂ SL(2,ℂ) DiracModule where
  toFun M := {
    toFun := fun ψ => ⟨leftHandedRep M ψ.left, rightHandedRep M ψ.right⟩
    map_add' := by
      intro ψ φ
      ext <;> simp
    map_smul' := by
      intro a ψ
      ext <;> simp
  }
  map_one' := by
    ext ψ <;> simp
  map_mul' := by
    intro M N
    ext ψ <;> simp

/-- The representation of `SL(2, ℂ)` on dual Dirac fermions induced from
dual-left and dual-right Weyl representations. -/
def altDiracRep : Representation ℂ SL(2,ℂ) AltDiracModule where
  toFun M := {
    toFun := fun ψ => ⟨altLeftHandedRep M ψ.left, altRightHandedRep M ψ.right⟩
    map_add' := by
      intro ψ φ
      ext <;> simp
    map_smul' := by
      intro a ψ
      ext <;> simp
  }
  map_one' := by
    ext ψ <;> simp
  map_mul' := by
    intro M N
    ext ψ <;> simp

@[simp]
lemma diracRep_apply_left (M : SL(2,ℂ)) (ψ : DiracModule) :
    (diracRep M ψ).left = leftHandedRep M ψ.left := rfl

@[simp]
lemma diracRep_apply_right (M : SL(2,ℂ)) (ψ : DiracModule) :
    (diracRep M ψ).right = rightHandedRep M ψ.right := rfl

@[simp]
lemma altDiracRep_apply_left (M : SL(2,ℂ)) (ψ : AltDiracModule) :
    (altDiracRep M ψ).left = altLeftHandedRep M ψ.left := rfl

@[simp]
lemma altDiracRep_apply_right (M : SL(2,ℂ)) (ψ : AltDiracModule) :
    (altDiracRep M ψ).right = altRightHandedRep M ψ.right := rfl

/-- The Weyl-pair representation on `LeftHandedModule × RightHandedModule`. -/
def weylPairRep : Representation ℂ SL(2,ℂ) (LeftHandedModule × RightHandedModule) :=
  Representation.prod leftHandedRep rightHandedRep

/-- The Dirac representation is equivalent to the product Weyl representation. -/
def diracRepEquivWeylPair : diracRep.Equiv weylPairRep :=
  Representation.Equiv.mk DiracModule.toProdEquiv fun M => by
    ext ψ <;> rfl

/-- Inclusion of left-handed Weyl spinors into Dirac spinors. -/
def leftToDirac : leftHandedRep.IntertwiningMap diracRep where
  toFun ψ := ⟨ψ, 0⟩
  map_add' := by
    intro ψ φ
    ext <;> simp
  map_smul' := by
    intro a ψ
    ext <;> simp
  isIntertwining' := by
    intro M
    ext ψ <;> simp

/-- Inclusion of right-handed Weyl spinors into Dirac spinors. -/
def rightToDirac : rightHandedRep.IntertwiningMap diracRep where
  toFun ψ := ⟨0, ψ⟩
  map_add' := by
    intro ψ φ
    ext <;> simp
  map_smul' := by
    intro a ψ
    ext <;> simp
  isIntertwining' := by
    intro M
    ext ψ <;> simp

/-- Projection from Dirac spinors to the left-handed Weyl component. -/
def diracToLeft : diracRep.IntertwiningMap leftHandedRep where
  toFun ψ := ψ.left
  map_add' := by
    intro ψ φ
    simp
  map_smul' := by
    intro a ψ
    simp
  isIntertwining' := by
    intro M
    ext ψ; simp

/-- Projection from Dirac spinors to the right-handed Weyl component. -/
def diracToRight : diracRep.IntertwiningMap rightHandedRep where
  toFun ψ := ψ.right
  map_add' := by
    intro ψ φ
    simp
  map_smul' := by
    intro a ψ
    simp
  isIntertwining' := by
    intro M
    ext ψ; simp

/-- Inclusion of dual-left-handed Weyl spinors into dual Dirac spinors. -/
def altLeftToAltDirac : altLeftHandedRep.IntertwiningMap altDiracRep where
  toFun ψ := ⟨ψ, 0⟩
  map_add' := by
    intro ψ φ
    ext <;> simp
  map_smul' := by
    intro a ψ
    ext <;> simp
  isIntertwining' := by
    intro M
    ext ψ <;> simp

/-- Inclusion of dual-right-handed Weyl spinors into dual Dirac spinors. -/
def altRightToAltDirac : altRightHandedRep.IntertwiningMap altDiracRep where
  toFun ψ := ⟨0, ψ⟩
  map_add' := by
    intro ψ φ
    ext <;> simp
  map_smul' := by
    intro a ψ
    ext <;> simp
  isIntertwining' := by
    intro M
    ext ψ <;> simp

/-- Projection from dual Dirac spinors to the dual-left-handed Weyl component. -/
def altDiracToAltLeft : altDiracRep.IntertwiningMap altLeftHandedRep where
  toFun ψ := ψ.left
  map_add' := by
    intro ψ φ
    simp
  map_smul' := by
    intro a ψ
    simp
  isIntertwining' := by
    intro M
    ext ψ; simp

/-- Projection from dual Dirac spinors to the dual-right-handed Weyl component. -/
def altDiracToAltRight : altDiracRep.IntertwiningMap altRightHandedRep where
  toFun ψ := ψ.right
  map_add' := by
    intro ψ φ
    simp
  map_smul' := by
    intro a ψ
    simp
  isIntertwining' := by
    intro M
    ext ψ; simp

/-- Left-chiral projector as a Dirac endomorphism intertwiner. -/
def leftProjector : diracRep.IntertwiningMap diracRep where
  toFun ψ := ⟨ψ.left, 0⟩
  map_add' := by
    intro ψ φ
    ext <;> simp
  map_smul' := by
    intro a ψ
    ext <;> simp
  isIntertwining' := by
    intro M
    ext ψ <;> simp

/-- Right-chiral projector as a Dirac endomorphism intertwiner. -/
def rightProjector : diracRep.IntertwiningMap diracRep where
  toFun ψ := ⟨0, ψ.right⟩
  map_add' := by
    intro ψ φ
    ext <;> simp
  map_smul' := by
    intro a ψ
    ext <;> simp
  isIntertwining' := by
    intro M
    ext ψ <;> simp

/-- Left-chiral projector on dual Dirac spinors. -/
def altLeftProjector : altDiracRep.IntertwiningMap altDiracRep where
  toFun ψ := ⟨ψ.left, 0⟩
  map_add' := by
    intro ψ φ
    ext <;> simp
  map_smul' := by
    intro a ψ
    ext <;> simp
  isIntertwining' := by
    intro M
    ext ψ <;> simp

/-- Right-chiral projector on dual Dirac spinors. -/
def altRightProjector : altDiracRep.IntertwiningMap altDiracRep where
  toFun ψ := ⟨0, ψ.right⟩
  map_add' := by
    intro ψ φ
    ext <;> simp
  map_smul' := by
    intro a ψ
    ext <;> simp
  isIntertwining' := by
    intro M
    ext ψ <;> simp

/-- Standard notation for the left chiral projector. -/
notation "Pₗ" => leftProjector

/-- Standard notation for the right chiral projector. -/
notation "Pᵣ" => rightProjector

/-- Standard notation for the dual-left chiral projector. -/
notation "Pₗᵃ" => altLeftProjector

/-- Standard notation for the dual-right chiral projector. -/
notation "Pᵣᵃ" => altRightProjector

@[simp]
lemma leftProjector_add_rightProjector (ψ : DiracModule) :
    Pₗ ψ + Pᵣ ψ = ψ := by
  ext <;> simp [leftProjector, rightProjector]

@[simp]
lemma leftProjector_idem (ψ : DiracModule) : Pₗ (Pₗ ψ) = Pₗ ψ := by
  ext <;> simp [leftProjector]

@[simp]
lemma rightProjector_idem (ψ : DiracModule) :
    Pᵣ (Pᵣ ψ) = Pᵣ ψ := by
  ext <;> simp [rightProjector]

@[simp]
lemma leftProjector_rightProjector (ψ : DiracModule) : Pₗ (Pᵣ ψ) = 0 := by
  ext <;> simp [leftProjector, rightProjector]

@[simp]
lemma rightProjector_leftProjector (ψ : DiracModule) : Pᵣ (Pₗ ψ) = 0 := by
  ext <;> simp [leftProjector, rightProjector]

@[simp]
lemma diracToLeft_comp_leftToDirac :
    diracToLeft.toLinearMap.comp leftToDirac.toLinearMap = LinearMap.id := by
  ext ψ
  rfl

@[simp]
lemma diracToRight_comp_rightToDirac :
    diracToRight.toLinearMap.comp rightToDirac.toLinearMap = LinearMap.id := by
  ext ψ
  rfl

@[simp]
lemma diracToLeft_comp_rightToDirac :
    (diracToLeft.toLinearMap.comp rightToDirac.toLinearMap :
      RightHandedModule →ₗ[ℂ] LeftHandedModule) = 0 := by
  ext ψ
  rfl

@[simp]
lemma diracToRight_comp_leftToDirac :
    (diracToRight.toLinearMap.comp leftToDirac.toLinearMap :
      LeftHandedModule →ₗ[ℂ] RightHandedModule) = 0 := by
  ext ψ
  rfl

@[simp]
lemma leftToDirac_comp_diracToLeft_apply (ψ : DiracModule) :
    leftToDirac (diracToLeft ψ) = Pₗ ψ := rfl

@[simp]
lemma rightToDirac_comp_diracToRight_apply (ψ : DiracModule) :
    rightToDirac (diracToRight ψ) = Pᵣ ψ := rfl

@[simp]
lemma diracRep_apply_leftProjector (M : SL(2,ℂ)) (ψ : DiracModule) :
    diracRep M (Pₗ ψ) = Pₗ (diracRep M ψ) := by
  ext <;> simp [leftProjector]

@[simp]
lemma diracRep_apply_rightProjector (M : SL(2,ℂ)) (ψ : DiracModule) :
    diracRep M (Pᵣ ψ) = Pᵣ (diracRep M ψ) := by
  ext <;> simp [rightProjector]

end

end Fermion
