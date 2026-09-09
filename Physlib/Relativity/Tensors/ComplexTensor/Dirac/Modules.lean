/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Modules
/-!

# Dirac modules

This file defines the module structures for Dirac spinors and dual Dirac spinors.

-/

@[expose] public section

namespace Fermion
noncomputable section

/-- Alias used in Dirac files for left-handed Weyl spinors. -/
abbrev LeftHandedModule := LeftHandedWeyl

/-- Alias used in Dirac files for right-handed Weyl spinors. -/
abbrev RightHandedModule := RightHandedWeyl

/-- Alias used in Dirac files for dual-left-handed Weyl spinors. -/
abbrev AltLeftHandedModule := DualLeftHandedWeyl

/-- Alias used in Dirac files for dual-right-handed Weyl spinors. -/
abbrev AltRightHandedModule := DualRightHandedWeyl

/-- The module in which Dirac fermions live, built from left and right Weyl modules. -/
structure DiracModule where
  /-- Left-handed Weyl component. -/
  left : LeftHandedModule
  /-- Right-handed Weyl component. -/
  right : RightHandedModule

namespace DiracModule

/-- The equivalence between `DiracModule` and `LeftHandedModule × RightHandedModule`. -/
def toProdFun : DiracModule ≃ (LeftHandedModule × RightHandedModule) where
  toFun ψ := ⟨ψ.left, ψ.right⟩
  invFun ψ := ⟨ψ.1, ψ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommMonoid DiracModule := Equiv.addCommMonoid toProdFun
instance : AddCommGroup DiracModule := Equiv.addCommGroup toProdFun
instance : Module ℂ DiracModule := Equiv.module ℂ toProdFun

/-- The linear equivalence between `DiracModule` and
`LeftHandedModule × RightHandedModule`. -/
@[simps!]
def toProdEquiv : DiracModule ≃ₗ[ℂ] (LeftHandedModule × RightHandedModule) :=
  Equiv.linearEquiv ℂ toProdFun

@[ext]
lemma ext (ψ φ : DiracModule) (hLeft : ψ.left = φ.left) (hRight : ψ.right = φ.right) : ψ = φ := by
  cases ψ
  cases φ
  simp at hLeft hRight
  simp [hLeft, hRight]

@[simp]
lemma left_add (ψ φ : DiracModule) : (ψ + φ).left = ψ.left + φ.left := rfl

@[simp]
lemma right_add (ψ φ : DiracModule) : (ψ + φ).right = ψ.right + φ.right := rfl

@[simp]
lemma left_smul (a : ℂ) (ψ : DiracModule) : (a • ψ).left = a • ψ.left := rfl

@[simp]
lemma right_smul (a : ℂ) (ψ : DiracModule) : (a • ψ).right = a • ψ.right := rfl

@[simp]
lemma left_zero : (0 : DiracModule).left = 0 := rfl

@[simp]
lemma right_zero : (0 : DiracModule).right = 0 := rfl

end DiracModule

/-- The module in which dual Dirac fermions live, built from dual-left and dual-right Weyl modules. -/
structure AltDiracModule where
  /-- Dual-left-handed Weyl component. -/
  left : AltLeftHandedModule
  /-- Dual-right-handed Weyl component. -/
  right : AltRightHandedModule

namespace AltDiracModule

/-- The equivalence between `AltDiracModule` and
`AltLeftHandedModule × AltRightHandedModule`. -/
def toProdFun : AltDiracModule ≃ (AltLeftHandedModule × AltRightHandedModule) where
  toFun ψ := ⟨ψ.left, ψ.right⟩
  invFun ψ := ⟨ψ.1, ψ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommMonoid AltDiracModule := Equiv.addCommMonoid toProdFun
instance : AddCommGroup AltDiracModule := Equiv.addCommGroup toProdFun
instance : Module ℂ AltDiracModule := Equiv.module ℂ toProdFun

/-- The linear equivalence between `AltDiracModule` and
`AltLeftHandedModule × AltRightHandedModule`. -/
@[simps!]
def toProdEquiv : AltDiracModule ≃ₗ[ℂ] (AltLeftHandedModule × AltRightHandedModule) :=
  Equiv.linearEquiv ℂ toProdFun

@[ext]
lemma ext (ψ φ : AltDiracModule) (hLeft : ψ.left = φ.left) (hRight : ψ.right = φ.right) : ψ = φ := by
  cases ψ
  cases φ
  simp at hLeft hRight
  simp [hLeft, hRight]

@[simp]
lemma left_add (ψ φ : AltDiracModule) : (ψ + φ).left = ψ.left + φ.left := rfl

@[simp]
lemma right_add (ψ φ : AltDiracModule) : (ψ + φ).right = ψ.right + φ.right := rfl

@[simp]
lemma left_smul (a : ℂ) (ψ : AltDiracModule) : (a • ψ).left = a • ψ.left := rfl

@[simp]
lemma right_smul (a : ℂ) (ψ : AltDiracModule) : (a • ψ).right = a • ψ.right := rfl

@[simp]
lemma left_zero : (0 : AltDiracModule).left = 0 := rfl

@[simp]
lemma right_zero : (0 : AltDiracModule).right = 0 := rfl

end AltDiracModule

end

end Fermion
