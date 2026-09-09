/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Dirac.Two
public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Contraction
/-!

# Contractions for Dirac spinors

This file defines basic bilinear contractions between Dirac and dual Dirac spinors.

-/

@[expose] public section

namespace Fermion
noncomputable section

/-- The bilinear contraction pairing a Dirac spinor and a dual Dirac spinor. -/
def diracAltBi : DiracModule →ₗ[ℂ] AltDiracModule →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => leftDualBi ψ.left φ.left + rightDualBi ψ.right φ.right
    map_add' := by
      intro φ χ
      simp [map_add, add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro a φ
      simp [map_smul, mul_add]
  }
  map_add' := by
    intro ψ χ
    ext φ
    simp [map_add, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a ψ
    ext φ
    simp [map_smul, mul_add]

@[simp]
lemma diracAltBi_apply (ψ : DiracModule) (φ : AltDiracModule) :
    (diracAltBi ψ) φ = leftDualBi ψ.left φ.left + rightDualBi ψ.right φ.right := rfl

@[simp]
lemma diracAltBi_left_only (ψ : LeftHandedModule) (φ : AltLeftHandedModule) :
    (diracAltBi ⟨ψ, 0⟩) ⟨φ, 0⟩ = leftDualBi ψ φ := by
  simp [diracAltBi]

@[simp]
lemma diracAltBi_right_only (ψ : RightHandedModule) (φ : AltRightHandedModule) :
    (diracAltBi ⟨0, ψ⟩) ⟨0, φ⟩ = rightDualBi ψ φ := by
  simp [diracAltBi]

end

end Fermion
