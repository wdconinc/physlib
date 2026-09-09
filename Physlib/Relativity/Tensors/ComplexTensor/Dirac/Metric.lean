/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Dirac.Unit
/-!

# Basic Dirac metric-like operators

This file defines chirality splitting operators built from Dirac projectors.

-/

@[expose] public section

namespace Fermion
noncomputable section

/-- The chirality splitting operator `Pₗ - Pᵣ` on Dirac spinors. -/
def chiralityOperator : diracRep.IntertwiningMap diracRep := Pₗ - Pᵣ

@[simp]
lemma chiralityOperator_apply (ψ : DiracModule) :
    chiralityOperator ψ = Pₗ ψ - Pᵣ ψ := rfl

@[simp]
lemma chiralityOperator_sq_apply (ψ : DiracModule) :
    chiralityOperator (chiralityOperator ψ) = ψ := by
  ext <;> simp [chiralityOperator, sub_eq_add_neg]

end

end Fermion
