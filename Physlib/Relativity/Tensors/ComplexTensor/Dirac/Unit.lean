/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Dirac.Contraction
/-!

# Unit-like morphisms for Dirac spinors

This file packages canonical chiral endomorphisms used in Dirac calculations.

-/

@[expose] public section

namespace Fermion
noncomputable section

/-- Left chiral idempotent viewed as a unit-like morphism. -/
abbrev leftChiralUnit : diracRep.IntertwiningMap diracRep := Pₗ

/-- Right chiral idempotent viewed as a unit-like morphism. -/
abbrev rightChiralUnit : diracRep.IntertwiningMap diracRep := Pᵣ

@[simp]
lemma leftChiralUnit_apply (ψ : DiracModule) : leftChiralUnit ψ = Pₗ ψ := rfl

@[simp]
lemma rightChiralUnit_apply (ψ : DiracModule) : rightChiralUnit ψ = Pᵣ ψ := rfl

@[simp]
lemma leftChiralUnit_add_rightChiralUnit (ψ : DiracModule) :
    leftChiralUnit ψ + rightChiralUnit ψ = ψ :=
  leftProjector_add_rightProjector ψ

end

end Fermion
