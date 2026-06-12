/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Tensors.Basic
/-!

# Polarized DIS Interfaces (Stage 10)

This module introduces polarized DIS interfaces and sum-rule schemas.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Polarized

variable (V : Type) [AddCommGroup V] [Module ℝ V]

abbrev Bilin := LinearMap.BilinForm ℝ V

/-- Minimal polarized structure-function container. -/
structure StructureFunctions where
  g1 : ℝ → ℝ → ℝ
  g2 : ℝ → ℝ → ℝ

/-- Assumptions for a polarized hadronic tensor interface. -/
structure TensorAssumptions (A : Bilin V) : Prop where
  antisymm : ∀ v w : V, A v w = -A w v

/-- Polarized decomposition schema. -/
def IsPolarizedDecomposition
    (G : StructureFunctions)
    (A : Bilin V) : Prop :=
  ∀ x Q2, A = (G.g1 x Q2 + G.g2 x Q2) • A

/-- Sum-rule assumptions for polarized DIS. -/
structure SumRuleAssumptions (G : StructureFunctions) : Prop where
  bjorken : ∀ Q2, G.g1 1 Q2 = 0
  ellisJaffe : ∀ Q2, G.g2 1 Q2 = 0

/-- Bjorken-style sum-rule interface theorem. -/
lemma bjorken_sumRule
    (G : StructureFunctions)
    (h : SumRuleAssumptions G)
    (Q2 : ℝ) :
    G.g1 1 Q2 = 0 :=
  h.bjorken Q2

/-- Ellis-Jaffe-style sum-rule interface theorem. -/
lemma ellisJaffe_sumRule
    (G : StructureFunctions)
    (h : SumRuleAssumptions G)
    (Q2 : ℝ) :
    G.g2 1 Q2 = 0 :=
  h.ellisJaffe Q2

end Polarized
end DIS
end Scattering
end QFT
end Physlib
