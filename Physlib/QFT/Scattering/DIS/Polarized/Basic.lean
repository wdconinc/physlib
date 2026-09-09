/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Tensors.Basic
/-!

# Polarized DIS Interfaces (Stage 10)

This module introduces polarized DIS interfaces: a structure-function container for
`g₁`, `g₂`, an antisymmetry assumption on the polarized hadronic tensor, a decomposition
schema, and endpoint conditions at `x = 1`. The moment identities usually called sum rules
live in `Physlib.QFT.Scattering.DIS.Polarized.SumRules`.

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

/-- Endpoint conditions on the polarized structure functions at the elastic point `x = 1`.

These are *not* sum rules: a sum rule is an identity for a moment `∫₀¹ dx xⁿ g(x, Q²)`,
whereas the fields below are pointwise statements at the single point `x = 1`. The real
moment identities (Bjorken, Ellis-Jaffe, Burkhardt-Cottingham) are stated in
`Physlib.QFT.Scattering.DIS.Polarized.SumRules`. -/
structure EndpointAssumptions (G : StructureFunctions) : Prop where
  /-- `g₁` vanishes at the elastic endpoint `x = 1`, at every scale. -/
  g1_vanishes_at_one : ∀ Q2, G.g1 1 Q2 = 0
  /-- `g₂` vanishes at the elastic endpoint `x = 1`, at every scale. -/
  g2_vanishes_at_one : ∀ Q2, G.g2 1 Q2 = 0

/-- Interface projection: `g₁` vanishes at `x = 1`. -/
lemma g1_vanishes_at_one
    (G : StructureFunctions)
    (h : EndpointAssumptions G)
    (Q2 : ℝ) :
    G.g1 1 Q2 = 0 :=
  h.g1_vanishes_at_one Q2

/-- Interface projection: `g₂` vanishes at `x = 1`. -/
lemma g2_vanishes_at_one
    (G : StructureFunctions)
    (h : EndpointAssumptions G)
    (Q2 : ℝ) :
    G.g2 1 Q2 = 0 :=
  h.g2_vanishes_at_one Q2

end Polarized
end DIS
end Scattering
end QFT
end Physlib
