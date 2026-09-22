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
  /-- The polarized structure function `g₁(x, Q²)`, in the Bjorken variable `x`
  and the virtuality `Q²`. -/
  g1 : ℝ → ℝ → ℝ
  /-- The polarized structure function `g₂(x, Q²)`, in the Bjorken variable `x`
  and the virtuality `Q²`. -/
  g2 : ℝ → ℝ → ℝ

/-- Structural assumptions on a polarized structure-function pair, mirroring
`Physlib.Particles.Parton.PDF.Assumptions`.

These are what makes any *moment* statement about `G` meaningful: without support and
integrability there is no reason for `∫₀¹ dx g₁(x, Q²)` to be anything but the junk value
that `MeasureTheory.integral` returns on a non-integrable function.

Integrability is required only on the physical support `[0, 1]` (`IntegrableOn`), not on
all of `ℝ`; combined with `support_g1` / `support_g2` that is equivalent to global
integrability, and it is the weaker hypothesis to discharge for a fit. -/
structure Assumptions (G : StructureFunctions) : Prop where
  /-- `g₁` is supported in the physical interval `[0, 1]`. -/
  support_g1 : ∀ x Q2, x < 0 ∨ 1 < x → G.g1 x Q2 = 0
  /-- `g₂` is supported in the physical interval `[0, 1]`. -/
  support_g2 : ∀ x Q2, x < 0 ∨ 1 < x → G.g2 x Q2 = 0
  /-- `g₁(·, Q²)` is almost-everywhere strongly measurable at every scale. -/
  measurable_g1 : ∀ Q2, MeasureTheory.AEStronglyMeasurable (fun x : ℝ => G.g1 x Q2)
  /-- `g₂(·, Q²)` is almost-everywhere strongly measurable at every scale. -/
  measurable_g2 : ∀ Q2, MeasureTheory.AEStronglyMeasurable (fun x : ℝ => G.g2 x Q2)
  /-- `g₁(·, Q²)` is integrable on the physical support at every scale. -/
  integrableOn_g1 : ∀ Q2,
    MeasureTheory.IntegrableOn (fun x : ℝ => G.g1 x Q2) (Set.Icc (0 : ℝ) 1)
  /-- `g₂(·, Q²)` is integrable on the physical support at every scale. -/
  integrableOn_g2 : ∀ Q2,
    MeasureTheory.IntegrableOn (fun x : ℝ => G.g2 x Q2) (Set.Icc (0 : ℝ) 1)

/-! ### The analytic/physical split of `Assumptions`

The bundle mixes a definition with an obligation, as its collinear counterpart does.
`HasPhysicalSupport` is the physical half: outside `[0, 1]` there is no inclusive scattering
process for `g₁` and `g₂` to describe, so their vanishing there is part of what a polarized
structure-function pair is, not a theorem waiting to be proved. `Regularity` is the analytic
half — measurability and integrability on the physical support — and is discharged for an
explicit pair in `Physlib.QFT.Scattering.DIS.Polarized.SumRules`.

The field set of `Assumptions` is unchanged. It had no dependent declaration anywhere in the
repository when this was written, so the split is additive rather than a migration.
-/

/-- **The physical half of `Assumptions`**: both polarized structure functions vanish
outside the physical range `[0, 1]` of the Bjorken variable. -/
structure HasPhysicalSupport (G : StructureFunctions) : Prop where
  /-- `g₁` is supported in the physical interval `[0, 1]`. -/
  support_g1 : ∀ x Q2, x < 0 ∨ 1 < x → G.g1 x Q2 = 0
  /-- `g₂` is supported in the physical interval `[0, 1]`. -/
  support_g2 : ∀ x Q2, x < 0 ∨ 1 < x → G.g2 x Q2 = 0

/-- **The analytic half of `Assumptions`**: measurability at every scale and integrability on
the physical support. -/
structure Regularity (G : StructureFunctions) : Prop where
  /-- `g₁(·, Q²)` is almost-everywhere strongly measurable at every scale. -/
  measurable_g1 : ∀ Q2, MeasureTheory.AEStronglyMeasurable (fun x : ℝ => G.g1 x Q2)
  /-- `g₂(·, Q²)` is almost-everywhere strongly measurable at every scale. -/
  measurable_g2 : ∀ Q2, MeasureTheory.AEStronglyMeasurable (fun x : ℝ => G.g2 x Q2)
  /-- `g₁(·, Q²)` is integrable on the physical support at every scale. -/
  integrableOn_g1 : ∀ Q2,
    MeasureTheory.IntegrableOn (fun x : ℝ => G.g1 x Q2) (Set.Icc (0 : ℝ) 1)
  /-- `g₂(·, Q²)` is integrable on the physical support at every scale. -/
  integrableOn_g2 : ∀ Q2,
    MeasureTheory.IntegrableOn (fun x : ℝ => G.g2 x Q2) (Set.Icc (0 : ℝ) 1)

/-- The physical half of a full assumption bundle. -/
lemma Assumptions.hasPhysicalSupport {G : StructureFunctions} (h : Assumptions G) :
    HasPhysicalSupport G :=
  { support_g1 := h.support_g1, support_g2 := h.support_g2 }

/-- The analytic half of a full assumption bundle. -/
lemma Assumptions.regularity {G : StructureFunctions} (h : Assumptions G) : Regularity G :=
  { measurable_g1 := h.measurable_g1
    measurable_g2 := h.measurable_g2
    integrableOn_g1 := h.integrableOn_g1
    integrableOn_g2 := h.integrableOn_g2 }

/-- The split is exact: `Assumptions` is the conjunction of the physical and the analytic
half, with no residue. -/
lemma assumptions_iff {G : StructureFunctions} :
    Assumptions G ↔ HasPhysicalSupport G ∧ Regularity G :=
  ⟨fun h => ⟨h.hasPhysicalSupport, h.regularity⟩, fun h =>
    { support_g1 := h.1.support_g1
      support_g2 := h.1.support_g2
      measurable_g1 := h.2.measurable_g1
      measurable_g2 := h.2.measurable_g2
      integrableOn_g1 := h.2.integrableOn_g1
      integrableOn_g2 := h.2.integrableOn_g2 }⟩

/-- The first moment `Γ₁(Q²) = ∫₀¹ dx g₁(x, Q²)`.

Convention: this is the moment with weight `x⁰`, i.e. the plain integral of `g₁` over the
physical support. It is what the Bjorken and Ellis-Jaffe sum rules constrain. Note the
index offset relative to `Physlib.Particles.Parton.PDF.mellinMoment`, where
`mellinMoment f n` is `∫₀¹ dx xⁿ f`, and relative to the literature, which usually writes
the `n`-th moment as `∫₀¹ dx xⁿ⁻¹ g`; on both of those scales `firstMomentG1` is `n = 0`
and `n = 1` respectively. -/
def firstMomentG1 (G : StructureFunctions) (Q2 : ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, G.g1 x Q2

/-- The first moment `Γ₂(Q²) = ∫₀¹ dx g₂(x, Q²)`.

Same weight convention as `firstMomentG1`: weight `x⁰`, no `xⁿ⁻¹` offset. This is the
quantity the Burkhardt-Cottingham sum rule asserts to vanish. -/
def firstMomentG2 (G : StructureFunctions) (Q2 : ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, G.g2 x Q2

/-- Assumptions for a polarized hadronic tensor interface. -/
structure TensorAssumptions (A : Bilin V) : Prop where
  antisymm : ∀ v w : V, A v w = -A w v

/-! ### `TensorAssumptions` is antisymmetry, and antisymmetry is `IsAlt`

`TensorAssumptions` had no consumer anywhere in the repository when this lane started: no
bridge produced one and no declaration took one. It is connected here rather than deleted,
because the physics content — that the polarized hadronic tensor is antisymmetric — is worth
naming, and because the connection is what shows the bundle is not a physics postulate at
all: over `ℝ` it is exactly Mathlib's `LinearMap.BilinForm.IsAlt`, an algebraic condition
with a standard consequence.
-/

/-- An antisymmetric bilinear form has vanishing diagonal. Over `ℝ` this needs no further
hypothesis, since `a = -a` forces `a = 0`. -/
lemma TensorAssumptions.apply_self_eq_zero {W : Type} [AddCommGroup W] [Module ℝ W]
    {A : Bilin W} (h : TensorAssumptions W A) (v : W) : A v v = 0 := by
  have hv := h.antisymm v v
  linarith

/-- `TensorAssumptions` is Mathlib's `LinearMap.BilinForm.IsAlt` spelled out: the DIS
interface adds nothing to the algebraic notion. -/
lemma tensorAssumptions_iff_isAlt {W : Type} [AddCommGroup W] [Module ℝ W]
    {A : Bilin W} : TensorAssumptions W A ↔ A.IsAlt := by
  constructor
  · intro h v
    exact h.apply_self_eq_zero v
  · intro h
    exact ⟨fun v w => (LinearMap.BilinForm.IsAlt.neg_eq h w v).symm⟩

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
