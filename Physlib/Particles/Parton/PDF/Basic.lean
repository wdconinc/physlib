/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# Collinear PDF Object Model

This module introduces first-class collinear PDF objects with explicit assumptions,
sum-rule interfaces, and Mellin-moment hooks.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace Particles
namespace Parton
namespace PDF

variable {Flavor : Type}

/-- A collinear PDF family with flavor index `i`, Bjorken variable `x`, and scale `Q2`. -/
abbrev Pdf (Flavor : Type) : Type := Flavor → ℝ → ℝ → ℝ

/-- The Mellin moment used by evolution and sum-rule interfaces. -/
def mellinMoment (f : Pdf Flavor) (n : ℕ) (i : Flavor) (Q2 : ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, x ^ n * f i x Q2

/-- Structural assumptions for a collinear PDF object.

The `nonneg` field is derivable, not fundamental. Positivity of a leading-twist parton density
is a consequence of positive semidefiniteness of the parton spin-density matrix, and for any
density built through that route it is a theorem: see `PDF.pdfOfSpinDensity_nonneg` and
`PDF.assumptions_pdfOfSpinDensity` in `Physlib/Particles/Parton/PDF/Positivity.lean`, where the
remaining three fields are exactly what has to be supplied. The field is kept here so that
existing users of `Assumptions` are unaffected. -/
structure Assumptions (f : Pdf Flavor) : Prop where
  support : ∀ i x Q2, x < 0 ∨ 1 < x → f i x Q2 = 0
  nonneg : ∀ i x Q2, 0 ≤ x → x ≤ 1 → 0 ≤ f i x Q2
  measurable : ∀ i Q2, MeasureTheory.AEStronglyMeasurable (fun x : ℝ => f i x Q2)
  momentIntegrable : ∀ n i Q2, MeasureTheory.Integrable (fun x : ℝ => x ^ n * f i x Q2)

/-- Outside the physical support domain, the PDF vanishes. -/
lemma eq_zero_of_not_mem_unitInterval
    (f : Pdf Flavor) (h : Assumptions f) (i : Flavor) (x Q2 : ℝ)
    (hx : x < 0 ∨ 1 < x) :
    f i x Q2 = 0 :=
  h.support i x Q2 hx

/-- On the unit interval, the PDF is nonnegative. -/
lemma nonneg_on_unitInterval
    (f : Pdf Flavor) (h : Assumptions f) (i : Flavor) (x Q2 : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ f i x Q2 :=
  h.nonneg i x Q2 hx0 hx1

/-- Integrability of Mellin-moment integrands provided by structural assumptions. -/
lemma mellinMoment_integrable
    (f : Pdf Flavor) (h : Assumptions f) (n : ℕ) (i : Flavor) (Q2 : ℝ) :
  MeasureTheory.Integrable (fun x : ℝ => x ^ n * f i x Q2) :=
  h.momentIntegrable n i Q2

/-! ### The analytic/physical split of `Assumptions`

`Assumptions` bundles two kinds of hypothesis, and the difference decides what can be
discharged and what cannot.

* `IsPartonDensity` is the **physical** half: the momentum fraction lies in `[0, 1]` and the
  density is nonnegative there. This is not a gap in the development. It is what the words
  "parton density" mean, and there is no formulation in which it becomes a theorem about an
  arbitrary function `Flavor → ℝ → ℝ → ℝ`; a concrete model either has the property or is
  not a parton density. (For a density built from a spin-density matrix the `nonneg` clause
  *is* a theorem — `Physlib.Particles.Parton.PDF.pdfOfSpinDensity_nonneg` — but that is a
  statement about that construction, not about `Pdf` in general.)
* `Regularity` is the **analytic** half: measurability in the momentum fraction and
  integrability of the Mellin-moment integrands. These are genuine obligations, and
  `Physlib.Particles.Parton.PDF.Model` discharges them for an explicit model.

`assumptions_iff` records that the split is exact: the bundle is the conjunction of the two
halves and nothing else. `Assumptions` itself is left in place with its field set unchanged,
because modules outside this one take it as a hypothesis.
-/

/-- **What it means to be a collinear parton density**: support in the physical range of the
momentum fraction, and nonnegativity there. A definition, not a theorem. -/
structure IsPartonDensity (f : Pdf Flavor) : Prop where
  /-- The density vanishes outside `[0, 1]`. -/
  support : ∀ i x Q2, x < 0 ∨ 1 < x → f i x Q2 = 0
  /-- The density is nonnegative on `[0, 1]`. -/
  nonneg : ∀ i x Q2, 0 ≤ x → x ≤ 1 → 0 ≤ f i x Q2

/-- **The analytic half of `Assumptions`**: measurability and moment integrability. Unlike
`IsPartonDensity` these are obligations that a concrete model discharges. -/
structure Regularity (f : Pdf Flavor) : Prop where
  /-- `f i · Q2` is almost-everywhere strongly measurable. -/
  measurable : ∀ i Q2, MeasureTheory.AEStronglyMeasurable (fun x : ℝ => f i x Q2)
  /-- Every Mellin-moment integrand of `f` is integrable. -/
  momentIntegrable : ∀ n i Q2, MeasureTheory.Integrable (fun x : ℝ => x ^ n * f i x Q2)

/-- The physical half of a full assumption bundle. -/
lemma Assumptions.isPartonDensity {f : Pdf Flavor} (h : Assumptions f) :
    IsPartonDensity f :=
  { support := h.support, nonneg := h.nonneg }

/-- The analytic half of a full assumption bundle. -/
lemma Assumptions.regularity {f : Pdf Flavor} (h : Assumptions f) : Regularity f :=
  { measurable := h.measurable, momentIntegrable := h.momentIntegrable }

/-- The split is exact: `Assumptions` is the conjunction of the physical and the analytic
half, with no residue. -/
lemma assumptions_iff {f : Pdf Flavor} :
    Assumptions f ↔ IsPartonDensity f ∧ Regularity f :=
  ⟨fun h => ⟨h.isPartonDensity, h.regularity⟩, fun h =>
    { support := h.1.support
      nonneg := h.1.nonneg
      measurable := h.2.measurable
      momentIntegrable := h.2.momentIntegrable }⟩

/-- Sum-rule assumptions used by the PDF interfaces. -/
structure SumRuleAssumptions [Fintype Flavor] (f : Pdf Flavor) : Type where
  momentum : ∀ Q2, (∑ i, mellinMoment f 1 i Q2) = 1
  valenceTarget : Flavor → ℝ
  valence : ∀ i Q2, mellinMoment f 0 i Q2 = valenceTarget i

/-- Momentum sum-rule interface theorem. -/
lemma momentum_sumRule [Fintype Flavor]
    (f : Pdf Flavor) (h : SumRuleAssumptions f) (Q2 : ℝ) :
    (∑ i, mellinMoment f 1 i Q2) = 1 :=
  h.momentum Q2

/-- Valence sum-rule interface theorem. -/
lemma valence_sumRule [Fintype Flavor]
    (f : Pdf Flavor) (h : SumRuleAssumptions f) (i : Flavor) (Q2 : ℝ) :
    mellinMoment f 0 i Q2 = h.valenceTarget i :=
  h.valence i Q2

end PDF
end Parton
end Particles
end Physlib
