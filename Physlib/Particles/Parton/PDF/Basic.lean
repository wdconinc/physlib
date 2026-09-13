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

/-- Structural assumptions for a collinear PDF object. -/
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
