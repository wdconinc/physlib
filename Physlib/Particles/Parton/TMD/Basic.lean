/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.PDF.Basic
/-!

# TMD Object Model

This module introduces transverse-momentum-dependent parton distributions
and their structural assumptions.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace Particles
namespace Parton
namespace TMD

variable {Flavor : Type}

/-- A TMD family `f_i(x,kT,Q2,ζ)`. -/
abbrev Tmd (Flavor : Type) : Type := Flavor → ℝ → ℝ → ℝ → ℝ → ℝ

/-- Structural assumptions for TMD objects. -/
structure Assumptions (f : Tmd Flavor) : Prop where
  supportX : ∀ i x kT Q2 ζ, x < 0 ∨ 1 < x → f i x kT Q2 ζ = 0
  supportKT : ∀ i x kT Q2 ζ, kT < 0 → f i x kT Q2 ζ = 0
  nonneg : ∀ i x kT Q2 ζ, 0 ≤ x → x ≤ 1 → 0 ≤ kT → 0 ≤ f i x kT Q2 ζ
  measurableKT : ∀ i x Q2 ζ, MeasureTheory.AEStronglyMeasurable (fun kT : ℝ => f i x kT Q2 ζ)

/-- Truncated **plain** integration in the transverse-momentum magnitude, with no
transverse measure: `∫_0^{ktMax} dk_T f`.

This is *not* the collinear reduction of a TMD, and must not be used as one; the
collinear density integrates the two-dimensional transverse measure, for which see
`integrateTransverse`. The definition is retained because it is the object some
interfaces were written against, and because the plain integral is occasionally the
quantity wanted in its own right. -/
def integrateKT
    (f : Tmd Flavor)
    (i : Flavor) (x Q2 ζ ktMax : ℝ) : ℝ :=
  ∫ kT in Set.Icc (0 : ℝ) ktMax, f i x kT Q2 ζ

/-- Truncated integration against the **transverse measure**,
`∫_{|k_T| ≤ ktMax} d²k_T f = 2π ∫_0^{ktMax} k_T dk_T f`.

The collinear parton density is the TMD integrated over `d²k_T`, so the Jacobian `2π k_T`
is part of the reduction and not a convention: without it, `collinearFromTmd` does not
produce a collinear density, and any quantitative use of the reduction is wrong by a
`k_T`-dependent weight. For an azimuthally symmetric TMD — which is what the type
`Tmd`, carrying only the magnitude `k_T`, presupposes — the azimuthal integral
contributes the factor `2π`. -/
def integrateTransverse
    (f : Tmd Flavor)
    (i : Flavor) (x Q2 ζ ktMax : ℝ) : ℝ :=
  ∫ kT in Set.Icc (0 : ℝ) ktMax, (2 * Real.pi * kT) * f i x kT Q2 ζ

/-- Unfolding lemma for the transverse-measure integral. -/
lemma integrateTransverse_eq_integral
    (f : Tmd Flavor)
    (i : Flavor) (x Q2 ζ ktMax : ℝ) :
    integrateTransverse f i x Q2 ζ ktMax
      = ∫ kT in Set.Icc (0 : ℝ) ktMax, (2 * Real.pi * kT) * f i x kT Q2 ζ :=
  rfl

/-- Support consequence in the Bjorken variable for TMDs. -/
lemma eq_zero_of_not_mem_unitInterval
    (f : Tmd Flavor) (h : Assumptions f)
    (i : Flavor) (x kT Q2 ζ : ℝ)
    (hx : x < 0 ∨ 1 < x) :
    f i x kT Q2 ζ = 0 :=
  h.supportX i x kT Q2 ζ hx

/-- Support consequence in the transverse-momentum variable. -/
lemma eq_zero_of_kT_neg
    (f : Tmd Flavor) (h : Assumptions f)
    (i : Flavor) (x kT Q2 ζ : ℝ)
    (hkT : kT < 0) :
    f i x kT Q2 ζ = 0 :=
  h.supportKT i x kT Q2 ζ hkT

/-- Positivity consequence in the physical region. -/
lemma nonneg_on_physicalRegion
    (f : Tmd Flavor) (h : Assumptions f)
    (i : Flavor) (x kT Q2 ζ : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hkT0 : 0 ≤ kT) :
    0 ≤ f i x kT Q2 ζ :=
  h.nonneg i x kT Q2 ζ hx0 hx1 hkT0

end TMD
end Parton
end Particles
end Physlib
