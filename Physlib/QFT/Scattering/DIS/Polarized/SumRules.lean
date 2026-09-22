/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Polarized.Basic
public import Physlib.Meta.Linters.Sorry
/-!

# Polarized Sum Rules

## i. Overview

This module states the polarized DIS sum rules as what they are: identities for the first
moments `Γ₁(Q²) = ∫₀¹ dx g₁(x, Q²)` and `Γ₂(Q²) = ∫₀¹ dx g₂(x, Q²)`.

**Moment convention.** `firstMomentG1` and `firstMomentG2` carry weight `x⁰`: they are
plain integrals over `[0, 1]`. In terms of `Physlib.Particles.Parton.PDF.mellinMoment`,
where `mellinMoment f n = ∫₀¹ dx xⁿ f`, that is `n = 0`. In terms of the literature's
`n`-th moment `∫₀¹ dx xⁿ⁻¹ g`, it is `n = 1`. Every statement below uses the weight-`x⁰`
convention and no other.

## ii. Key results

- `BjorkenSumRule` — the proton-neutron non-singlet identity, with the nucleon axial
  charge ratio `g_A/g_V` and the perturbative correction series as explicit inputs rather
  than hard-coded numbers.
- `EllisJaffeSumRule` — the proton-only statement. It is *conditional* on a vanishing
  strange-quark polarization, and that hypothesis is an explicit field, because the sum
  rule is violated experimentally: stating it unconditionally would formalize a falsehood
  about the physical proton.
- `BurkhardtCottingham` — `Γ₂(Q²) = 0`.
- `g2WW`, `wandzuraWilczek` — the twist-2 Wandzura-Wilczek expression for `g₂` in terms of
  `g₁`, together with `burkhardtCottingham_wandzuraWilczek`: the Wandzura-Wilczek `g₂`
  satisfies the Burkhardt-Cottingham sum rule, by a Fubini argument on the triangle
  `0 ≤ x < y ≤ 1`. That step, `integral_tail_swap`, is now proved (grex, Lean 4.33.0), so
  the sum rule no longer rests on any `sorry`. It remains conditional on the hypotheses
  bundled in `WandzuraWilczekAssumptions` — in particular `prod_integrable`, the
  product-measure integrability that Fubini needs and that genuinely does not follow from
  the two one-dimensional integrability fields. That is the usual conditional-on-stated-
  assumptions posture of this development, not an unproved step.

## iii. Table of contents

- A. Bjorken sum rule
- B. Ellis-Jaffe sum rule
- C. Burkhardt-Cottingham sum rule
- D. Wandzura-Wilczek relation
- E. An explicit structure-function pair
- F. Remaining targets, not yet formalized here

## References

- J. D. Bjorken, Phys. Rev. **148** (1966) 1467.
- J. Ellis and R. L. Jaffe, Phys. Rev. D **9** (1974) 1444.
- H. Burkhardt and W. N. Cottingham, Ann. Phys. **56** (1970) 453.
- S. Wandzura and F. Wilczek, Phys. Lett. B **72** (1977) 195.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Polarized

/-! ## A. Bjorken sum rule -/

/-- The Bjorken sum rule for a proton/neutron pair of polarized structure functions.

`Γ₁ᵖ(Q²) − Γ₁ⁿ(Q²) = (1/6) |g_A/g_V| (1 + Δ(Q²))`, an identity for the non-singlet
combination of first moments, tied to the nucleon axial charge.

Both `gAOverGV` and the perturbative correction `correction` are inputs rather than
derived quantities. `gAOverGV` is a nucleon matrix element that this repository does not
yet formalize (see the note at the end of the module); `correction` is the QCD radiative
series, which is scheme- and order-dependent, so it is kept an abstract function of `Q²`
rather than a hard-coded expansion. -/
structure BjorkenSumRule (Gp Gn : StructureFunctions) (gAOverGV : ℝ)
    (correction : ℝ → ℝ) : Prop where
  /-- The non-singlet first-moment identity, at every scale. -/
  bjorken : ∀ Q2, firstMomentG1 Gp Q2 - firstMomentG1 Gn Q2
    = (1 / 6) * |gAOverGV| * (1 + correction Q2)

/-- The experimental use of the Bjorken sum rule: it determines `|g_A/g_V|` from the
measured non-singlet first moment, once the perturbative correction is known.

This is an inversion of the sum rule, not a restatement of it. -/
lemma abs_gAOverGV_eq_of_bjorken
    (Gp Gn : StructureFunctions) (gAOverGV : ℝ) (correction : ℝ → ℝ)
    (hB : BjorkenSumRule Gp Gn gAOverGV correction)
    (Q2 : ℝ) (hCorr : 1 + correction Q2 ≠ 0) :
    |gAOverGV|
      = 6 * (firstMomentG1 Gp Q2 - firstMomentG1 Gn Q2) / (1 + correction Q2) := by
  have h := hB.bjorken Q2
  rw [eq_div_iff hCorr, h]
  ring

/-! ## B. Ellis-Jaffe sum rule -/

/-- The Ellis-Jaffe sum rule for the proton.

Unlike the Bjorken sum rule this is *not* a consequence of current algebra alone: it needs
the extra hypothesis that the strange-quark polarization vanishes. That hypothesis is the
field `strange_unpolarized`, and it is what the measurement of `Γ₁ᵖ` falsified — the
"proton spin problem". Formalizing the conclusion without carrying the hypothesis would
state something false about the physical proton.

The structure therefore carries the leading-twist flavour decomposition of the first
moment as a separate field, so that `strange_unpolarized` is a hypothesis that does real
work on it, rather than a free-floating equation about an unconstrained function.

`deltaU`, `deltaD`, `deltaS` are the scale-dependent quark helicity charges
`Δq(Q²) = ∫₀¹ dx [Δq(x, Q²) + Δq̄(x, Q²)]`, and the quark charge weights are
`e_u² = 4/9`, `e_d² = e_s² = 1/9`. -/
structure EllisJaffeSumRule (Gp : StructureFunctions)
    (deltaU deltaD deltaS : ℝ → ℝ) (correction : ℝ → ℝ) : Prop where
  /-- Leading-twist quark-parton decomposition of the proton first moment,
  `Γ₁ᵖ = ½ Σ_q e_q² Δq`, dressed by the perturbative correction. -/
  moment_decomposition : ∀ Q2,
    firstMomentG1 Gp Q2
      = (1 / 2) * ((4 / 9) * deltaU Q2 + (1 / 9) * deltaD Q2 + (1 / 9) * deltaS Q2)
        * (1 + correction Q2)
  /-- The SU(3)-symmetric hypothesis of a vanishing strange-quark polarization. This is
  the assumption that experiment rejects. -/
  strange_unpolarized : ∀ Q2, deltaS Q2 = 0

/-- The Ellis-Jaffe prediction: under a vanishing strange polarization, the proton first
moment is fixed by the up and down helicity charges alone.

`Γ₁ᵖ(Q²) = (1/18) (4 Δu(Q²) + Δd(Q²)) (1 + Δ(Q²))`. -/
lemma ellisJaffe_prediction
    (Gp : StructureFunctions) (deltaU deltaD deltaS correction : ℝ → ℝ)
    (hEJ : EllisJaffeSumRule Gp deltaU deltaD deltaS correction)
    (Q2 : ℝ) :
    firstMomentG1 Gp Q2
      = (1 / 18) * (4 * deltaU Q2 + deltaD Q2) * (1 + correction Q2) := by
  rw [hEJ.moment_decomposition Q2, hEJ.strange_unpolarized Q2]
  ring

/-! ## C. Burkhardt-Cottingham sum rule -/

/-- The Burkhardt-Cottingham sum rule, `∫₀¹ dx g₂(x, Q²) = 0` at every scale.

It follows from the analytic structure of the forward virtual Compton amplitude rather
than from the parton model, so at this level it is a hypothesis; `g2WW` below gives a
family of structure functions that provably satisfies it. -/
structure BurkhardtCottingham (G : StructureFunctions) : Prop where
  /-- The vanishing of the first moment of `g₂`, at every scale. -/
  bc : ∀ Q2, firstMomentG2 G Q2 = 0

/-! ## D. Wandzura-Wilczek relation -/

/-- The Wandzura-Wilczek (twist-2) expression for `g₂` in terms of `g₁`:

`g₂^WW(x, Q²) = −g₁(x, Q²) + ∫_x¹ (dy / y) g₁(y, Q²)`.

The tail integral is taken over `Set.Ioc x 1`; the half-open interval is the natural one
for the triangle decomposition `0 ≤ x < y ≤ 1` used below, and differs from `Set.Icc x 1`
by a null set, so the value is unchanged. -/
def g2WW (G : StructureFunctions) (x Q2 : ℝ) : ℝ :=
  -G.g1 x Q2 + ∫ y in Set.Ioc x 1, G.g1 y Q2 / y

/-- The Wandzura-Wilczek structure-function pair built from a given `g₁`: the same `g₁`,
and `g₂` replaced by its twist-2 Wandzura-Wilczek expression. -/
def wandzuraWilczek (G : StructureFunctions) : StructureFunctions where
  g1 := G.g1
  g2 := g2WW G

/-- Integrability hypotheses needed to evaluate the Wandzura-Wilczek first moment at a
fixed scale `Q²`.

These are collected here rather than assumed inline at each use, per the repository
convention for definitions that integrate. Only `g₁` appears: `g₂^WW` is built from it. -/
structure WandzuraWilczekAssumptions (G : StructureFunctions) (Q2 : ℝ) : Prop where
  /-- `g₁(·, Q²)` is integrable on the physical support `[0, 1]`. -/
  g1_integrableOn :
    MeasureTheory.IntegrableOn (fun x : ℝ => G.g1 x Q2) (Set.Icc (0 : ℝ) 1)
  /-- The Wandzura-Wilczek tail `x ↦ ∫_(x,1] dy g₁(y, Q²)/y` is integrable on `[0, 1]`. -/
  tail_integrableOn :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => ∫ y in Set.Ioc x 1, G.g1 y Q2 / y) (Set.Icc (0 : ℝ) 1)
  /-- The integrand of the double integral is integrable for the product measure on
  `[0, 1] × [0, 1]`. This is exactly the hypothesis that licenses the Fubini swap
  `∫₀¹ dx ∫_x¹ dy = ∫₀¹ dy ∫₀^y dx`; it is not derivable from the two one-dimensional
  integrability statements above. -/
  prod_integrable :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => if p.1 < p.2 then G.g1 p.2 Q2 / p.2 else 0)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)).prod
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))

/-- Fubini on the triangle `{(x, y) : 0 ≤ x ≤ 1, x < y ≤ 1}`: integrating the
Wandzura-Wilczek tail over `x ∈ [0, 1]` and swapping the order of integration replaces the
inner `x`-integral by the length `y` of `[0, y)`. -/
lemma integral_tail_swap
    (G : StructureFunctions) (Q2 : ℝ)
    (hWW : WandzuraWilczekAssumptions G Q2) :
    (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Ioc x 1, G.g1 y Q2 / y)
      = ∫ y in Set.Icc (0 : ℝ) 1, G.g1 y Q2 / y * y := by
  have hIcc : MeasurableSet (Set.Icc (0 : ℝ) 1) := measurableSet_Icc
  -- (1) For `0 ≤ x` the tail `Ioc x 1` is exactly the part of `Icc 0 1` above `x`, so the
  -- inner integral can be taken over the *fixed* set `Icc 0 1` against an `if`. That is
  -- what makes the product measure in `prod_integrable` the right one for Fubini.
  have step1 : Set.EqOn
      (fun x : ℝ => ∫ y in Set.Ioc x 1, G.g1 y Q2 / y)
      (fun x : ℝ => ∫ y in Set.Icc (0 : ℝ) 1, (if x < y then G.g1 y Q2 / y else 0))
      (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    have hmeas : MeasurableSet {y : ℝ | x < y} :=
      measurableSet_lt measurable_const measurable_id
    have hset : Set.Icc (0 : ℝ) 1 ∩ {y : ℝ | x < y} = Set.Ioc x 1 := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_Ioc]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hx.1.trans h.1.le, h.2⟩, h.1⟩⟩
    show (∫ y in Set.Ioc x 1, G.g1 y Q2 / y)
        = ∫ y in Set.Icc (0 : ℝ) 1, (if x < y then G.g1 y Q2 / y else 0)
    rw [← hset, ← MeasureTheory.setIntegral_indicator hmeas]
    exact MeasureTheory.setIntegral_congr_fun hIcc fun y _ => by
      by_cases h : x < y <;> simp [Set.indicator_apply, h]
  rw [MeasureTheory.setIntegral_congr_fun hIcc step1]
  -- (2) Fubini on the product of the two restricted measures.
  rw [MeasureTheory.integral_integral_swap hWW.prod_integrable]
  -- (3) The inner `x`-integral is a constant over `Ico 0 y`, whose length is `y`.
  refine MeasureTheory.setIntegral_congr_fun hIcc fun y hy => ?_
  have hmeas2 : MeasurableSet {x : ℝ | x < y} :=
    measurableSet_lt measurable_id measurable_const
  have hset2 : Set.Icc (0 : ℝ) 1 ∩ {x : ℝ | x < y} = Set.Ico 0 y := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_Ico]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.le.trans hy.2⟩, h.2⟩⟩
  show (∫ x in Set.Icc (0 : ℝ) 1, (if x < y then G.g1 y Q2 / y else 0))
      = G.g1 y Q2 / y * y
  have hind : (∫ x in Set.Icc (0 : ℝ) 1, (if x < y then G.g1 y Q2 / y else 0))
      = ∫ _x in Set.Icc (0 : ℝ) 1 ∩ {x : ℝ | x < y}, G.g1 y Q2 / y := by
    rw [← MeasureTheory.setIntegral_indicator hmeas2]
    exact MeasureTheory.setIntegral_congr_fun hIcc fun x _ => by
      by_cases h : x < y <;> simp [Set.indicator_apply, h]
  rw [hind, hset2, MeasureTheory.setIntegral_const,
    Real.volume_real_Ico_of_le hy.1, sub_zero, smul_eq_mul, mul_comm]

/-- Integrating the Wandzura-Wilczek tail over `[0, 1]` returns the first moment of `g₁`,
`∫₀¹ dx ∫_x¹ (dy/y) g₁(y) = ∫₀¹ dy g₁(y)`.

The swap of `integral_tail_swap` produces a factor `y` which cancels the `1/y`, almost
everywhere on `[0, 1]` — the exceptional point `y = 0` is null. Stated with the integral
written out rather than as `firstMomentG1 G Q2` so that it rewrites without unfolding a
definition. -/
lemma integral_tail_eq_integral_g1
    (G : StructureFunctions) (Q2 : ℝ)
    (hWW : WandzuraWilczekAssumptions G Q2) :
    (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Ioc x 1, G.g1 y Q2 / y)
      = ∫ y in Set.Icc (0 : ℝ) 1, G.g1 y Q2 := by
  rw [integral_tail_swap G Q2 hWW]
  refine MeasureTheory.integral_congr_ae ?_
  have hne :
      ∀ᵐ y : ℝ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)), y ≠ 0 := by
    refine MeasureTheory.ae_restrict_of_ae ?_
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne] with y hy
  field_simp

/-- **The Wandzura-Wilczek `g₂` satisfies the Burkhardt-Cottingham sum rule.**

`∫₀¹ dx g₂^WW(x, Q²) = 0`. The `−g₁` term contributes `−Γ₁` and the tail term contributes
`+Γ₁`, by `integral_tail_eq_integral_g1`. -/
theorem firstMoment_g2WW_eq_zero
    (G : StructureFunctions) (Q2 : ℝ)
    (hWW : WandzuraWilczekAssumptions G Q2) :
    (∫ x in Set.Icc (0 : ℝ) 1, g2WW G x Q2) = 0 := by
  have hneg :
      MeasureTheory.IntegrableOn (fun x : ℝ => -G.g1 x Q2) (Set.Icc (0 : ℝ) 1) :=
    hWW.g1_integrableOn.neg
  calc (∫ x in Set.Icc (0 : ℝ) 1, g2WW G x Q2)
      = ∫ x in Set.Icc (0 : ℝ) 1,
          (-G.g1 x Q2 + ∫ y in Set.Ioc x 1, G.g1 y Q2 / y) := rfl
    _ = (∫ x in Set.Icc (0 : ℝ) 1, -G.g1 x Q2)
          + ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Ioc x 1, G.g1 y Q2 / y :=
        MeasureTheory.integral_add hneg hWW.tail_integrableOn
    _ = -(∫ x in Set.Icc (0 : ℝ) 1, G.g1 x Q2)
          + ∫ y in Set.Icc (0 : ℝ) 1, G.g1 y Q2 := by
        rw [MeasureTheory.integral_neg, integral_tail_eq_integral_g1 G Q2 hWW]
    _ = 0 := by ring

/-- The Wandzura-Wilczek structure-function pair satisfies the Burkhardt-Cottingham sum
rule at every scale for which the integrability hypotheses hold. -/
theorem burkhardtCottingham_wandzuraWilczek
    (G : StructureFunctions)
    (hWW : ∀ Q2, WandzuraWilczekAssumptions G Q2) :
    BurkhardtCottingham (wandzuraWilczek G) := by
  refine ⟨fun Q2 => ?_⟩
  have h := firstMoment_g2WW_eq_zero G Q2 (hWW Q2)
  simpa [firstMomentG2, wandzuraWilczek] using h

/-! ## E. An explicit structure-function pair

`WandzuraWilczekAssumptions` had no instance. Every result above is conditional on it, and
in particular `burkhardtCottingham_wandzuraWilczek` is conditional on `prod_integrable`, a
product-measure hypothesis that nothing in the repository discharged. The pair below
discharges all three fields, at every scale, so the Burkhardt-Cottingham sum rule for the
Wandzura-Wilczek `g₂` becomes an unconditional theorem about a concrete object
(`burkhardtCottingham_modelStructureFunctions`).

The model is the simplest one whose tail integral has a closed form: `g₁(x, Q²) = x` on
`[0, 1]` and `0` outside, at every scale. Then `g₁(y)/y` is the indicator of `(0, 1]` — the
point `y = 0` included, where `g₁(0) = 0` and the junk value of `0/0` is `0` — so the
Wandzura-Wilczek tail is `1 - max x 0`. That single computation, `integral_tail_modelG1`, is
what the three discharges rest on.

It also settles a question about `g2WW` that the definition leaves open:
`g2WW_modelStructureFunctions_of_neg` shows the Wandzura-Wilczek `g₂` is *not* supported in
`[0, 1]` even when `g₁` is. See the docstring there.
-/

/-- The explicit `g₁` used below: `x` on the physical support, `0` outside, at every
scale. -/
def modelG1 : ℝ → ℝ → ℝ := fun x _ => Set.indicator (Set.Icc (0 : ℝ) 1) id x

/-- An explicit polarized structure-function pair, with `g₂ = 0`. Only `g₁` enters
`WandzuraWilczekAssumptions`; the twist-2 `g₂` built from this `g₁` is
`g2WW modelStructureFunctions`. -/
def modelStructureFunctions : StructureFunctions where
  g1 := modelG1
  g2 := fun _ _ => 0

/-- The Wandzura-Wilczek integrand of the model is the indicator of `(0, 1]`. -/
lemma modelG1_div_eq_indicator (Q2 : ℝ) :
    (fun y : ℝ => modelStructureFunctions.g1 y Q2 / y)
      = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) := by
  funext y
  show Set.indicator (Set.Icc (0 : ℝ) 1) id y / y
      = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) y
  by_cases hy : y ∈ Set.Ioc (0 : ℝ) 1
  · have hmem : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    have hy0 : y ≠ 0 := hy.1.ne'
    simp [Set.indicator_apply, hy, hmem, div_self hy0]
  · rcases lt_trichotomy y 0 with h | h | h
    · have hIcc : y ∉ Set.Icc (0 : ℝ) 1 := fun hm => absurd hm.1 (not_le.mpr h)
      simp [Set.indicator_apply, hy, hIcc]
    · simp [Set.indicator_apply, hy, h]
    · have hIcc : y ∉ Set.Icc (0 : ℝ) 1 := fun hm => hy ⟨h, hm.2⟩
      simp [Set.indicator_apply, hy, hIcc]

/-- The Wandzura-Wilczek tail of the model in closed form:
`∫_(x,1] dy g₁(y, Q²)/y = 1 - max x 0` for every `x ≤ 1`. -/
lemma integral_tail_modelG1 (Q2 : ℝ) {x : ℝ} (hx : x ≤ 1) :
    (∫ y in Set.Ioc x 1, modelStructureFunctions.g1 y Q2 / y) = 1 - max x 0 := by
  have hmax : max x 0 ≤ 1 := max_le hx zero_le_one
  rw [modelG1_div_eq_indicator Q2,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc, Set.Ioc_inter_Ioc]
  simp only [min_self]
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hmax, smul_eq_mul, mul_one]

/-- The model `g₁` is globally integrable: it is an indicator of a compact interval carrying
a continuous function. -/
lemma integrable_modelG1 (Q2 : ℝ) :
    MeasureTheory.Integrable (fun x : ℝ => modelStructureFunctions.g1 x Q2) := by
  show MeasureTheory.Integrable (Set.indicator (Set.Icc (0 : ℝ) 1) id)
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
    continuous_id.integrableOn_Icc

/-- **All three fields of `WandzuraWilczekAssumptions` hold for the model**, at every scale.
`prod_integrable` is the one that matters: the integrand is bounded by `1` and both factors
of the product measure are finite, so Fubini applies with no further hypothesis. -/
lemma wandzuraWilczekAssumptions_modelStructureFunctions (Q2 : ℝ) :
    WandzuraWilczekAssumptions modelStructureFunctions Q2 := by
  haveI hfin : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  have hmeasF : Measurable (fun y : ℝ => modelStructureFunctions.g1 y Q2 / y) := by
    rw [modelG1_div_eq_indicator Q2]
    exact measurable_const.indicator measurableSet_Ioc
  have hifeq : (fun p : ℝ × ℝ =>
        if p.1 < p.2 then modelStructureFunctions.g1 p.2 Q2 / p.2 else 0)
      = Set.indicator {p : ℝ × ℝ | p.1 < p.2}
          (fun p : ℝ × ℝ => modelStructureFunctions.g1 p.2 Q2 / p.2) := by
    funext p
    by_cases h : p.1 < p.2
    · simp [Set.indicator_apply, h]
    · simp [Set.indicator_apply, h]
  have hprodmeas : Measurable (fun p : ℝ × ℝ =>
      if p.1 < p.2 then modelStructureFunctions.g1 p.2 Q2 / p.2 else 0) := by
    rw [hifeq]
    exact (hmeasF.comp measurable_snd).indicator
      (measurableSet_lt measurable_fst measurable_snd)
  have hbound : ∀ p : ℝ × ℝ,
      ‖(if p.1 < p.2 then modelStructureFunctions.g1 p.2 Q2 / p.2 else 0)‖ ≤ 1 := by
    intro p
    have hval : modelStructureFunctions.g1 p.2 Q2 / p.2
        = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) p.2 :=
      congrFun (modelG1_div_eq_indicator Q2) p.2
    by_cases h : p.1 < p.2
    · rw [if_pos h, hval]
      by_cases hm : p.2 ∈ Set.Ioc (0 : ℝ) 1
      · simp [Set.indicator_apply, hm]
      · simp [Set.indicator_apply, hm]
    · rw [if_neg h]
      simp
  refine ⟨(integrable_modelG1 Q2).integrableOn, ?_, ?_⟩
  · have hcont : Continuous (fun x : ℝ => 1 - max x 0) :=
      continuous_const.sub (continuous_id.max continuous_const)
    refine hcont.integrableOn_Icc.congr_fun ?_ measurableSet_Icc
    intro x hx
    exact (integral_tail_modelG1 Q2 hx.2).symm
  · exact MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
      hprodmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

/-- **The Burkhardt-Cottingham sum rule, unconditionally, for an explicit pair.**
`∫₀¹ dx g₂^WW(x, Q²) = 0` at every scale for the Wandzura-Wilczek `g₂` built from `modelG1`,
with every field of `WandzuraWilczekAssumptions` discharged rather than assumed. -/
theorem burkhardtCottingham_modelStructureFunctions :
    BurkhardtCottingham (wandzuraWilczek modelStructureFunctions) :=
  burkhardtCottingham_wandzuraWilczek modelStructureFunctions
    wandzuraWilczekAssumptions_modelStructureFunctions

/-- The model pair satisfies `Polarized.Assumptions`, which had no instance anywhere in the
repository. This is a satisfiability witness for that bundle, nothing more. -/
lemma assumptions_modelStructureFunctions : Assumptions modelStructureFunctions := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x Q2 hx
    have hIcc : x ∉ Set.Icc (0 : ℝ) 1 := by
      rcases hx with h | h
      · exact fun hm => absurd hm.1 (not_le.mpr h)
      · exact fun hm => absurd hm.2 (not_le.mpr h)
    show Set.indicator (Set.Icc (0 : ℝ) 1) id x = 0
    simp [Set.indicator_apply, hIcc]
  · intro x Q2 _
    rfl
  · intro Q2
    exact (measurable_id.indicator measurableSet_Icc).aestronglyMeasurable
  · intro Q2
    exact MeasureTheory.aestronglyMeasurable_const
  · intro Q2
    exact (integrable_modelG1 Q2).integrableOn
  · intro Q2
    exact MeasureTheory.integrableOn_zero

/-- **`g2WW` is not supported in the physical interval, even when `g₁` is.** For the model,
`g₂^WW(x, Q²) = 1` at every `x < 0`: the tail `∫_(x,1] dy g₁(y, Q²)/y` does not know that `x`
is unphysical, and `−g₁(x)` vanishes there, so nothing cancels it.

No sum rule above is affected — every moment here is an integral over `[0, 1]`, where the
expression is the Wandzura-Wilczek relation of the literature. What it does mean is that
`wandzuraWilczek G` must not be assumed to satisfy `Polarized.HasPhysicalSupport`, and hence
not `Polarized.Assumptions` either, however well `G` itself does: compare
`assumptions_modelStructureFunctions` for the same `g₁`. A `g₂^WW` that vanishes off `[0, 1]`
needs the tail's lower limit clamped at `max x 0`; that is a change to the definition and is
left to whoever needs it, since every consumer here integrates over `[0, 1]` only. -/
lemma g2WW_modelStructureFunctions_of_neg {x : ℝ} (hx : x < 0) (Q2 : ℝ) :
    g2WW modelStructureFunctions x Q2 = 1 := by
  have hx1 : x ≤ 1 := by linarith
  have hg1 : modelStructureFunctions.g1 x Q2 = 0 := by
    have hIcc : x ∉ Set.Icc (0 : ℝ) 1 := fun hm => absurd hm.1 (not_le.mpr hx)
    show Set.indicator (Set.Icc (0 : ℝ) 1) id x = 0
    simp [Set.indicator_apply, hIcc]
  simp only [g2WW]
  rw [hg1, integral_tail_modelG1 Q2 hx1, max_eq_right hx.le]
  ring

/-! ## F. Remaining targets

Two statements in this family are deliberately absent.

- **Sum-rule conservation under evolution.** That the momentum and valence sum rules hold
  at every scale, given that they hold at one and that the DGLAP kernels satisfy
  `Σ_i ∫₀¹ dx x P_ij(x) = 0`, requires the evolution equation to be stated correctly
  first. The current `dglapRhsLogScale` applies `alphaS` without the conventional
  `1/(2π)`; fixing that is the subject of the `task/e2-dglap-wellposedness` branch, and
  this theorem should be added on top of it, not before it.
- **Derivation of the Bjorken sum rule.** `gAOverGV` is a nucleon axial-current matrix
  element. Once the repository formalizes that matrix element, `BjorkenSumRule` becomes
  derivable rather than assumed; until then it stays an input and is documented as
  external.
-/

end Polarized
end DIS
end Scattering
end QFT
end Physlib
