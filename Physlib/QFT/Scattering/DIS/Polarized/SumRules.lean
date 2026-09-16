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
  `0 ≤ x < y ≤ 1`. That argument's own claim to being "the one genuine theorem in this
  file" does not hold yet: it rests on `integral_tail_swap`, whose Fubini-swap step is
  still `@[sorryful]` below, so the sum rule is proved conditionally on that step, not
  unconditionally.

## iii. Table of contents

- A. Bjorken sum rule
- B. Ellis-Jaffe sum rule
- C. Burkhardt-Cottingham sum rule
- D. Wandzura-Wilczek relation
- E. Remaining targets, not yet formalized here

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
@[sorryful]
lemma integral_tail_swap
    (G : StructureFunctions) (Q2 : ℝ)
    (hWW : WandzuraWilczekAssumptions G Q2) :
    (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Ioc x 1, G.g1 y Q2 / y)
      = ∫ y in Set.Icc (0 : ℝ) 1, G.g1 y Q2 / y * y := by
  -- TODO(task/sum-rules): the Fubini swap itself is not written out. Intended argument,
  -- in three steps.
  -- (1) For `x ∈ Set.Icc 0 1` one has the exact set identity
  --     `Set.Ioc x 1 = {y ∈ Set.Icc 0 1 | x < y}` (`0 ≤ x` and `x < y` force `0 < y`),
  --     so the inner integral equals
  --     `∫ y in Set.Icc (0:ℝ) 1, if x < y then G.g1 y Q2 / y else 0`.
  --     Rewriting under the outer integral needs `MeasureTheory.setIntegral_congr_fun`
  --     (or `integral_congr_ae` on the restricted measure) plus measurability of
  --     `Set.Icc 0 1`.
  -- (2) Apply `MeasureTheory.integral_integral_swap` to
  --     `fun x y => if x < y then G.g1 y Q2 / y else 0` on the product measure
  --     `(volume.restrict (Set.Icc 0 1)).prod (volume.restrict (Set.Icc 0 1))`, with
  --     `hWW.prod_integrable` as the product-integrability hypothesis. Note that
  --     `integral_integral_swap` is stated for `Integrable (Function.uncurry f)`, so the
  --     field may need to be restated in `Function.uncurry` form, or bridged with
  --     `MeasureTheory.integrable_prod_iff`.
  -- (3) Evaluate the resulting inner `x`-integral: for `y ∈ Set.Icc 0 1`,
  --     `∫ x in Set.Icc (0:ℝ) 1, (if x < y then c else 0) = c * y`, since
  --     `{x ∈ Set.Icc 0 1 | x < y} = Set.Ico 0 y` and `Real.volume_Ico` gives
  --     `ENNReal.ofReal (y - 0)`. Expected route: `MeasureTheory.integral_indicator`
  --     (after rewriting the `if` as `Set.indicator`), then
  --     `MeasureTheory.setIntegral_const` and `MeasureTheory.measureReal_restrict_apply`.
  -- Update: all three names above are confirmed present at the pinned mathlib rev
  -- (v4.33.0, packages/mathlib read directly from /opt/lake/builds) --
  -- `MeasureTheory.setIntegral_congr_fun (hs : MeasurableSet s) (h : EqOn f g s)`
  -- (Mathlib/MeasureTheory/Integral/Bochner/Set.lean), `MeasureTheory.integral_integral_swap`
  -- (Mathlib/MeasureTheory/Integral/Prod.lean, takes `Integrable (uncurry f) (μ.prod ν)`
  -- exactly as anticipated), and `measureReal_restrict_apply` (used elsewhere in mathlib
  -- itself, e.g. Integral/Gamma.lean). Confirming the *names* exist is not the same as a
  -- checked proof term -- assembling the three steps still needs a real elaborator, which
  -- remains unavailable here -- so this stays `sorry`/`@[sorryful]` rather than an attempted
  -- proof. The mathematics is standard and the statement is believed correct.
  sorry

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

/-! ## E. Remaining targets

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
