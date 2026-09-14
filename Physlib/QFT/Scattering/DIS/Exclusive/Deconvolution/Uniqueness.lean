/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.Linters.Sorry
public import Physlib.QFT.Scattering.DIS.Exclusive.Deconvolution.Basic
/-!

# GPD Uniqueness from Partial DGLAP Knowledge, and its Coexistence with Shadow GPDs

Two recent results about GPD reconstruction point in opposite directions:

* **Non-uniqueness.** There is an infinite family of shadow GPDs producing identical
  Compton form factors at a fixed order and scale
  (`Deconvolution.hasShadow_of_isLeadingOrderDvcs`, arXiv:2303.12006).
* **Uniqueness up to a D-term.** Knowing a GPD at vanishing and low skewness inside the
  DGLAP region determines it on its whole support up to a D-term
  (`exists_dTerm_of_agreeOnLowSkewnessDglap`, arXiv:2401.12013).

Both are right, and this module is about why. **The two statements take different
inputs.** The first is about what *Compton form factor data at one order and scale*
determines; the second is about what *GPD values in a kinematic region* determine. The
purpose of the module is to make the difference a theorem rather than a remark.

## The reconciliation, in three proved steps

1. `Physlib.Particles.Parton.GPD.gpdOfDTerm_eq_zero_of_inDglapRegion` — a pure D-term
   vanishes identically on the DGLAP region. So the ambiguity left by the uniqueness
   theorem is, by construction, invisible to the data that theorem uses.
2. `not_isShadow_of_eq_gpdOfDTerm` — a shadow GPD is never a pure D-term, provided the
   Compton map is faithful on D-terms (`SeparatesDTerms`). So the ambiguity left by the
   Compton map is *not* of the kind the uniqueness theorem tolerates.
3. `shadow_visible_in_lowSkewness_dglap` — consequently, under the uniqueness statement,
   every shadow GPD is nonzero somewhere in the DGLAP region at accessible skewness.
   A shadow hides from Compton form factors at one order and scale; it does not hide from
   a direct determination of the GPD at low skewness.

Steps 1-3 are proved. The two headline statements they reconcile are not: each is a
tagged `sorry` naming what it needs.

## Why `SeparatesDTerms` is the right hypothesis and not a placeholder

The D-term is the subtraction constant of the fixed-`t` dispersion relation for the DVCS
amplitude (Diehl and Ivanov, arXiv:0712.3533; Polyakov and Schweitzer,
arXiv:1801.05858). Faithfulness of the Compton map on D-terms is therefore a property the
physical map is believed to have, not an arbitrary convenience: it says that the real
part of the form factor fixes the subtraction constant. It is stated as a concrete
implication between quantified equations, not as an opaque `Prop` field.

## Deviation from the source statement

arXiv:2401.12013 reports reconstructions with a maximal skewness as low as 20% of the
longitudinal momentum fraction, i.e. a data region of the shape `|ξ| ≤ c |x|`. The
hypothesis used here, `|ξ| ≤ ξ₀` with `ξ₀ > 0` fixed, is a neighbourhood of vanishing
skewness rather than a cone. The two coincide near `|x| = 1` and the cone is the weaker
assumption at small `|x|`; the choice made here is the one under which the analytic
argument (Radon inversion from a neighbourhood of the `ξ = 0` slice) is stated most
directly. See `NOTES.md` of `task/frontier-open-targets`.

## References

* Y. Guo, X. Ji, M. G. Santiago, J. Yang and H.-C. Zhang (listing; primary source not
  consulted), *Unraveling Generalized Parton Distributions Through Lorentz Symmetry and
  Partial DGLAP Knowledge*, arXiv:2401.12013.
* E. Moffat *et al.*, *Shedding light on shadow generalized parton distributions*,
  Phys. Rev. D **108** (2023) 036027 (arXiv:2303.12006).
* M. Diehl and D. Yu. Ivanov, *Dispersion representations for hard exclusive reactions*
  (arXiv:0712.3533).

The first two entries were checked against public listings. The following two are
**recalled and unverified** — neither was retrieved or checked when this file was
written, and they should be confirmed before being relied on:

* N. Chouika, C. Mezrag, H. Moutarde and J. Rodríguez-Quintero, *Covariant Extension of
  the GPD overlap representation at low Fock states* (arXiv:1711.05108), recalled as
  reducing the ERBL-region extension to an incomplete-data Radon inversion.
* J. Boman and E. T. Quinto, Duke Math. J. **55** (1987) 943, recalled as the uniqueness
  theorem for the Radon transform with incomplete data that such a reduction appeals to.

No equation number is attributed to any of these, and bibliographic data throughout was
taken from listings rather than from the articles themselves.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Exclusive
namespace Deconvolution

open Physlib.Particles.Parton.GPD

variable {Flavor : Type}

/-!

## The data of a low-skewness DGLAP determination

-/

/-- Two GPD models are indistinguishable by DGLAP-region data at skewness below `ξ₀`.

This is the input of the uniqueness statement: the values of `H` in the region
`|ξ| < |x| ≤ 1` for `|ξ| ≤ ξ₀`. Note that it is a hypothesis about the *distribution*,
not about an observable — which is exactly what separates this result from the
shadow-GPD obstruction, whose input is Compton form factor data. -/
def AgreeOnLowSkewnessDglap (M₁ M₂ : Model Flavor) (xi0 : ℝ) : Prop :=
  ∀ i x xi t, InDglapRegion x xi → |xi| ≤ xi0 → M₁.H i x xi t = M₂.H i x xi t

/-!

## Uniqueness up to a D-term

-/

/-- **The analytic core of arXiv:2401.12013.** Agreement in the DGLAP region at low
skewness forces the double-distribution parts of two representations to agree.

Everything the uniqueness statement asserts beyond this is algebra, discharged by
`Physlib.Particles.Parton.GPD.sub_eq_gpdOfDTerm_of_dd_eq`. -/
@[sorryful]
theorem dd_eq_of_agreeOnLowSkewnessDglap {M₁ M₂ : Model Flavor}
    (R₁ : AdmitsDoubleDistribution M₁) (R₂ : AdmitsDoubleDistribution M₂)
    (xi0 : ℝ) (hxi0 : 0 < xi0)
    (hdata : AgreeOnLowSkewnessDglap M₁ M₂ xi0) :
    ∀ i β α t, R₁.ddH.F i β α t = R₂.ddH.F i β α t := by
  -- TODO(task/frontier-open-targets): this is an incomplete-data Radon inversion and is
  -- the whole content of the cited result. The intended argument:
  --   1. Put `H := M₁.H - M₂.H`. By `hdata` it vanishes on `{(x, ξ) : |ξ| < |x| ≤ 1,
  --      |ξ| ≤ ξ₀}`, and by `R₁.reprH`/`R₂.reprH` it is the GPD induced by the difference
  --      of the two double distributions together with the difference of the D-terms.
  --   2. On the DGLAP region the D-term piece is absent
  --      (`gpdOfDTerm_eq_zero_of_inDglapRegion`), so the Radon transform of
  --      `F₁ - F₂` vanishes on every line `x = β + αξ` meeting that region.
  --   3. Conclude `F₁ = F₂` a.e. from a uniqueness theorem for the Radon transform with
  --      incomplete data: a distribution supported in the rhombus whose line integrals
  --      vanish over an open set of lines meeting every point of the rhombus is zero.
  --      UNVERIFIED ATTRIBUTION: this is recalled as Boman-Quinto, Duke Math. J. 55
  --      (1987) 943, applied in this setting as in arXiv:1711.05108. Neither reference
  --      was retrieved or checked; confirm both before relying on this step.
  --   4. Upgrade a.e. equality to the pointwise statement, which needs a continuity or
  --      regularity field on `DoubleDistribution` that does not currently exist -- the
  --      structure carries support, `α`-symmetry and integrability only. Adding it is a
  --      prerequisite, and is noted as such rather than silently assumed.
  -- Mathlib v4.33 has no Radon transform at all, let alone an incomplete-data uniqueness
  -- result for one, so step 3 is not a matter of finding the right lemma name: the
  -- analysis would have to be built. (That much is checked; the attribution above is not.)
  sorry

/-- **Uniqueness up to a D-term (arXiv:2401.12013), in the form quoted in the
literature.** Two models that admit double-distribution representations and agree on the
DGLAP region at low skewness differ exactly by the GPD of a single D-term.

The `∃ dt` is not an accident of the proof: by
`Physlib.Particles.Parton.GPD.gpdOfDTerm_eq_zero_of_inDglapRegion` a D-term is invisible
to the hypothesis `hdata`, so no argument taking this data can do better. -/
@[sorryful]
theorem exists_dTerm_of_agreeOnLowSkewnessDglap {M₁ M₂ : Model Flavor}
    (R₁ : AdmitsDoubleDistribution M₁) (R₂ : AdmitsDoubleDistribution M₂)
    (xi0 : ℝ) (hxi0 : 0 < xi0)
    (hdata : AgreeOnLowSkewnessDglap M₁ M₂ xi0) :
    ∃ dt : DTerm Flavor, ∀ i x xi t,
      M₁.H i x xi t = M₂.H i x xi t + gpdOfDTerm dt i x xi t :=
  ⟨DTerm.sub R₁.dtH R₂.dtH, fun i x xi t =>
    sub_eq_gpdOfDTerm_of_dd_eq R₁ R₂
      (dd_eq_of_agreeOnLowSkewnessDglap R₁ R₂ xi0 hxi0 hdata) i x xi t⟩

/-- The ambiguity the uniqueness statement leaves is *exactly* the ambiguity its data
cannot see: adding a D-term to a model changes nothing in the DGLAP region.

Proved, and the reason `exists_dTerm_of_agreeOnLowSkewnessDglap` cannot be strengthened
by any argument using only `AgreeOnLowSkewnessDglap`. -/
theorem agreeOnLowSkewnessDglap_of_eq_add_gpdOfDTerm {M₁ M₂ : Model Flavor}
    (dt : DTerm Flavor) (xi0 : ℝ)
    (h : ∀ i x xi t, M₁.H i x xi t = M₂.H i x xi t + gpdOfDTerm dt i x xi t) :
    AgreeOnLowSkewnessDglap M₁ M₂ xi0 := by
  intro i x xi t hdglap _
  rw [h i x xi t, gpdOfDTerm_eq_zero_of_inDglapRegion dt i x xi t hdglap, add_zero]

/-!

## Faithfulness of the Compton map on D-terms

-/

/-- The Compton map at this order and scale **separates D-terms**: a D-term whose Compton
form factors vanish identically is itself zero.

Physically this is the statement that the D-term is fixed by the real part of the Compton
form factor, being the subtraction constant of the fixed-`t` dispersion relation
(arXiv:0712.3533, arXiv:1801.05858). It is carried as a hypothesis because it is a
property of the physical coefficient function, which is not written down here. -/
structure SeparatesDTerms (K : ComptonCoefficient) (Flavor : Type) : Prop where
  /-- A D-term in the kernel of the Compton map is the zero D-term. -/
  dTerm_faithful : ∀ (dt : DTerm Flavor) (i : Flavor),
    (∀ xi t, cffOfGpd K (gpdOfDTerm dt) i xi t = 0) → ∀ u t, dt.D i u t = 0

/-!

## The reconciliation

-/

/-- **The two ambiguities are disjoint.** A shadow GPD is never a pure D-term.

This is the first half of the reconciliation: the object the shadow-GPD result produces
is not the object the uniqueness result tolerates. Its proof is the whole argument —
a pure D-term in the kernel of a map that separates D-terms is the zero D-term, hence the
zero GPD, contradicting nontriviality. -/
theorem not_isShadow_of_eq_gpdOfDTerm (K : ComptonCoefficient)
    (hsep : SeparatesDTerms K Flavor) (S : Model Flavor) (hS : IsShadow K S)
    (dt : DTerm Flavor)
    (hrepr : ∀ i x xi t, S.H i x xi t = gpdOfDTerm dt i x xi t) :
    False := by
  obtain ⟨i₀, x₀, xi₀, t₀, hne⟩ := hS.nontrivial
  have hfun : (gpdOfDTerm dt : Gpd Flavor) = S.H := by
    funext i' x' xi' t'
    exact (hrepr i' x' xi' t').symm
  have hker : ∀ (i : Flavor) (xi t : ℝ), cffOfGpd K (gpdOfDTerm dt) i xi t = 0 := by
    intro i xi t
    rw [hfun]
    exact hS.inKernel i xi t
  have hD : ∀ (i : Flavor) (u t : ℝ), dt.D i u t = 0 :=
    fun i => hsep.dTerm_faithful dt i (hker i)
  refine hne ?_
  rw [hrepr i₀ x₀ xi₀ t₀]
  exact gpdOfDTerm_eq_zero_of_dTerm_eq_zero dt hD i₀ x₀ xi₀ t₀

/-- **The reconciliation.** Under the uniqueness statement and faithfulness of the
Compton map on D-terms, every shadow GPD is nonzero somewhere in the DGLAP region at
skewness below `ξ₀`.

In words: a shadow hides from Compton form factors at one order and scale, but it does
not hide from a direct determination of the GPD at low skewness. The two frontier results
therefore constrain complementary data and do not collide.

The uniqueness statement is taken as an explicit hypothesis `huniq` rather than pulled in
from `exists_dTerm_of_agreeOnLowSkewnessDglap`, so that this theorem is free of `sorry`
and the logical dependency is visible in its signature. -/
theorem shadow_visible_in_lowSkewness_dglap (K : ComptonCoefficient)
    (hsep : SeparatesDTerms K Flavor) (S : Model Flavor) (hS : IsShadow K S)
    (R : AdmitsDoubleDistribution S) (xi0 : ℝ)
    (huniq : ∀ (M₁ M₂ : Model Flavor), AdmitsDoubleDistribution M₁ →
      AdmitsDoubleDistribution M₂ → AgreeOnLowSkewnessDglap M₁ M₂ xi0 →
      ∃ dt : DTerm Flavor, ∀ i x xi t,
        M₁.H i x xi t = M₂.H i x xi t + gpdOfDTerm dt i x xi t) :
    ∃ i x xi t, InDglapRegion x xi ∧ |xi| ≤ xi0 ∧ S.H i x xi t ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hdata : AgreeOnLowSkewnessDglap S (Model.zero Flavor) xi0 := by
    intro i x xi t hdglap hxi
    simpa using hcon i x xi t hdglap hxi
  obtain ⟨dt, hdt⟩ := huniq S (Model.zero Flavor) R (admitsDoubleDistribution_zero Flavor) hdata
  refine not_isShadow_of_eq_gpdOfDTerm K hsep S hS dt ?_
  intro i x xi t
  simpa using hdt i x xi t

/-- **The two frontier results, stated together with their hypotheses explicit.**

There exists a leading-order shadow GPD — invisible to Compton form factors at that order
and scale — and it is nonetheless visible in the DGLAP region at low skewness, so the
uniqueness result applies to it without contradiction.

Depends on both tagged `sorry`s of this development: the shadow construction and the
incomplete-data Radon inversion. The glue between them is proved. -/
@[sorryful]
theorem shadow_and_uniqueness_coexist [Nonempty Flavor] (K : ComptonCoefficient)
    (hLO : IsLeadingOrderDvcs K) (hsep : SeparatesDTerms K Flavor)
    (xi0 : ℝ) (hxi0 : 0 < xi0)
    (hrepr : ∀ S : Model Flavor, IsShadow K S → AdmitsDoubleDistribution S) :
    ∃ S : Model Flavor, IsShadow K S ∧
      ∃ i x xi t, InDglapRegion x xi ∧ |xi| ≤ xi0 ∧ S.H i x xi t ≠ 0 := by
  obtain ⟨S, hS, _hA, _hpoly⟩ := hasShadow_of_isLeadingOrderDvcs (Flavor := Flavor) K hLO
  refine ⟨S, hS, ?_⟩
  refine shadow_visible_in_lowSkewness_dglap K hsep S hS (hrepr S hS) xi0 ?_
  intro M₁ M₂ R₁ R₂ hdata
  exact exists_dTerm_of_agreeOnLowSkewnessDglap R₁ R₂ xi0 hxi0 hdata

end Deconvolution
end Exclusive
end DIS
end Scattering
end QFT
end Physlib
