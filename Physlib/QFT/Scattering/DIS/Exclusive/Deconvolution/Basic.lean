/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.Linters.Sorry
public import Physlib.Particles.Parton.GPD.Ambiguity
public import Physlib.Particles.Parton.GPD.Moments
/-!

# The Compton Map and its Kernel: Shadow GPDs

The *deconvolution problem* of deeply virtual Compton scattering is the question of
whether the map from a generalized parton distribution to its Compton form factors is
injective. This module states the map, its kernel, and the shadow-GPD obstruction.

## Order and scale are part of the data, not of the GPD

The Compton form factor is computed from a perturbative coefficient function at a
renormalization scale, and the kernel of the resulting linear map depends on **both**.
Shadow GPDs "manifest as multiple solutions (at a fixed scale `Q²`) to the inverse
problem", and the reason the obstruction is not fatal is that "the known classes of
shadow GPDs begin to contribute to observables after evolution, and can then be
constrained (at the input scale) by data that has a finite `Q²` range"
(Moffat *et al.*, arXiv:2303.12006, abstract). They are also process-dependent.

`ComptonCoefficient` therefore carries an explicit `order` and `scale`, and `IsShadow` is
a relation between a coefficient function and a model, never a property of a model alone.
A formalization that dropped the labels would assert that a shadow is invisible to *all*
DVCS data, which is false. `isShadow_congr` records that the shadow set depends on the
coefficient function only through its values — hence on order, scale and process only
through the coefficient function they determine.

## What is and is not proved here

* The map, its kernel, linearity in the GPD, and the equivalence "same Compton form
  factors" ⇔ "difference in the kernel" are proved.
* `ComptonIntegrable` is discharged for continuous data by
  `ComptonIntegrable.of_continuousOn` (compactness of `[-1, 1]`), so the bundle is an
  assumption only for the distributional coefficient functions it was introduced for.
* `isShadow_of_moments_eq_zero` reduces the construction of a shadow to the construction
  of a nonzero GPD annihilated by the moment functionals the map samples, which is the
  mechanism of the shadow-GPD constructions in the literature.
* `hasShadow_of_isLeadingOrderDvcs`, the literature claim itself, is a tagged `sorry`:
  the explicit construction needs Gegenbauer polynomials and a conformal-moment
  transform, neither of which exists here or in mathlib. See its `TODO`.

The coefficient function is deliberately left abstract. Writing down the leading-order
DVCS coefficient function honestly requires the `iε` prescription
`1 / (ξ - x - iε) - 1 / (ξ + x - iε)` as a distributional limit, and this repository has
no principal-value machinery; a fixed-`ε` stand-in would be a different object, and a
theorem about it would be a theorem about the wrong thing. `IsLeadingOrderDvcs` instead
names the structural properties of that coefficient function which the shadow
construction uses.

## References

* E. Moffat, A. Freese, I. Cloët, T. Donohoe, L. Gamberg, W. Melnitchouk, A. Metz,
  A. Prokudin and N. Sato, *Shedding light on shadow generalized parton distributions*,
  Phys. Rev. D **108** (2023) 036027 (arXiv:2303.12006).
* V. Bertone, H. Dutrieux, C. Mezrag, H. Moutarde and P. Sznajder, *Shadow generalized
  parton distributions: a practical approach to the deconvolution problem of DVCS*,
  SciPost Phys. Proc. **8** (2022) 107 (arXiv:2107.11312).
* M. Diehl, *Generalized parton distributions*, Phys. Rept. **388** (2003) 41
  (arXiv:hep-ph/0307382).
* A. V. Belitsky and A. V. Radyushkin, Phys. Rept. **418** (2005) 1 (arXiv:hep-ph/0504030).

Bibliographic data above was taken from public listings rather than from the articles
themselves; no equation number is cited anywhere in this module for that reason.

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

## The Compton map

-/

/-- An order- and scale-labelled Compton coefficient function.

The coefficient function is complex-valued because the physical one carries the `iε`
prescription of the hard propagators: the real part of the resulting form factor is a
principal-value integral and the imaginary part samples the GPD on the cross-over line.

The `order` and `scale` fields are load-bearing rather than decorative. The kernel of the
induced map is a function of the coefficient function, hence of the order at which it is
truncated, of the scale at which it is evaluated, and of the process it describes; a
GPD annihilated at one choice is in general not annihilated at another. -/
structure ComptonCoefficient : Type where
  /-- The perturbative order at which this coefficient function is complete. -/
  order : ℕ
  /-- The renormalization scale `Q²` at which the coefficient function is evaluated. -/
  scale : ℝ
  /-- The coefficient function `C(x, ξ, t)`. -/
  C : ℝ → ℝ → ℝ → ℂ

/-- The Compton form factor of a bare GPD function, at the order and scale carried by `K`.

The integral runs over the full GPD support `|x| ≤ 1`. Restricting it to `x ≥ 0` — as the
GPD interface did before the support correction — would discard the antiquark region and
the negative-`x` half of the ERBL region, and would make the shadow-GPD question
unstatable, since the known shadow constructions live partly in the ERBL region. -/
def cffOfGpd (K : ComptonCoefficient) (H : Gpd Flavor) (i : Flavor) (xi t : ℝ) : ℂ :=
  ∫ x in Set.Icc (-1 : ℝ) 1, K.C x xi t * ((H i x xi t : ℝ) : ℂ)

/-- The Compton form factor built from the `H` component of a GPD model. -/
def cffH (K : ComptonCoefficient) (M : Model Flavor) (i : Flavor) (xi t : ℝ) : ℂ :=
  cffOfGpd K M.H i xi t

/-- Integrability of the Compton integrand, carried as an assumption bundle rather than
assumed inline at each use. -/
structure ComptonIntegrable (K : ComptonCoefficient) (H : Gpd Flavor) (i : Flavor) : Prop where
  /-- The integrand is integrable on the GPD support, at every skewness and momentum
  transfer. -/
  integrableOn : ∀ xi t,
    MeasureTheory.IntegrableOn
      (fun x : ℝ => K.C x xi t * ((H i x xi t : ℝ) : ℂ)) (Set.Icc (-1 : ℝ) 1)

/-- **Discharging `ComptonIntegrable` for regular data.** A coefficient function and a GPD
that are continuous on the support `[-1, 1]` at every skewness and momentum transfer give an
integrable Compton integrand there, because `[-1, 1]` is compact.

This turns the bundle from an assumption into a hypothesis on the input for every model to
which it applies. It does *not* cover the physical leading-order coefficient function, which
carries the `iε` prescription and is a distribution rather than a continuous function — see
the module docstring. That case needs the principal-value machinery this repository lacks,
so the bundle is kept rather than replaced. -/
lemma ComptonIntegrable.of_continuousOn (K : ComptonCoefficient) (H : Gpd Flavor) (i : Flavor)
    (hC : ∀ xi t, ContinuousOn (fun x : ℝ => K.C x xi t) (Set.Icc (-1 : ℝ) 1))
    (hH : ∀ xi t, ContinuousOn (fun x : ℝ => H i x xi t) (Set.Icc (-1 : ℝ) 1)) :
    ComptonIntegrable K H i where
  integrableOn := fun xi t =>
    ((hC xi t).fun_mul
      (Complex.continuous_ofReal.comp_continuousOn' (hH xi t))).integrableOn_Icc

/-- The globally continuous case of `ComptonIntegrable.of_continuousOn`, which is the form
most model GPDs are presented in. -/
lemma ComptonIntegrable.of_continuous (K : ComptonCoefficient) (H : Gpd Flavor) (i : Flavor)
    (hC : ∀ xi t, Continuous (fun x : ℝ => K.C x xi t))
    (hH : ∀ xi t, Continuous (fun x : ℝ => H i x xi t)) :
    ComptonIntegrable K H i :=
  ComptonIntegrable.of_continuousOn K H i (fun xi t => (hC xi t).continuousOn)
    (fun xi t => (hH xi t).continuousOn)

/-- The Compton map is linear: it takes the difference of two GPDs to the difference of
their Compton form factors. This is the step that turns the deconvolution problem into a
question about a kernel. -/
lemma cffOfGpd_sub (K : ComptonCoefficient) (H₁ H₂ : Gpd Flavor) (i : Flavor)
    (h₁ : ComptonIntegrable K H₁ i) (h₂ : ComptonIntegrable K H₂ i) (xi t : ℝ) :
    cffOfGpd K (H₁ - H₂) i xi t = cffOfGpd K H₁ i xi t - cffOfGpd K H₂ i xi t := by
  have hpt : ∀ x : ℝ, K.C x xi t * (((H₁ - H₂) i x xi t : ℝ) : ℂ)
      = K.C x xi t * ((H₁ i x xi t : ℝ) : ℂ) - K.C x xi t * ((H₂ i x xi t : ℝ) : ℂ) := by
    intro x
    simp [Pi.sub_apply, Complex.ofReal_sub, mul_sub]
  simp only [cffOfGpd, hpt]
  exact MeasureTheory.integral_sub (h₁.integrableOn xi t) (h₂.integrableOn xi t)

/-!

## The kernel

-/

/-- Membership in the kernel of the Compton map at the order and scale carried by `K`:
the Compton form factor vanishes at every skewness and momentum transfer. -/
def IsInComptonKernel (K : ComptonCoefficient) (H : Gpd Flavor) (i : Flavor) : Prop :=
  ∀ xi t, cffOfGpd K H i xi t = 0

/-- **The deconvolution problem, stated.** Two GPD models are indistinguishable by Compton
form factors at this order and scale exactly when their difference lies in the kernel of
the map.

The whole question of GPD extraction from a single exclusive channel is therefore a
question about that kernel: the extraction is unique iff the kernel is trivial. -/
lemma isInComptonKernel_sub_iff (K : ComptonCoefficient) (M₁ M₂ : Model Flavor) (i : Flavor)
    (h₁ : ComptonIntegrable K M₁.H i) (h₂ : ComptonIntegrable K M₂.H i) :
    IsInComptonKernel K (M₁.H - M₂.H) i ↔ ∀ xi t, cffH K M₁ i xi t = cffH K M₂ i xi t := by
  constructor
  · intro h xi t
    have hz := h xi t
    rw [cffOfGpd_sub K M₁.H M₂.H i h₁ h₂ xi t] at hz
    exact sub_eq_zero.mp hz
  · intro h xi t
    rw [cffOfGpd_sub K M₁.H M₂.H i h₁ h₂ xi t]
    exact sub_eq_zero.mpr (h xi t)

/-!

## Shadow GPDs

-/

/-- A **shadow GPD** at the order and scale carried by `K`.

The three conditions are what make such an object an obstruction to extraction rather
than a curiosity:

* `nontrivial` — it is not the zero model, so adding it to a fit changes the GPD;
* `forwardVanishing` — its forward limit vanishes, so the collinear PDF data that would
  otherwise constrain it does not;
* `inKernel` — its Compton form factors vanish identically at this order and scale, so
  DVCS data analysed there does not see it.

Physical admissibility (support, skewness range) and polynomiality are deliberately *not*
fields: they are carried separately in `HasShadow`, because they are the hypotheses under
which the existence claim has content and it should be visible where they enter. -/
structure IsShadow (K : ComptonCoefficient) (S : Model Flavor) : Prop where
  /-- The model is not identically zero. -/
  nontrivial : ∃ i x xi t, S.H i x xi t ≠ 0
  /-- The forward limit vanishes, so collinear PDF data does not see it. -/
  forwardVanishing : ∀ i x t, S.H i x 0 t = 0
  /-- Every Compton form factor vanishes at this order and scale. -/
  inKernel : ∀ i, IsInComptonKernel K S.H i

/-- The shadow property depends on the coefficient function only through its values.

Trivial, but worth recording: it is the formal reason that "shadow" is never a property
of a GPD alone, and hence that a shadow at one order, scale or process carries no
information about another. -/
lemma isShadow_congr {K K' : ComptonCoefficient} (S : Model Flavor)
    (hC : ∀ x xi t, K.C x xi t = K'.C x xi t) (hS : IsShadow K S) :
    IsShadow K' S := by
  refine ⟨hS.nontrivial, hS.forwardVanishing, ?_⟩
  intro i xi t
  have h := hS.inKernel i xi t
  simpa [cffOfGpd, hC] using h

/-- The Compton map at this order and scale **has a shadow** for the flavour space
`Flavor`: its kernel contains a nonzero, physically admissible, polynomiality-respecting
model with vanishing forward limit.

Stated as a definition rather than asserted, so that results depending on it carry it
visibly as a hypothesis. -/
def HasShadow (K : ComptonCoefficient) (Flavor : Type) : Prop :=
  ∃ S : Model Flavor, IsShadow K S ∧ Assumptions S ∧ Nonempty (PolynomialityAssumptions S)

/-!

## The mechanism: factorization through sampled moments

-/

/-- The structural fact behind the shadow-GPD constructions: at fixed order and scale the
Compton map annihilates any GPD annihilated by a family of moment functionals.

For the leading-order DVCS coefficient function those functionals are the conformal
moments at non-negative integer conformal spin; constructing a shadow then amounts to
finding a nonzero GPD on which all of them vanish. Carrying the family as data makes the
construction problem explicit instead of hiding it inside an existence claim. -/
structure FactorsThroughMoments (K : ComptonCoefficient) (Flavor : Type) : Type where
  /-- The moment functionals the map samples, indexed by conformal spin. -/
  moment : ℕ → Gpd Flavor → Flavor → ℝ → ℝ
  /-- A GPD annihilated by all of them lies in the kernel of the Compton map. -/
  cff_eq_zero_of_moments_eq_zero : ∀ (H : Gpd Flavor) (i : Flavor),
    (∀ n t, moment n H i t = 0) → IsInComptonKernel K H i

/-- **The shadow problem, reduced.** A nonzero model with vanishing forward limit on which
all sampled moments vanish is a shadow.

This is the provable half of the shadow-GPD claim: the work in the literature is not in
this step but in exhibiting such a model subject to polynomiality. -/
theorem isShadow_of_moments_eq_zero {K : ComptonCoefficient}
    (F : FactorsThroughMoments K Flavor) (S : Model Flavor)
    (hne : ∃ i x xi t, S.H i x xi t ≠ 0)
    (hfwd : ∀ i x t, S.H i x 0 t = 0)
    (hmom : ∀ n i t, F.moment n S.H i t = 0) :
    IsShadow K S :=
  ⟨hne, hfwd, fun i => F.cff_eq_zero_of_moments_eq_zero S.H i (fun n t => hmom n i t)⟩

/-!

## The leading-order DVCS coefficient function and the literature claim

-/

/-- The structural properties of the leading-order DVCS quark coefficient function that
the shadow construction uses.

`C(x, ξ, t)` has no independent dependence on the momentum transfer, and — being built
from the two hard quark propagators `1 / (ξ ∓ x - iε)` — is homogeneous of degree `-1`
under simultaneous rescaling of `x` and `ξ`. Homogeneity is what collapses the
coefficient function to a single function of `x / ξ`, hence what makes the kernel at each
skewness the annihilator of one linear functional; it is the property the
conformal-moment analysis rests on.

These are properties, not a definition: the coefficient function itself is a distribution
and is not written down in this repository. -/
structure IsLeadingOrderDvcs (K : ComptonCoefficient) : Prop where
  /-- This is a leading-order coefficient function. -/
  order_eq : K.order = 0
  /-- No independent momentum-transfer dependence. -/
  tIndependent : ∀ x xi t t', K.C x xi t = K.C x xi t'
  /-- Homogeneity of degree `-1` in `(x, ξ)`. -/
  homogeneous : ∀ (l x xi t : ℝ), 0 < l →
    K.C (l * x) (l * xi) t = ((l : ℝ) : ℂ)⁻¹ * K.C x xi t

/-- **Non-uniqueness at leading order (arXiv:2303.12006, arXiv:2107.11312).** The
leading-order DVCS Compton map has a shadow.

Together with `exists_dTerm_of_agreeOnLowSkewnessDglap` in
`Physlib.QFT.Scattering.DIS.Exclusive.Deconvolution.Uniqueness` this is the pair of
statements the frontier task targets; see that module for why they do not collide. -/
@[sorryful]
theorem hasShadow_of_isLeadingOrderDvcs [Nonempty Flavor] (K : ComptonCoefficient)
    (hK : IsLeadingOrderDvcs K) :
    HasShadow K Flavor := by
  -- TODO(task/frontier-open-targets): what is missing is the explicit construction, not
  -- the reduction. `isShadow_of_moments_eq_zero` reduces the goal to exhibiting a nonzero
  -- `S : Model Flavor` with (a) vanishing forward limit, (b) vanishing conformal moments
  -- at every non-negative integer conformal spin, and (c) `PolynomialityAssumptions S`
  -- together with `GPD.Assumptions S`. The constructions in the literature build `S` from
  -- Gegenbauer polynomials `C_n^{3/2}` on the ERBL region matched to a DGLAP-region tail
  -- and verify (b) by an orthogonality relation. Mathlib v4.33 has `Polynomial.Chebyshev`
  -- and `Polynomial.legendre` but no Gegenbauer family and no conformal-moment transform,
  -- and this repository has neither; both would have to be built first, and that is a
  -- task in its own right rather than a step of this proof.
  -- `hK` is the hypothesis under which the claim is made. Dropping it would leave a
  -- statement about an arbitrary coefficient function, which is false in general: a
  -- coefficient function whose sampled moment family separates points has trivial kernel.
  sorry

end Deconvolution
end Exclusive
end DIS
end Scattering
end QFT
end Physlib
