/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Inference.Unfolding
public import Physlib.Meta.Linters.Sorry
/-!

# Identifiability of the parton-distribution inverse problem

Determining a parton distribution from data is an inverse problem. At leading order each
datum is a bounded linear functional of the distribution,

`d a = ∫ K a x * f x dx + noise` for `a = 1, …, m`,

while `f` ranges over an infinite-dimensional space of densities. This module states and
proves the resulting identifiability failure, together with its positive counterpart.

## Main results

- `not_finiteDimensional_blindSubspace`: finitely many bounded measurements of an
  infinite-dimensional density space leave a blind subspace that is not finite-dimensional,
  so the set of densities indistinguishable from any given one is infinite-dimensional.
- `foldForward_eq_predict`: the bridge to the finite-dimensional layer of
  `DIS.Inference.Unfolding`. A response matrix acting on bin contents is the composition of a
  continuum experiment with a binning, so the binned forward map is the restriction of a
  continuum one.
- `not_finiteDimensional_blindSubspace_binning`: binning alone already contributes an
  infinite-dimensional blind subspace, independently of the response matrix and of its rank.
- `exists_unique_penalized_minimizer`: on a compact convex set of admissible densities the
  total chi-square plus a strictly convex penalty has a unique minimizer.
- `not_finiteDimensional_blindSubspace_kernels`: the concrete instance, on square-integrable
  densities over the physical support `(0, 1]` of the Bjorken variable.

## What this does and does not say

The theorem is about the *unregularized* problem: the map from densities to a finite data
vector has an infinite-dimensional kernel, so a fit to finitely many data is determined only
up to that kernel. It does **not** say that published parton-distribution uncertainty bands
are wrong. It says that such bands are conditional on a prior or a regularization, and
`exists_unique_penalized_minimizer` is the statement that a prior of the right kind is
exactly what makes the minimizer unique. Two immediate corollaries of the same reading: a
closure test probes the self-consistency of a fitting pipeline rather than the
identifiability of `f`, and each additional datum removes at most one dimension of the
ambiguity.

## The contrast with bias control

`Unfolding.bias_propagates_to_linear_functional` bounds how unfolding bias appears in a
linear functional of a binned result, but that bound is an *assumption*, carried by
`Unfolding.BiasControlAssumptions`. The ambiguity in the continuum density is by contrast a
*theorem*, needing no physics input beyond infinite-dimensionality of the density space.
`bias_bounded_with_infinite_ambiguity` places the two side by side.

## Conventions

- A measurement is an element of `E →L[ℝ] ℝ`. Linearity in the density is the leading-order
  factorization statement, not a mathematical convenience (Collins, *Foundations of
  Perturbative QCD*, 2011); continuity is a genuine restriction on the kernel, discussed at
  `DensityL2`.
- `Experiment E m` is `Fin m → (E →L[ℝ] ℝ)`, with no wrapper structure: a one-field structure
  around a functional would carry no information beyond the functional itself.
- `totalChiSq` sums the per-point `chiSq` of `DIS.Inference.Basic`, whose normalization is
  `chiSq p o σ = (p - o) ^ 2 / (|σ| + 1)` and not `(p - o) ^ 2 / σ ^ 2`. Every statement here
  is stated for that normalization; none of them uses more about it than nonnegativity and
  convexity in the prediction `p`.
- The kernel of the forward map is called the *blind subspace* rather than the kernel, to
  keep it distinct from the measurement kernels `K a` of the integral above.

## References

- arXiv:2302.14731, *Inverse problems in PDF determinations* — the Bayesian framing of the
  statement proved here.
- arXiv:2404.07573, *Bayesian inference with Gaussian processes for the determination of
  parton distributions* — the constructive counterpart, and an instance of the regularization
  in `exists_unique_penalized_minimizer`.
- arXiv:2303.12006, *Shedding light on shadow generalized parton distributions* — an explicit
  infinite family in the blind subspace of a forward map in the exclusive sector.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Inference
namespace Identifiability

/-!

## Rank-nullity in the form used here

-/

/-- Rank-nullity, in the form this module needs: a linear map into a finite-dimensional space
whose kernel is finite-dimensional has a finite-dimensional domain.

The proof splits the domain as `ker f ⊕ q` for an algebraic complement `q`, on which `f` is
injective, so that `q` embeds into the finite-dimensional codomain.

The mathlib citations used below — `Submodule.exists_isCompl`,
`Submodule.prodEquivOfIsCompl`, `FiniteDimensional.of_injective` and
`FiniteDimensional.of_surjective` — are stated from memory of the library and were not
checked against a toolchain; the argument itself is elementary and does not depend on which
spelling of rank-nullity the library currently offers. -/
theorem finiteDimensional_of_finiteDimensional_ker {M N : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N] [FiniteDimensional ℝ N]
    (f : M →ₗ[ℝ] N) (hker : FiniteDimensional ℝ (LinearMap.ker f)) :
    FiniteDimensional ℝ M := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  have hinj : Function.Injective (f.domRestrict q) := by
    intro y z hyz
    have hzero : f ((y : M) - (z : M)) = 0 := by
      rw [map_sub]
      have hy : f (y : M) = f.domRestrict q y := rfl
      have hz : f (z : M) = f.domRestrict q z := rfl
      rw [hy, hz, hyz, sub_self]
    have hmem : (y : M) - (z : M) ∈ LinearMap.ker f ⊓ q :=
      ⟨LinearMap.mem_ker.mpr hzero, q.sub_mem y.2 z.2⟩
    rw [hq.inf_eq_bot, Submodule.mem_bot] at hmem
    exact Subtype.ext (eq_of_sub_eq_zero hmem)
  haveI : FiniteDimensional ℝ q := FiniteDimensional.of_injective (f.domRestrict q) hinj
  haveI := hker
  exact FiniteDimensional.of_surjective
    (Submodule.prodEquivOfIsCompl (LinearMap.ker f) q hq).toLinearMap
    (Submodule.prodEquivOfIsCompl (LinearMap.ker f) q hq).surjective

/-!

## Finite experiments on a continuum density space

-/

/-- A finite experiment on a density space: `m` bounded linear measurements. The intended
reading of the `a`-th component is `f ↦ ∫ K a x * f x dx` for a measurement kernel `K a`;
that the functional lies in `E →L[ℝ] ℝ` is exactly the requirement that the kernel pair with
the chosen density space boundedly, which is a real constraint and not a formality — see
`DensityL2`. -/
abbrev Experiment (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) :=
  Fin m → (E →L[ℝ] ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m n : ℕ}

/-- The predictions of an experiment for a given density. -/
def predict (X : Experiment E m) (f : E) : Fin m → ℝ := fun a => X a f

/-- The prediction map of an experiment, packaged as a linear map into the
finite-dimensional space `Fin m → ℝ`. Each component is continuous by construction;
continuity of the joint map is not needed for the dimension count below, so only the linear
structure is recorded here. -/
def predictLin (X : Experiment E m) : E →ₗ[ℝ] (Fin m → ℝ) where
  toFun f := predict X f
  map_add' f g := by
    funext a
    simp [predict]
  map_smul' c f := by
    funext a
    simp [predict]

@[simp]
lemma predictLin_apply (X : Experiment E m) (f : E) (a : Fin m) :
    predictLin X f a = X a f := rfl

/-- The blind subspace of an experiment: the densities on which every one of the `m`
measurements returns zero. Two densities are indistinguishable by the experiment exactly
when their difference lies here, so the blind subspace is the linear model of the
experiment's resolution. -/
def blindSubspace (X : Experiment E m) : Submodule ℝ E := LinearMap.ker (predictLin X)

/-- Membership in the blind subspace is annihilation by every measurement. -/
lemma mem_blindSubspace_iff (X : Experiment E m) (f : E) :
    f ∈ blindSubspace X ↔ ∀ a, X a f = 0 := by
  rw [blindSubspace, LinearMap.mem_ker]
  constructor
  · intro hf a
    simpa using congrFun hf a
  · intro hf
    funext a
    simpa using hf a

/-- The blind subspace is the intersection of the kernels of the individual measurements.
This is the form in which the statement is usually written informally. -/
lemma blindSubspace_eq_iInf (X : Experiment E m) :
    blindSubspace X = ⨅ a, LinearMap.ker (X a : E →ₗ[ℝ] ℝ) := by
  ext f
  rw [mem_blindSubspace_iff, Submodule.mem_iInf]
  simp [LinearMap.mem_ker]

/-- Densities differing by an element of the blind subspace give identical predictions:
the data cannot separate them. -/
theorem predict_eq_of_sub_mem_blindSubspace (X : Experiment E m) (f g : E)
    (h : f - g ∈ blindSubspace X) : predict X f = predict X g := by
  funext a
  have ha : X a (f - g) = 0 := (mem_blindSubspace_iff X (f - g)).mp h a
  rw [map_sub] at ha
  simp only [predict]
  linarith

/-- Conversely, identical predictions force the difference into the blind subspace, so the
blind subspace is exactly the indistinguishability class of zero. -/
theorem sub_mem_blindSubspace_of_predict_eq (X : Experiment E m) (f g : E)
    (h : predict X f = predict X g) : f - g ∈ blindSubspace X := by
  rw [mem_blindSubspace_iff]
  intro a
  have ha : X a f = X a g := congrFun h a
  rw [map_sub, ha, sub_self]

/-- **Identifiability failure.** With finitely many bounded measurements of an
infinite-dimensional density space, the blind subspace is not finite-dimensional: the set of
densities indistinguishable from any given one is an infinite-dimensional affine subspace.

Since a further measurement enlarges `m` by one and so can cut the blind subspace down by at
most one dimension, no finite data set closes the gap. -/
theorem not_finiteDimensional_blindSubspace (hE : ¬ FiniteDimensional ℝ E)
    (X : Experiment E m) : ¬ FiniteDimensional ℝ (blindSubspace X) := by
  intro hker
  exact hE (finiteDimensional_of_finiteDimensional_ker (predictLin X) hker)

-- A convenience wrapper phrased with mathlib's `InfiniteDimensional` typeclass was removed
-- here: checked directly against the pinned mathlib source (grepped the whole tree), there is
-- no `InfiniteDimensional` class for modules/vector spaces at this pin -- the only matches are
-- an unrelated order-theoretic `InfiniteDimensional` (`Mathlib/Order/RelSeries.lean`, about
-- poset chains) and module *length* (`Mathlib/RingTheory/Length.lean`). Mathlib's own idiom
-- for "infinite-dimensional vector space" at this revision is exactly the plain hypothesis
-- `¬ FiniteDimensional ℝ E` that `not_finiteDimensional_blindSubspace` above already takes;
-- there is no bridging class to wrap it in.

/-!

## Bridge to the binned response-matrix layer

A binning is itself an experiment: `n` bounded functionals whose values are the bin
contents, computed by `predict`. Composing a binning with a response matrix gives the
`m`-measurement continuum experiment whose predictions the binned layer of
`DIS.Inference.Unfolding` manipulates.

-/

/-- Compose a response matrix with a binning. The `i`-th measurement of the resulting
continuum experiment is `f ↦ ∑ j, R i j * bin j f`, that is, the response matrix applied to
the bin contents of `f`. -/
def experimentOfResponse (R : Unfolding.ResponseMatrix m n) (bin : Experiment E n) :
    Experiment E m :=
  fun i => ∑ j : Fin n, R i j • bin j

/-- The measurements of `experimentOfResponse` in explicit form. -/
@[simp]
lemma experimentOfResponse_apply (R : Unfolding.ResponseMatrix m n) (bin : Experiment E n)
    (i : Fin m) (f : E) :
    experimentOfResponse R bin i f = ∑ j : Fin n, R i j * bin j f := by
  simp [experimentOfResponse, smul_eq_mul]

/-- **The bridge.** Folding a continuum density forward through a binning and then a response
matrix agrees with evaluating the composed continuum experiment and adding the background.
This identifies the finite-dimensional forward map of `DIS.Inference.Unfolding` as the
restriction of a continuum measurement to the range of a binning, which is what licenses
reading the theorems of this module as statements about that layer. -/
theorem foldForward_eq_predict (R : Unfolding.ResponseMatrix m n) (bin : Experiment E n)
    (f : E) (background : Fin m → ℝ) :
    Unfolding.foldForward R (predict bin f) background
      = fun i => predict (experimentOfResponse R bin) f i + background i := by
  funext i
  simp [Unfolding.foldForward, predict]

/-- Binning alone loses information: densities with identical bin contents fold forward to
identical predictions, whatever the response matrix. -/
theorem foldForward_eq_of_predict_bin_eq (R : Unfolding.ResponseMatrix m n)
    (bin : Experiment E n) (f g : E) (background : Fin m → ℝ)
    (h : predict bin f = predict bin g) :
    Unfolding.foldForward R (predict bin f) background
      = Unfolding.foldForward R (predict bin g) background := by
  rw [h]

/-- The blind subspace of a binning is contained in the blind subspace of any experiment
factoring through it: composing with a response matrix can only lose further information. -/
theorem blindSubspace_le_experimentOfResponse (R : Unfolding.ResponseMatrix m n)
    (bin : Experiment E n) :
    blindSubspace bin ≤ blindSubspace (experimentOfResponse R bin) := by
  intro f hf
  rw [mem_blindSubspace_iff] at hf ⊢
  intro i
  rw [experimentOfResponse_apply]
  refine Finset.sum_eq_zero ?_
  intro j _
  rw [hf j, mul_zero]

/-- **Binning is already fatal.** The ambiguity contributed by the binning alone is
infinite-dimensional. This is independent of the response matrix and, in particular, of any
rank condition on it: an invertible `R` recovers the bin contents but never the density, so
no amount of unfolding at fixed binning is an identifiability statement about `f`. -/
theorem not_finiteDimensional_blindSubspace_binning (hE : ¬ FiniteDimensional ℝ E)
    (bin : Experiment E n) : ¬ FiniteDimensional ℝ (blindSubspace bin) :=
  not_finiteDimensional_blindSubspace hE bin

/-!

## The fit objective, and what restores uniqueness

-/

/-- Total chi-square of a density against the data of a finite experiment, assembled from the
per-point `chiSq` contribution of `DIS.Inference.Basic`. -/
def totalChiSq (X : Experiment E m) (data sigma : Fin m → ℝ) (f : E) : ℝ :=
  ∑ a : Fin m, chiSq (predict X f a) (data a) (sigma a)

/-- The total chi-square is nonnegative. -/
lemma totalChiSq_nonneg (X : Experiment E m) (data sigma : Fin m → ℝ) (f : E) :
    0 ≤ totalChiSq X data sigma f :=
  Finset.sum_nonneg fun a _ => chiSq_nonneg _ _ _

/-- The chi-square cannot separate densities differing by an element of the blind subspace:
the objective of the unregularized fit is constant along every blind direction, so it has no
isolated minimizer. -/
lemma totalChiSq_eq_of_sub_mem_blindSubspace (X : Experiment E m) (data sigma : Fin m → ℝ)
    (f g : E) (h : f - g ∈ blindSubspace X) :
    totalChiSq X data sigma f = totalChiSq X data sigma g := by
  rw [totalChiSq, totalChiSq, predict_eq_of_sub_mem_blindSubspace X f g h]

/-- The total chi-square is continuous in the density, since each measurement is. -/
lemma continuous_totalChiSq (X : Experiment E m) (data sigma : Fin m → ℝ) :
    Continuous (totalChiSq X data sigma) := by
  have h : totalChiSq X data sigma
      = fun f => ∑ a : Fin m, chiSq (predict X f a) (data a) (sigma a) := rfl
  rw [h]
  refine continuous_finset_sum _ fun a _ => ?_
  simp only [chiSq, predict]
  exact (((X a).continuous.sub continuous_const).pow 2).div_const _

/-- Convexity of the per-point chi-square contribution in the prediction, for the
normalization `chiSq p o σ = (p - o) ^ 2 / (|σ| + 1)` used in `DIS.Inference.Basic`. The
identity behind it is that the convexity defect equals `a * b * (p - q) ^ 2 / (|σ| + 1)`. -/
lemma chiSq_convex_comb (p q o s a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    chiSq (a * p + b * q) o s ≤ a * chiSq p o s + b * chiSq q o s := by
  have hc : (0 : ℝ) < |s| + 1 := by positivity
  have hcne : |s| + 1 ≠ 0 := ne_of_gt hc
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [chiSq]
  have hid : a * ((p - o) ^ 2 / (|s| + 1)) + (1 - a) * ((q - o) ^ 2 / (|s| + 1))
      - (a * p + (1 - a) * q - o) ^ 2 / (|s| + 1)
      = a * (1 - a) * (p - q) ^ 2 / (|s| + 1) := by
    field_simp
    ring
  have hnn : 0 ≤ a * (1 - a) * (p - q) ^ 2 / (|s| + 1) :=
    div_nonneg (mul_nonneg (mul_nonneg ha (by linarith)) (sq_nonneg _)) hc.le
  linarith

/-- The total chi-square is convex in the density on any convex set of densities: it is a sum
of convex functions of linear functionals of the density. -/
lemma convexOn_totalChiSq (X : Experiment E m) (data sigma : Fin m → ℝ) {S : Set E}
    (hS : Convex ℝ S) : ConvexOn ℝ S (totalChiSq X data sigma) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  have hstep : ∀ i : Fin m,
      chiSq (predict X (a • x + b • y) i) (data i) (sigma i)
        ≤ a * chiSq (predict X x i) (data i) (sigma i)
          + b * chiSq (predict X y i) (data i) (sigma i) := by
    intro i
    have hlin : predict X (a • x + b • y) i
        = a * predict X x i + b * predict X y i := by
      simp [predict]
    rw [hlin]
    exact chiSq_convex_comb _ _ _ _ _ _ ha hb hab
  have hsum : ∑ i : Fin m, chiSq (predict X (a • x + b • y) i) (data i) (sigma i)
      ≤ ∑ i : Fin m, (a * chiSq (predict X x i) (data i) (sigma i)
        + b * chiSq (predict X y i) (data i) (sigma i)) :=
    Finset.sum_le_sum fun i _ => hstep i
  have hsplit : ∑ i : Fin m, (a * chiSq (predict X x i) (data i) (sigma i)
        + b * chiSq (predict X y i) (data i) (sigma i))
      = a * (∑ i : Fin m, chiSq (predict X x i) (data i) (sigma i))
        + b * (∑ i : Fin m, chiSq (predict X y i) (data i) (sigma i)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [totalChiSq, smul_eq_mul]
  rw [← hsplit]
  exact hsum

/-- A strictly convex continuous objective on a nonempty compact set has a unique minimizer.
This is the general form of what a regularization or prior buys: not a smaller blind
subspace, but a selection rule on it. -/
theorem exists_unique_isMinOn_of_strictConvexOn {S : Set E} (hS : IsCompact S)
    (hSne : S.Nonempty) {J : E → ℝ} (hJc : ContinuousOn J S)
    (hJ : StrictConvexOn ℝ S J) :
    ∃! f, f ∈ S ∧ IsMinOn J S f := by
  obtain ⟨f, hfS, hfmin⟩ := hS.exists_isMinOn hSne hJc
  refine ⟨f, ⟨hfS, hfmin⟩, ?_⟩
  rintro g ⟨hgS, hgmin⟩
  by_contra hgf
  have hJeq : J g = J f :=
    le_antisymm (isMinOn_iff.mp hgmin f hfS) (isMinOn_iff.mp hfmin g hgS)
  have hmid : (1 / 2 : ℝ) • g + (1 / 2 : ℝ) • f ∈ S :=
    hJ.1 hgS hfS (by norm_num) (by norm_num) (by norm_num)
  have hlt : J ((1 / 2 : ℝ) • g + (1 / 2 : ℝ) • f)
      < (1 / 2 : ℝ) • J g + (1 / 2 : ℝ) • J f :=
    hJ.2 hgS hfS hgf (by norm_num) (by norm_num) (by norm_num)
  have hge : J f ≤ J ((1 / 2 : ℝ) • g + (1 / 2 : ℝ) • f) := isMinOn_iff.mp hfmin _ hmid
  simp only [smul_eq_mul] at hlt
  rw [hJeq] at hlt
  linarith

/-- **What restores uniqueness.** On a compact convex set of admissible densities, adding a
strictly convex penalty to the total chi-square gives a problem with a unique minimizer —
even though the chi-square term alone is constant along an infinite-dimensional subspace
`blindSubspace X`, by `not_finiteDimensional_blindSubspace` together with
`totalChiSq_eq_of_sub_mem_blindSubspace`. The uniqueness is therefore a property of the
penalty and of the admissible set, and is not extracted from the data. -/
theorem exists_unique_penalized_minimizer (X : Experiment E m) (data sigma : Fin m → ℝ)
    {S : Set E} (hS : IsCompact S) (hSne : S.Nonempty) {pen : E → ℝ}
    (hpenC : ContinuousOn pen S) (hpen : StrictConvexOn ℝ S pen) :
    ∃! f, f ∈ S ∧ IsMinOn (fun g => totalChiSq X data sigma g + pen g) S f := by
  have hchi : ConvexOn ℝ S (totalChiSq X data sigma) :=
    convexOn_totalChiSq X data sigma hpen.1
  have hstrict : StrictConvexOn ℝ S (fun g => totalChiSq X data sigma g + pen g) := by
    refine ⟨hpen.1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have h1 := hchi.2 hx hy ha.le hb.le hab
    have h2 := hpen.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at h1 h2 ⊢
    linarith
  exact exists_unique_isMinOn_of_strictConvexOn hS hSne
    ((continuous_totalChiSq X data sigma).continuousOn.add hpenC) hstrict

/-!

## The honest picture: bounded bias, unbounded ambiguity

-/

/-- The two halves of the honest statement, side by side. The *bias* of an unfolded binned
result is bounded, but only by assumption, via `Unfolding.BiasControlAssumptions`. The
*ambiguity* of the underlying continuum density is infinite-dimensional, and that is a
theorem requiring no assumption beyond infinite-dimensionality of the density space. The two
coexist: a bounded bias on a binned observable says nothing about the dimension of the set of
densities compatible with it. -/
theorem bias_bounded_with_infinite_ambiguity (hE : ¬ FiniteDimensional ℝ E)
    (bin : Experiment E n) (res : Unfolding.UnfoldingResult n) (σTrue : Fin n → ℝ)
    (hBias : Unfolding.BiasControlAssumptions res σTrue) (weight : Fin n → ℝ) :
    |∑ i, weight i * res.unfolded i - ∑ i, weight i * σTrue i|
        ≤ (∑ i, |weight i|) * res.biasBound
      ∧ ¬ FiniteDimensional ℝ (blindSubspace bin) :=
  ⟨Unfolding.bias_propagates_to_linear_functional res σTrue hBias weight,
    not_finiteDimensional_blindSubspace hE bin⟩

/-!

## A concrete density space

-/

/-- The concrete density space: square-integrable densities on the physical support `(0, 1]`
of the Bjorken variable.

`L²` rather than `L¹` is a deliberate choice, and it is the point at which this development
could quietly become vacuous. A measurement functional `f ↦ ∫ K x * f x dx` is bounded on
`L²` exactly when the kernel is itself square integrable, by Cauchy-Schwarz; on `L¹` it is
bounded only for an essentially bounded kernel, which the collinear kernels of DIS are not.
Pointwise evaluation of a density is not a bounded functional on either space and is
deliberately excluded, so the measurements modelled here are smeared or binned observables
rather than idealized point measurements. Indicator kernels of bins are square integrable, so
the binning bridge above does instantiate in this space. -/
abbrev DensityL2 : Type :=
  MeasureTheory.Lp ℝ 2 (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))

/-- The measurement functional attached to a square-integrable kernel: the `L²` inner product
against the kernel. -/
def kernelMeasurement (K : DensityL2) : DensityL2 →L[ℝ] ℝ := innerSL ℝ K

/-- The measurement functional in integral form. -/
@[sorryful]
lemma kernelMeasurement_apply (K f : DensityL2) :
    kernelMeasurement K f
      = ∫ x, K x * f x ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  -- Confirmed against the pinned mathlib source: `MeasureTheory.L2.inner_def (f g) :
  -- ⟪f, g⟫ = ∫ a, ⟪f a, g a⟫ ∂μ` exists exactly as anticipated
  -- (Mathlib/MeasureTheory/Function/L2Space.lean:137). Not attempting the full proof here --
  -- DensityL2's own inner-product/coercion unfolding is not traced -- so this stays open, but
  -- with the previously-unconfirmed name now confirmed.
  sorry

/-- An experiment built from `m` square-integrable measurement kernels. -/
def experimentOfKernels (K : Fin m → DensityL2) : Experiment DensityL2 m :=
  fun a => kernelMeasurement (K a)

/-- The concrete density space is infinite-dimensional. -/
@[sorryful]
lemma not_finiteDimensional_densityL2 : ¬ FiniteDimensional ℝ DensityL2 := by
  -- TODO(task/u2-identifiability): the intended argument exhibits an infinite linearly
  -- independent family, for instance the indicators of the pairwise disjoint intervals
  -- `Set.Ioc (1 / (k + 2)) (1 / (k + 1))` for `k : ℕ`. Each is square integrable on `(0, 1]`
  -- and they have pairwise disjoint supports, hence are linearly independent in `L²`.
  -- Writing this needs the current names for `MeasureTheory.memLp_indicator_const` and
  -- `Real.volume_Ioc` plus a `LinearIndependent` argument over disjoint supports, none of
  -- which could be confirmed without a toolchain, so the step is left open.
  sorry

/-- **The concrete statement.** Finitely many square-integrable measurement kernels leave an
infinite-dimensional blind subspace of square-integrable densities on `(0, 1]`. This is the
instance that carries the physics content: the abstract theorem alone does not exhibit a
space in which the measurement functionals really are continuous. -/
@[sorryful]
theorem not_finiteDimensional_blindSubspace_kernels (K : Fin m → DensityL2) :
    ¬ FiniteDimensional ℝ (blindSubspace (experimentOfKernels K)) :=
  not_finiteDimensional_blindSubspace not_finiteDimensional_densityL2 _

end Identifiability
end Inference
end DIS
end Scattering
end QFT
end Physlib
