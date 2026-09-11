/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.Linters.Sorry
public import Physlib.Particles.Parton.PDF.Basic
public import Physlib.QFT.Factorization.Convolution.Collinear
/-!

# The Mellin transform of a collinear convolution

The Mellin transform turns the collinear convolution of collinear factorization into a pointwise
product. This is the reason moment space is the natural home of evolution: the integro-differential
DGLAP equation becomes, for each value of the Mellin index, an ordinary differential equation in
`Q ^ 2` whose coefficients are the anomalous dimensions.

## Conventions

- **The transform.** `mellinDis f N = ∫_{(0,1]} x ^ (N - 1) * f x dx`. This is the DIS/literature
  convention: the momentum sum rule sits at `N = 2` and the number sum rule at `N = 1`.
- **Relation to `mellinMoment`.** The repository's `Physlib.Particles.Parton.PDF.mellinMoment f n`
  is `∫_{[0,1]} x ^ n * f x dx`, i.e. the *shifted* index: `mellinMoment f n = mellinDis f (n + 1)`
  (`mellinDis_eq_mellinMoment`). In particular the momentum sum rule is `mellinMoment f 1`, which
  is `mellinDis f 2`. Both conventions are in use in the literature and mixing them is a standing
  source of off-by-one errors; every statement below is in terms of `N`, with the `n + 1` bridge
  proved once.
- **The domain is `(0,1]`, not `[0,1]`.** The weight `x ^ (N - 1)` is singular at `0`, so the
  transform must be an integral over `Set.Ioc 0 1`; `mellinMoment` uses `Set.Icc 0 1`, which is
  harmless there (the integrand is bounded near `0` for `n : ℕ`) but not here. The two agree
  whenever both are defined, because `{0}` is a null set.
- **Complex powers.** `(x : ℂ) ^ (N - 1)` is `Complex.cpow`, which has a branch cut on the
  negative reals; on the domain `(0,1]` it is well behaved, which is why the domain is kept
  visible in every statement.

## Which transform

Mathlib's `mellin` (`Mathlib/Analysis/MellinTransform.lean`) integrates over `Set.Ioi 0` and would
supply convergence and analyticity in the complex index for free, at the cost of extending each
distribution by zero to `(0, ∞)`. No mathlib source was available in the environment in which this
module was written, so its exact signature and hypotheses could not be checked; rather than guess
them, the transform here is defined from scratch on the DIS domain. The intended bridge, to be
added once the signature can be confirmed, is

```
mellinDis f N = mellin (fun t => if t ≤ 1 then (f t : ℂ) else 0) N
```

from which analyticity of `mellinDis` in `N` on the convergence strip would follow. Until then,
analyticity in `N` is *not* available from this module.

## Scope

The convolution theorem below is for *integrable* coefficient functions. Physical splitting
kernels have `1 / (1 - z)` endpoint singularities regulated by plus-distributions; those are not
functions `ℝ → ℝ` and are out of scope, as is the corresponding `1 / (1 - z)` term of the
transform. Extending the theorem to distributional kernels is a separate development.

## Table of contents

- A. The transform and its convergence strip
- B. Linearity
- C. Natural indices and the bridge to `mellinMoment`
- D. The convolution theorem
- E. Moment-space corollaries

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace QFT
namespace Factorization
namespace Convolution

/-!

## A. The transform and its convergence strip

-/

/-- The DIS Mellin transform of a real distribution supported on `(0,1]`:
`mellinDis f N = ∫_{(0,1]} x ^ (N - 1) * f x dx`, with the index convention in which the momentum
sum rule sits at `N = 2`. The value is complex because the index is; the argument is real because
parton distributions are. -/
def mellinDis (f : ℝ → ℝ) (N : ℂ) : ℂ :=
  ∫ x in Set.Ioc (0 : ℝ) 1, (x : ℂ) ^ (N - 1) * (f x : ℂ)

/-- `f` has an absolutely convergent Mellin transform at index `N`. For a distribution behaving
like `x ^ (-lam)` as `x → 0` this holds exactly on the half plane `lam < Re N`, so the "strip" of
the convolution theorem is a genuine constraint and not a formality. -/
def MellinDisConvergent (f : ℝ → ℝ) (N : ℂ) : Prop :=
  MeasureTheory.IntegrableOn
    (fun x : ℝ => (x : ℂ) ^ (N - 1) * (f x : ℂ)) (Set.Ioc (0 : ℝ) 1)

/-- The Mellin transform of the zero distribution vanishes. -/
lemma mellinDis_zero (N : ℂ) : mellinDis (fun _ => 0) N = 0 := by
  simp [mellinDis]

/-!

## B. Linearity

-/

/-- The Mellin transform is homogeneous. No convergence hypothesis is needed: both sides are the
same Bochner integral. -/
lemma mellinDis_const_mul (c : ℝ) (f : ℝ → ℝ) (N : ℂ) :
    mellinDis (fun x => c * f x) N = (c : ℂ) * mellinDis f N := by
  have h : (fun x : ℝ => (x : ℂ) ^ (N - 1) * ((c * f x : ℝ) : ℂ))
      = fun x : ℝ => (c : ℂ) • ((x : ℂ) ^ (N - 1) * (f x : ℂ)) := by
    funext x
    simp only [Complex.ofReal_mul, smul_eq_mul]
    ring
  rw [mellinDis, h, MeasureTheory.integral_smul, mellinDis, smul_eq_mul]

/-- The Mellin transform is additive on the convergence strip. -/
lemma mellinDis_add (f g : ℝ → ℝ) (N : ℂ)
    (hf : MellinDisConvergent f N) (hg : MellinDisConvergent g N) :
    mellinDis (fun x => f x + g x) N = mellinDis f N + mellinDis g N := by
  have h : (fun x : ℝ => (x : ℂ) ^ (N - 1) * ((f x + g x : ℝ) : ℂ))
      = fun x : ℝ => (x : ℂ) ^ (N - 1) * (f x : ℂ) + (x : ℂ) ^ (N - 1) * (g x : ℂ) := by
    funext x
    push_cast
    ring
  rw [mellinDis, h, MeasureTheory.integral_add hf hg, mellinDis, mellinDis]

/-- The Mellin transform commutes with finite sums on the convergence strip. This is the form
needed by flavor sums, in particular by the DGLAP operator. -/
lemma mellinDis_finsetSum {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℝ) (N : ℂ)
    (h : ∀ i ∈ s, MellinDisConvergent (g i) N) :
    mellinDis (fun x => ∑ i ∈ s, g i x) N = ∑ i ∈ s, mellinDis (g i) N := by
  have hfun : (fun x : ℝ => (x : ℂ) ^ (N - 1) * ((∑ i ∈ s, g i x : ℝ) : ℂ))
      = fun x : ℝ => ∑ i ∈ s, (x : ℂ) ^ (N - 1) * (g i x : ℂ) := by
    funext x
    rw [Complex.ofReal_sum, Finset.mul_sum]
  simp only [mellinDis]
  rw [hfun, MeasureTheory.integral_finset_sum s h]

/-!

## C. Natural indices and the bridge to `mellinMoment`

-/

/-- At index `n + 1` with `n : ℕ` the complex weight collapses to the real monomial `x ^ n`;
this is the identity that makes the natural-moment corollaries free of complex analysis. -/
lemma mellinDis_natCast_add_one (f : ℝ → ℝ) (n : ℕ) :
    mellinDis f ((n : ℂ) + 1) = ∫ x in Set.Ioc (0 : ℝ) 1, ((x ^ n * f x : ℝ) : ℂ) := by
  have h : (fun x : ℝ => (x : ℂ) ^ (((n : ℂ) + 1) - 1) * (f x : ℂ))
      = fun x : ℝ => ((x ^ n * f x : ℝ) : ℂ) := by
    funext x
    -- TODO(task/e1-mellin-convolution): `add_sub_cancel_right : a + b - b = a` and
    -- `Complex.cpow_natCast : x ^ (n : ℂ) = x ^ n` are the two rewrites used here; both have had
    -- different names in earlier mathlib versions (`add_sub_cancel`, `Complex.cpow_nat_cast`)
    -- and neither could be checked against source at this pin.
    rw [add_sub_cancel_right, Complex.cpow_natCast]
    push_cast
    ring
  rw [mellinDis, h]

/-- At natural indices the Mellin transform is the complexification of a real integral. -/
lemma mellinDis_natCast_add_one_eq_ofReal (f : ℝ → ℝ) (n : ℕ) :
    mellinDis f ((n : ℂ) + 1)
      = ((∫ x in Set.Ioc (0 : ℝ) 1, x ^ n * f x : ℝ) : ℂ) := by
  rw [mellinDis_natCast_add_one]
  -- TODO(task/e1-mellin-convolution): the lemma pulling `Complex.ofReal` out of a Bochner
  -- integral is `MeasureTheory.integral_ofReal` (it is unconditional, both sides being `0` off
  -- the integrable case); at some mathlib versions it is stated for `RCLike` and may need to be
  -- reached as `RCLike.ofReal_integral` or with the target field supplied explicitly.
  exact MeasureTheory.integral_ofReal

/-- **Bridge to the repository's integer moments.** `mellinMoment f n` is
`∫_{[0,1]} x ^ n * f x dx`, so it is the Mellin transform at index `n + 1`, *not* at index `n`.
Note that no assumption on the PDF is needed: the two domains `[0,1]` and `(0,1]` differ by a
null set, whether or not the integrand is integrable. -/
lemma mellinDis_eq_mellinMoment {Flavor : Type}
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor) (n : ℕ) (i : Flavor) (Q2 : ℝ) :
    mellinDis (fun x => f i x Q2) ((n : ℂ) + 1)
      = ((Physlib.Particles.Parton.PDF.mellinMoment f n i Q2 : ℝ) : ℂ) := by
  rw [mellinDis_natCast_add_one_eq_ofReal]
  simp only [Physlib.Particles.Parton.PDF.mellinMoment]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

/-!

## D. The convolution theorem

-/

/-- The complexified two-variable integrand whose iterated integral is the Mellin transform of a
collinear convolution: `mellinIntegrand C f N x z = x ^ (N - 1) * K_C (x, z) * f z`. -/
def mellinIntegrand (C f : ℝ → ℝ) (N : ℂ) (x z : ℝ) : ℂ :=
  (x : ℂ) ^ (N - 1) * ((integrand (collinearKernel C) f x z : ℝ) : ℂ)

/-- Hypotheses of the Mellin convolution theorem, collected in one bundle: absolute convergence
of each transform at the index `N` (the "strip" condition), and joint integrability on the
triangle `{(x, z) : 0 < x ≤ z ≤ 1}` in exactly the form the Fubini exchange consumes.

None of the fields is a bare `Prop` placeholder: each is an integrability statement about a named
integrand, so the bundle cannot be discharged vacuously. -/
structure MellinConvolutionAssumptions (C f : ℝ → ℝ) (N : ℂ) : Prop where
  /-- The transform of the coefficient function converges absolutely at `N`. -/
  convC : MellinDisConvergent C N
  /-- The transform of the distribution converges absolutely at `N`. -/
  convF : MellinDisConvergent f N
  /-- Joint integrability of the two-variable integrand over `(0,1] × (0,1]`, which is what the
  exchange of the `x` and `z` integrations requires. The support condition of the collinear
  kernel restricts this to the triangle `0 < x ≤ z ≤ 1`. -/
  jointIntegrable : MeasureTheory.Integrable
    (Function.uncurry (mellinIntegrand C f N))
    ((MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))

/-- The inner integral of `mellinIntegrand` reproduces the convolution, weighted. This is an
unconditional identity: the `z`-integral is the convolution by definition, and the complex weight
is a constant in `z`. -/
lemma integral_mellinIntegrand_eq (C f : ℝ → ℝ) (N : ℂ) (x : ℝ) :
    (∫ z in Set.Ioc (0 : ℝ) 1, mellinIntegrand C f N x z)
      = (x : ℂ) ^ (N - 1) * ((convolveAt (collinearKernel C) f x : ℝ) : ℂ) := by
  simp only [mellinIntegrand]
  -- TODO(task/e1-mellin-convolution): `MeasureTheory.integral_const_mul` is the `RCLike`-valued
  -- lemma `∫ a, r * f a = r * ∫ a, f a`; if it is unavailable at this pin the same step is
  -- `MeasureTheory.integral_smul` after `← smul_eq_mul`.
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_ofReal,
    convolveAt_eq_integral_Ioc]

/-- The Mellin transform of a collinear convolution as an iterated integral. Unconditional. -/
lemma mellinDis_convolveAt_eq_iteratedIntegral (C f : ℝ → ℝ) (N : ℂ) :
    mellinDis (convolveAt (collinearKernel C) f) N
      = ∫ x in Set.Ioc (0 : ℝ) 1, ∫ z in Set.Ioc (0 : ℝ) 1, mellinIntegrand C f N x z := by
  rw [funext (integral_mellinIntegrand_eq C f N), mellinDis]

/-- Joint integrability implies that the convolution itself has a convergent transform, so the
assumption bundle is enough to state and use moment-space additivity downstream. -/
lemma MellinConvolutionAssumptions.convolutionConvergent {C f : ℝ → ℝ} {N : ℂ}
    (h : MellinConvolutionAssumptions C f N) :
    MellinDisConvergent (convolveAt (collinearKernel C) f) N := by
  show MeasureTheory.IntegrableOn
    (fun x : ℝ => (x : ℂ) ^ (N - 1) * ((convolveAt (collinearKernel C) f x : ℝ) : ℂ))
    (Set.Ioc (0 : ℝ) 1)
  rw [← funext (integral_mellinIntegrand_eq C f N)]
  -- TODO(task/e1-mellin-convolution): `MeasureTheory.Integrable.integral_prod_left` of
  -- `Mathlib/MeasureTheory/Constructions/Prod/Integral.lean` states that integrability of
  -- `uncurry F` on `μ.prod ν` gives integrability of `fun x => ∫ y, F x y ∂ν` for `μ`; the name
  -- could not be checked against source at this pin.
  exact h.jointIntegrable.integral_prod_left

/-- The scaling step of the convolution theorem: for `z` in the physical region, substituting
`x = z * u` in the inner `x`-integral factors the weight as `(z * u) ^ (N - 1)` and consumes the
`z⁻¹` Jacobian of the collinear kernel, leaving `z ^ (N - 1) * f z` times the transform of the
coefficient function.

This is the one place where the collinear form of the kernel is used, and it is the sanity check
on the definition: with any other power of `z` in the kernel the factorization fails. -/
@[sorryful]
lemma integral_mellinIntegrand_of_mem (C f : ℝ → ℝ) (N : ℂ) {z : ℝ}
    (hz0 : 0 < z) (hz1 : z ≤ 1) (hC : MellinDisConvergent C N) :
    (∫ x in Set.Ioc (0 : ℝ) 1, mellinIntegrand C f N x z)
      = (z : ℂ) ^ (N - 1) * (f z : ℂ) * mellinDis C N := by
  -- TODO(task/e1-mellin-convolution): this is the change-of-variables step and it is not proved.
  -- The intended argument, in four steps:
  --   1. On `(0,1]` the kernel's indicator restricts the domain: since `z ≤ 1`, the integrand
  --      vanishes on `Set.Ioc z 1`, so the integral equals
  --      `∫ x in Set.Ioc 0 z, x ^ (N - 1) * (z⁻¹ * C (x / z) * f z)`
  --      (`collinearKernel_of_lt`, plus a set-restriction lemma such as
  --      `MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero`, or `Set.indicator` and
  --      `MeasureTheory.setIntegral_indicator` with `Set.Ioc_inter_Ioc`).
  --   2. Substitute `x = z * u`. Via `intervalIntegral.integral_of_le` (both domains are `Ioc`
  --      with ordered endpoints) and `intervalIntegral.integral_comp_mul_left` for `z ≠ 0`, this
  --      is `z • ∫ u in Set.Ioc 0 1, (z * u) ^ (N - 1) * (z⁻¹ * C u * f z)`.
  --   3. Factor the complex power: `((z * u : ℝ) : ℂ) ^ (N - 1) = z ^ (N - 1) * u ^ (N - 1)` for
  --      `0 ≤ z`, `0 ≤ u` (`Complex.mul_cpow_ofReal_nonneg`, name unchecked). The explicit `z`
  --      from the substitution cancels the kernel's `z⁻¹` (`mul_inv_cancel₀ hz0.ne'`), which is
  --      the content of the theorem.
  --   4. Pull the constants `z ^ (N - 1) * f z` out of the `u`-integral
  --      (`MeasureTheory.integral_const_mul`), leaving `mellinDis C N`.
  -- `hC` is needed in step 2 only to know the substituted integrand is integrable, so that the
  -- change-of-variables lemma is not applied to a divergent integral; if the route above turns
  -- out not to need it, drop the hypothesis rather than leaving it unused.
  sorry

/-- **The Mellin convolution theorem.** On the strip where both transforms converge absolutely
and the two-variable integrand is jointly integrable, the Mellin transform of the collinear
convolution is the product of the transforms:
`M[C ⊗ f] (N) = M[C] (N) * M[f] (N)`.

This is the identity behind evolution in moment space: applied to the DGLAP splitting kernels it
turns the integro-differential evolution equation into an ordinary differential equation in the
scale for each `N`, with the anomalous dimensions `M[P] (N)` as coefficients. -/
@[sorryful]
theorem mellinDis_convolveAt (C f : ℝ → ℝ) (N : ℂ)
    (h : MellinConvolutionAssumptions C f N) :
    mellinDis (convolveAt (collinearKernel C) f) N = mellinDis C N * mellinDis f N := by
  rw [mellinDis_convolveAt_eq_iteratedIntegral]
  -- TODO(task/e1-mellin-convolution): `MeasureTheory.integral_integral_swap` takes
  -- `Integrable (Function.uncurry F) (μ.prod ν)`, which is exactly `h.jointIntegrable`; the name
  -- could not be checked against source at this pin.
  rw [MeasureTheory.integral_integral_swap h.jointIntegrable]
  have hinner : ∀ z ∈ Set.Ioc (0 : ℝ) 1,
      (∫ x in Set.Ioc (0 : ℝ) 1, mellinIntegrand C f N x z)
        = ((z : ℂ) ^ (N - 1) * (f z : ℂ)) * mellinDis C N :=
    fun z hz => integral_mellinIntegrand_of_mem C f N hz.1 hz.2 h.convC
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hinner,
    MeasureTheory.integral_mul_const]
  have hf : (∫ z in Set.Ioc (0 : ℝ) 1, (z : ℂ) ^ (N - 1) * (f z : ℂ)) = mellinDis f N := rfl
  rw [hf, mul_comm]

/-!

## E. Moment-space corollaries

-/

/-- The collinear convolution is commutative in moment space: `M[C ⊗ f] = M[f ⊗ C]`, whenever
both convolutions satisfy the hypotheses of the convolution theorem at `N`. (Commutativity of
`⊗` itself is a statement about the convolution before transforming and needs an injectivity
argument in `N`, which is not available here; see the module docstring on analyticity.) -/
@[sorryful]
theorem mellinDis_convolveAt_comm (C f : ℝ → ℝ) (N : ℂ)
    (h₁ : MellinConvolutionAssumptions C f N) (h₂ : MellinConvolutionAssumptions f C N) :
    mellinDis (convolveAt (collinearKernel C) f) N
      = mellinDis (convolveAt (collinearKernel f) C) N := by
  rw [mellinDis_convolveAt C f N h₁, mellinDis_convolveAt f C N h₂, mul_comm]

/-- **Natural moments multiply.** At integer index the convolution theorem is an identity between
real integrals, with no complex analysis in the statement:
`∫_{(0,1]} x ^ n (C ⊗ f) (x) dx = (∫_{(0,1]} u ^ n C u du) * (∫_{(0,1]} z ^ n f z dz)`.
This is the form used by the sum rules (`n = 0` for number, `n = 1` for momentum) and by DGLAP in
moment space. -/
@[sorryful]
theorem moment_convolveAt (C f : ℝ → ℝ) (n : ℕ)
    (h : MellinConvolutionAssumptions C f ((n : ℂ) + 1)) :
    (∫ x in Set.Ioc (0 : ℝ) 1, x ^ n * convolveAt (collinearKernel C) f x)
      = (∫ u in Set.Ioc (0 : ℝ) 1, u ^ n * C u) * ∫ z in Set.Ioc (0 : ℝ) 1, z ^ n * f z := by
  have h' := mellinDis_convolveAt C f ((n : ℂ) + 1) h
  rw [mellinDis_natCast_add_one_eq_ofReal, mellinDis_natCast_add_one_eq_ofReal,
    mellinDis_natCast_add_one_eq_ofReal] at h'
  exact_mod_cast h'

/-- The natural-moment convolution theorem in terms of the repository's `mellinMoment`, which is
the form the sum-rule and evolution interfaces consume. Note the index shift: `mellinMoment ... n`
appears against the weight `x ^ n`, i.e. at Mellin index `n + 1`. -/
@[sorryful]
theorem mellinMoment_convolveAt {Flavor : Type} (C : ℝ → ℝ)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor) (n : ℕ) (i : Flavor) (Q2 : ℝ)
    (h : MellinConvolutionAssumptions C (fun x => f i x Q2) ((n : ℂ) + 1)) :
    (∫ x in Set.Ioc (0 : ℝ) 1, x ^ n * convolveAt (collinearKernel C) (fun z => f i z Q2) x)
      = (∫ u in Set.Ioc (0 : ℝ) 1, u ^ n * C u)
        * Physlib.Particles.Parton.PDF.mellinMoment f n i Q2 := by
  rw [moment_convolveAt C (fun x => f i x Q2) n h]
  congr 1
  simp only [Physlib.Particles.Parton.PDF.mellinMoment]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

end Convolution
end Factorization
end QFT
end Physlib
