/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.GPD.Moments
public import Physlib.Particles.Parton.GPD.DoubleDistribution
public import Physlib.Meta.Linters.Sorry
/-!

# Polynomiality of GPD Moments from the Double-Distribution Representation

This module derives polynomiality — that the `x`-moments of a GPD are *even* polynomials
in the skewness `ξ`, with the top coefficient the D-term — for a GPD built from a double
distribution, instead of assuming it.

## Statement

With the moment convention of `Physlib.Particles.Parton.GPD.Moments` (integrand `x ^ n`,
integration over the full support `[-1, 1]`, literature index `n + 1`):

```text
∫_{-1}^{1} dx x^n H(x, ξ, t)
  = Σ_{k = 0}^{n} C(n, k) ξ^k ∫∫ dβ dα β^(n-k) α^k F(β, α, t)   +   ξ^(n+1) ∫ du u^n D(u, t)
```

for `|ξ| ≤ 1`. The derivation is: substitute the one-dimensional form of the
double-distribution representation, change variables from `(x, β)` to `(β, α)` with
`x = β + αξ` (Jacobian `|ξ|`, cancelling the `1/|ξ|` prefactor), exchange the order of
integration, expand `(β + αξ)^n` by the binomial theorem, and read off the coefficient of
`ξ^k`. The D-term piece is a one-dimensional rescaling, `x = ξ u`.

Two structural facts then give the physics content:

* `DoubleDistribution.alphaSymm` kills every odd-`k` term, so the polynomial is even
  (`momentCoeff_eq_zero_of_odd`);
* `DTerm.odd` kills `∫ du u^n D` for even `n`, so the `ξ^(n+1)` slot is occupied only when
  `n + 1` — the literature index — is even. That slot is the D-term
  (`momentPolynomial_coeff_top`).

## References

* D. Müller, D. Robaschik, B. Geyer *et al.*, Fortschr. Phys. **42** (1994) 101.
* A. V. Radyushkin, *Nonforward parton distributions*, Phys. Rev. D **56** (1997) 5524.
* X. Ji, *Off-forward parton distributions*, J. Phys. G **24** (1998) 1181.
* M. Diehl, *Generalized parton distributions*, Phys. Rept. **388** (2003) 41, §4.3.
* A. V. Belitsky and A. V. Radyushkin, Phys. Rept. **418** (2005) 1, §3.

## Status

The algebraic and polynomial-bookkeeping content is proved, including both parity inputs
(`ddMoment_eq_zero_of_odd` and `dtMoment_eq_zero_of_even`). Exactly **one** statement is
left as a marked `sorry`: the Fubini/change-of-variables core
`mellinMomentGpd_ofDoubleDistribution`, whose `TODO` names the intended argument.

Four declarations inherit that `sorry` and are tagged accordingly:
`mellinMomentGpd_polynomial`, `mellinMomentH_polynomial`,
`polynomialityAssumptionsOfDoubleDistribution` and
`mellinMomentH_n0_eq_at_zero_ofDoubleDistribution`. Under `#print axioms` each of the five
reports `sorryAx`, while every other declaration in this module reports only
`[propext, Classical.choice, Quot.sound]`.

**Consequence for the assumption bundle.** `polynomialityAssumptionsOfDoubleDistribution`
is advertised in `GPD.Moments` as discharging `PolynomialityAssumptions`, and it is the
only bridge offered. Because it rests on the `sorry` above, that discharge is not real at
the kernel level: "polynomiality holds for double-distribution models" is currently
*assumed*, in the same sense that the bundle itself assumes it, rather than established.
The bridge is retained because its reduction to a single analytic statement is genuine
content, but it must not be read as retiring the bundle.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace Particles
namespace Parton
namespace GPD

variable {Flavor : Type}

/-- The `(β, α)` monomial moment `∫∫ dβ dα β^m α^k F(β, α, t)` of a double distribution.

These are the form factors `A_{n,k}(t)` of the polynomiality expansion, up to the binomial
factor supplied by `momentCoeff`. -/
def ddMoment (dd : DoubleDistribution Flavor) (i : Flavor) (m k : ℕ) (t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, p.1 ^ m * p.2 ^ k * dd.F i p.1 p.2 t

/-- The `m`-th monomial moment `∫ du u^m D(u, t)` of a D-term. -/
def dtMoment (dt : DTerm Flavor) (i : Flavor) (m : ℕ) (t : ℝ) : ℝ :=
  ∫ u : ℝ, u ^ m * dt.D i u t

/-- Odd `α`-moments of a double distribution vanish.

This is the formal content of the `α`-symmetry of `F`, and it is what makes the moment
polynomial *even* in `ξ`. -/
lemma ddMoment_eq_zero_of_odd (dd : DoubleDistribution Flavor) (i : Flavor) (m k : ℕ)
    (t : ℝ) (hk : Odd k) :
    ddMoment dd i m k t = 0 := by
  -- the reflection `(β, α) ↦ (β, -α)` preserves `volume` on `ℝ × ℝ`
  have hmp : MeasureTheory.MeasurePreserving
      (⇑((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)))
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) MeasureTheory.volume := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.MeasurePreserving.id _).prod
      (MeasureTheory.Measure.measurePreserving_neg _)
  -- composing the integrand with it multiplies it by `(-1)^k = -1`
  have hflip : ∀ p : ℝ × ℝ,
      p.1 ^ m * (-p.2) ^ k * dd.F i p.1 (-p.2) t
        = -(p.1 ^ m * p.2 ^ k * dd.F i p.1 p.2 t) := by
    intro p
    rw [hk.neg_pow, dd.alphaSymm]
    ring
  have key : ddMoment dd i m k t = -ddMoment dd i m k t := by
    calc ddMoment dd i m k t
        = ∫ p : ℝ × ℝ, p.1 ^ m * (-p.2) ^ k * dd.F i p.1 (-p.2) t :=
          (hmp.integral_comp' (fun p : ℝ × ℝ => p.1 ^ m * p.2 ^ k * dd.F i p.1 p.2 t)).symm
      _ = ∫ p : ℝ × ℝ, -(p.1 ^ m * p.2 ^ k * dd.F i p.1 p.2 t) := by simp_rw [hflip]
      _ = -ddMoment dd i m k t := by rw [MeasureTheory.integral_neg]; rfl
  linarith

/-- Even monomial moments of a D-term vanish, by its oddness in `u`.

This is what confines the D-term to the moments of even literature index. -/
lemma dtMoment_eq_zero_of_even (dt : DTerm Flavor) (i : Flavor) (m : ℕ) (t : ℝ)
    (hm : Even m) :
    dtMoment dt i m t = 0 := by
  -- there is no dedicated odd-function-integral lemma at this pin, so this goes through
  -- negation being measure preserving, exactly as in `ddMoment_eq_zero_of_odd`
  have hmp : MeasureTheory.MeasurePreserving (⇑(MeasurableEquiv.neg ℝ))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) MeasureTheory.volume :=
    MeasureTheory.Measure.measurePreserving_neg _
  have hflip : ∀ u : ℝ, (-u) ^ m * dt.D i (-u) t = -(u ^ m * dt.D i u t) := by
    intro u
    rw [hm.neg_pow, dt.odd]
    ring
  have key : dtMoment dt i m t = -dtMoment dt i m t := by
    calc dtMoment dt i m t
        = ∫ u : ℝ, (-u) ^ m * dt.D i (-u) t :=
          (hmp.integral_comp' (fun u : ℝ => u ^ m * dt.D i u t)).symm
      _ = ∫ u : ℝ, -(u ^ m * dt.D i u t) := by simp_rw [hflip]
      _ = -dtMoment dt i m t := by rw [MeasureTheory.integral_neg]; rfl
  linarith

/-- The coefficient of `ξ^k` in the `n`-th moment of a GPD built from `dd` and `dt`.

For `k ≤ n` it is the binomial-weighted `(β, α)` moment of the double distribution; the
single extra slot `k = n + 1` carries the D-term. -/
def momentCoeff (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (k : ℕ) (t : ℝ) : ℝ :=
  if k ≤ n then (n.choose k : ℝ) * ddMoment dd i (n - k) k t
  else if k = n + 1 then dtMoment dt i n t
  else 0

/-- Odd coefficients of the moment polynomial vanish: moments are even in `ξ`. -/
lemma momentCoeff_eq_zero_of_odd (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (k : ℕ) (t : ℝ) (hk : Odd k) :
    momentCoeff dd dt n i k t = 0 := by
  rw [momentCoeff]
  split_ifs with h1 h2
  · rw [ddMoment_eq_zero_of_odd dd i (n - k) k t hk, mul_zero]
  · have hodd : Odd (n + 1) := h2 ▸ hk
    have hn : Even n := by
      rcases Nat.even_or_odd n with h | h
      · exact h
      · exfalso
        obtain ⟨j, hj⟩ := h
        obtain ⟨l, hl⟩ := hodd
        omega
    exact dtMoment_eq_zero_of_even dt i n t hn
  · rfl

/-- The moment polynomial of a GPD built from a double distribution and a D-term. -/
def momentPolynomial (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 2), Polynomial.C (momentCoeff dd dt n i k t) * Polynomial.X ^ k

/-- The coefficients of `momentPolynomial` are exactly `momentCoeff`. -/
lemma momentPolynomial_coeff (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) (k : ℕ) :
    (momentPolynomial dd dt n i t).coeff k = momentCoeff dd dt n i k t := by
  rw [momentPolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (n + 2)) k (fun j => momentCoeff dd dt n i j t)]
  by_cases hk : k < n + 2
  · rw [if_pos (Finset.mem_range.mpr hk)]
  · rw [if_neg (fun hmem => hk (Finset.mem_range.mp hmem))]
    rw [momentCoeff, if_neg (by omega : ¬ k ≤ n), if_neg (by omega : k ≠ n + 1)]

/-- The moment polynomial has degree at most `n + 1`.

The bound is `n + 1` rather than `n` because the repository's moment index is the
literature index minus one; see the `GPD.Moments` module docstring. -/
lemma momentPolynomial_natDegree_le (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) :
    (momentPolynomial dd dt n i t).natDegree ≤ n + 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [momentPolynomial_coeff, momentCoeff, if_neg (by omega : ¬ m ≤ n),
    if_neg (by omega : m ≠ n + 1)]

/-- Evaluating the moment polynomial is summing the coefficients against powers of `ξ`. -/
lemma momentPolynomial_eval (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) (xi : ℝ) :
    (momentPolynomial dd dt n i t).eval xi
      = ∑ k ∈ Finset.range (n + 2), momentCoeff dd dt n i k t * xi ^ k := by
  simp [momentPolynomial, Polynomial.eval_finsetSum]

/-- **The analytic core.** The `n`-th moment of a GPD built from a double distribution and
a D-term is the explicit sum of `(β, α)` moments and the D-term moment, for physical
skewness `|ξ| ≤ 1`. -/
@[sorryful]
theorem mellinMomentGpd_ofDoubleDistribution
    (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (xi t : ℝ) (hxi : |xi| ≤ 1) :
    mellinMomentGpd (gpdOfDoubleDistribution dd dt) n i xi t
      = ∑ k ∈ Finset.range (n + 2), momentCoeff dd dt n i k t * xi ^ k := by
  -- TODO(task/p3-gpd-polynomiality): this is the measure-theoretic heart of the target and
  -- is left open. Intended argument, in five steps:
  --   1. Replace `∫ x in Set.Icc (-1) 1` by `∫ x` over all of `ℝ`. The integrand vanishes
  --      off `[-1, 1]` by `gpdOfDoubleDistribution_eq_zero_of_one_lt_abs` (which is proved,
  --      and is where `hxi` is used). The lemma is
  --      `MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero`, CONFIRMED present
  --      at this pin (Integral/Bochner/Set.lean:489), taking `(h : ∀ x, x ∉ s → f x = 0)`.
  --   2. Split the integral over the two summands of `gpdOfDoubleDistribution`. This needs
  --      integrability of each piece separately; the `ξ ≠ 0` branch should get it from
  --      `dd.momentIntegrable` and `dt.momentIntegrable` after the change of variables of
  --      step 3, so the split is best done after, or via `MeasureTheory.integral_add` with
  --      integrability transported backwards.
  --   3. For the `F` piece, change variables `(x, β) ↦ (β, α)` with `α = (x - β)/ξ`. The
  --      Jacobian `|ξ|` cancels the `(|ξ|)⁻¹` prefactor. Then exchange the order of
  --      integration with `MeasureTheory.integral_integral_swap`, using `dd.integrable`
  --      and `dd.momentIntegrable`, to reach `∫∫ dβ dα (β + αξ)^n F(β, α, t)`.
  --   4. Expand `(β + αξ)^n` with `add_pow` and integrate term by term
  --      (`MeasureTheory.integral_finset_sum`), giving
  --      `∑ k ∈ range (n+1), (n.choose k) * ξ^k * ddMoment dd i (n-k) k t`.
  --   5. For the D-term piece, rescale `x = ξ u`; the Lebesgue Jacobian `|ξ|` times the
  --      prefactor `ξ/|ξ|` gives `ξ`, and `x^n = ξ^n u^n`, so the piece is
  --      `ξ^(n+1) * dtMoment dt i n t`, which is the `k = n + 1` term.
  --   The `ξ = 0` branch must be handled separately: there the D-term is absent and only
  --   the `k = 0` term survives, since `momentCoeff … 0 …` is `ddMoment dd i n 0 t` and
  --   `∫ x x^n ∫ α F(x, α, t)` is that same double integral by Fubini.
  --
  -- Status (2026-09-19). The two parity inputs this consumes, `ddMoment_eq_zero_of_odd` and
  -- `dtMoment_eq_zero_of_even`, are now PROVED, so the prerequisites are in place. Every
  -- name the plan needs has been checked against the pinned mathlib and exists:
  -- `setIntegral_eq_integral_of_forall_compl_eq_zero` (step 1, above),
  -- `integral_image_eq_integral_abs_det_fderiv_smul` (step 3's Jacobian change of
  -- variables, Function/Jacobian.lean:1213), `MeasureTheory.integral_integral_swap`
  -- (step 3's exchange, Integral/Prod.lean:482) and `add_pow` (step 4).
  --
  -- It is nevertheless left open deliberately, and the honest reason is effort rather than
  -- a missing ingredient: step 3 is a two-dimensional change of variables with a Jacobian
  -- whose integrability hypotheses must be transported across the substitution before
  -- Fubini can be applied, step 4 integrates a binomial expansion term by term, and the
  -- `ξ = 0` degenerate branch is a separate argument. That is a project on the scale of a
  -- PR of its own, not a proof step, and attempting it inside a sorry-reduction pass would
  -- have meant claiming progress without a compiler behind it. The five other sorries in
  -- this pass were each discharged and verified; this one is reported as open.
  sorry

/-- **Polynomiality.** For a GPD built from a double distribution and a D-term, the `n`-th
`x`-moment is, at physical skewness, an even polynomial in `ξ` of degree at most `n + 1`.

Inherits the `sorry` of `mellinMomentGpd_ofDoubleDistribution`, which supplies the
`polynomial` clause; the evenness clause and the degree bound are proved outright. -/
@[sorryful]
theorem mellinMomentGpd_polynomial
    (dd : DoubleDistribution Flavor) (dt : DTerm Flavor) (n : ℕ) (i : Flavor) (t : ℝ) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ n + 1 ∧ (∀ k, Odd k → p.coeff k = 0) ∧
      ∀ xi, |xi| ≤ 1 →
        mellinMomentGpd (gpdOfDoubleDistribution dd dt) n i xi t = p.eval xi := by
  refine ⟨momentPolynomial dd dt n i t, momentPolynomial_natDegree_le dd dt n i t, ?_, ?_⟩
  · intro k hk
    rw [momentPolynomial_coeff]
    exact momentCoeff_eq_zero_of_odd dd dt n i k t hk
  · intro xi hxi
    rw [momentPolynomial_eval]
    exact mellinMomentGpd_ofDoubleDistribution dd dt n i xi t hxi

/-- Polynomiality for a full GPD model built from double distributions.

Inherits the `sorry` of `mellinMomentGpd_ofDoubleDistribution` through
`mellinMomentGpd_polynomial`. -/
@[sorryful]
theorem mellinMomentH_polynomial
    (ddH ddE : DoubleDistribution Flavor) (dtH dtE : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ n + 1 ∧ (∀ k, Odd k → p.coeff k = 0) ∧
      ∀ xi, |xi| ≤ 1 →
        mellinMomentH (Model.ofDoubleDistribution ddH dtH ddE dtE) n i xi t = p.eval xi := by
  exact mellinMomentGpd_polynomial ddH dtH n i t

/-- Below the top slot the coefficients are pure double-distribution form factors. -/
lemma momentPolynomial_coeff_of_le (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) (k : ℕ) (hk : k ≤ n) :
    (momentPolynomial dd dt n i t).coeff k
      = (n.choose k : ℝ) * ddMoment dd i (n - k) k t := by
  rw [momentPolynomial_coeff, momentCoeff, if_pos hk]

/-- **The D-term is the top coefficient.** The `ξ^(n+1)` coefficient of the moment
polynomial is exactly the `n`-th moment of the D-term, with no double-distribution
contribution. In literature indexing this is the `ξ^n` coefficient of the `n`-th moment,
the `C_n(t)` that carries the pressure and shear-force interpretation of the nucleon
(see e.g. arXiv:2501.16257). -/
lemma momentPolynomial_coeff_top (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) :
    (momentPolynomial dd dt n i t).coeff (n + 1) = dtMoment dt i n t := by
  rw [momentPolynomial_coeff, momentCoeff, if_neg (by omega : ¬ n + 1 ≤ n), if_pos rfl]

/-- The D-term slot is empty for even `n`, i.e. for odd literature index `n + 1`. -/
lemma momentPolynomial_coeff_top_eq_zero_of_even (dd : DoubleDistribution Flavor)
    (dt : DTerm Flavor) (n : ℕ) (i : Flavor) (t : ℝ) (hn : Even n) :
    (momentPolynomial dd dt n i t).coeff (n + 1) = 0 := by
  rw [momentPolynomial_coeff_top]
  exact dtMoment_eq_zero_of_even dt i n t hn

/-- **The bridge to the assumption bundle — not yet a discharge.** Any GPD model built
from double distributions satisfies `PolynomialityAssumptions`, *conditionally on*
`mellinMomentGpd_ofDoubleDistribution`, which is a tagged `sorry`.

The `coeff` and `coeff_eq_zero_of_odd` fields are supplied by proved results; the
`polynomial` field is exactly the open analytic core. So what this definition achieves is
a reduction — the whole bundle is now pinned to one measure-theoretic statement instead of
three — and **not** the retirement of the bundle. `#print axioms` on it reports `sorryAx`
Until that `sorry` is closed, a caller who
obtains `PolynomialityAssumptions` this way has assumed polynomiality, not proved it. -/
@[sorryful]
def polynomialityAssumptionsOfDoubleDistribution
    (ddH ddE : DoubleDistribution Flavor) (dtH dtE : DTerm Flavor) :
    PolynomialityAssumptions (Model.ofDoubleDistribution ddH dtH ddE dtE) where
  coeff := fun n i k t => momentCoeff ddH dtH n i k t
  coeff_eq_zero_of_odd := fun n i k t hk => momentCoeff_eq_zero_of_odd ddH dtH n i k t hk
  polynomial := fun n i xi t hxi => by
    exact mellinMomentGpd_ofDoubleDistribution ddH dtH n i xi t hxi

/-- The `n = 0` corollary of `GPD.Moments`, with its hypothesis supplied by the bridge
above rather than by the caller.

Since that bridge rests on `mellinMomentGpd_ofDoubleDistribution`, so does this: the
hypothesis has been *relocated*, not discharged. -/
@[sorryful]
lemma mellinMomentH_n0_eq_at_zero_ofDoubleDistribution
    (ddH ddE : DoubleDistribution Flavor) (dtH dtE : DTerm Flavor)
    (i : Flavor) (xi t : ℝ) (hxi : |xi| ≤ 1) :
    mellinMomentH (Model.ofDoubleDistribution ddH dtH ddE dtE) 0 i xi t
      = mellinMomentH (Model.ofDoubleDistribution ddH dtH ddE dtE) 0 i 0 t :=
  mellinMomentH_n0_eq_at_zero _
    (polynomialityAssumptionsOfDoubleDistribution ddH ddE dtH dtE) i xi t hxi

end GPD
end Parton
end Particles
end Physlib
