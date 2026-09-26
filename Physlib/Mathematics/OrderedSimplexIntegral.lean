/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The ordered iterated integral of a product

For `f : ℝ → ℝ` and endpoints `t`, `T`, the `n`-fold integral of `f t₁ * ⋯ * f tₙ` over the
descending region `T > t₁ > ⋯ > tₙ > t` equals `(∫ s in t..T, f s) ^ n / n !`.

`orderedProdIntegral f T n t` is that region integral, written as an *iterated* interval
integral with the **smallest** variable outermost:

  `orderedProdIntegral f T 0       t = 1`
  `orderedProdIntegral f T (n + 1) t = ∫ x in t..T, f x * orderedProdIntegral f T n x`

Fixing the smallest coordinate at `x` leaves the remaining `n` coordinates ranging over the
same ordered region with lower endpoint `x`, which is exactly this recursion.  The main
result is `orderedProdIntegral_eq`.

## The proof, and why not symmetrization

The textbook argument is a symmetrization: the integrand is symmetric, the `n !` orderings
of the coordinates tile the cube `[t, T] ^ n` up to a measure-zero diagonal, so the ordered
region carries `1 / n !` of the cube integral.  That is correct, but as a formalization
target it needs almost-disjointness of `n !` permuted simplices, that they cover, and a
measure-preserving change of variables under each permutation — a composite that does not
exist ready-made in `Mathlib` at the pinned revision.

The route taken here is induction on `n` with the fundamental theorem of calculus, and it
needs none of that.  Write `F x = ∫ s in x..T, f s`.  Integrating out the smallest variable
turns the inductive hypothesis into `∫ x in t..T, f x * F x ^ n / n !`; since `F` is the
integral *up to* `T` its derivative is `-f`, so `x ↦ -F x ^ (n + 1) / (n + 1)` is an
antiderivative of `x ↦ f x * F x ^ n`, and FTC-2 collapses the integral to
`F t ^ (n + 1) / (n + 1)` because `F T = 0`.  Only `intervalIntegral`, the FTC pair and the
chain rule for `x ↦ F x ^ n` are used; there is no measure theory on the simplex, no
permutation argument and no almost-everywhere reasoning.

The iterated form is also the one an application usually wants, since a sequential sampler
of the ordered coordinates produces precisely this nesting.  Identifying it with the
integral of a product over the subset `{p : Fin n → ℝ | T > p 0 > ⋯ > p (n - 1) > t}` of
`ℝ ^ n` is a separate Fubini argument and is **not** proved here.

## Scope

Stated for `f : ℝ → ℝ` under `Continuous f`.  Continuity is used twice — for the derivative
of the primitive, and for interval integrability of the integrand at each stage — and could
be relaxed towards `IntervalIntegrable` at the cost of carrying integrability hypotheses
through the induction; that is not attempted here.

Nothing in this file is physics-specific: it is mathlib-shaped and upstreamable, and is kept
here only so that downstream files can use it now.  Upstreaming is handled separately, as
for this repository's su(N) material.
-/

@[expose] public section

namespace Physlib
namespace OrderedSimplex

open scoped Nat
open MeasureTheory intervalIntegral

/-- The integral of `f t₁ * ⋯ * f tₙ` over the descending region `T > t₁ > ⋯ > tₙ > t`,
written as an iterated interval integral with the smallest coordinate outermost.  The empty
product integrates to `1`. -/
noncomputable def orderedProdIntegral (f : ℝ → ℝ) (T : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, t => ∫ x in t..T, f x * orderedProdIntegral f T n x

variable {f : ℝ → ℝ}

/-- The zero-fold ordered integral is the empty product. -/
@[simp]
lemma orderedProdIntegral_zero (f : ℝ → ℝ) (T t : ℝ) : orderedProdIntegral f T 0 t = 1 := by
  simp only [orderedProdIntegral]

/-- Peeling off the smallest coordinate: fixing it at `x` leaves the ordered integral of one
fewer coordinate over the region with lower endpoint `x`. -/
lemma orderedProdIntegral_succ (f : ℝ → ℝ) (T : ℝ) (n : ℕ) (t : ℝ) :
    orderedProdIntegral f T (n + 1) t = ∫ x in t..T, f x * orderedProdIntegral f T n x := by
  simp only [orderedProdIntegral]

/-- The primitive `u ↦ ∫ s in u..T, f s` of a continuous `f`, differentiated in its *lower*
limit: the derivative is `-f`, which is what makes the induction below telescope. -/
lemma hasDerivAt_integral_lower (hf : Continuous f) (T x : ℝ) :
    HasDerivAt (fun u => ∫ s in u..T, f s) (-f x) x :=
  integral_hasDerivAt_left (hf.intervalIntegrable _ _)
    (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt

/-- The primitive of a continuous function, as a function of its lower limit, is continuous.
This is what makes each stage of the induction interval integrable. -/
lemma continuous_integral_lower (hf : Continuous f) (T : ℝ) :
    Continuous fun u => ∫ s in u..T, f s :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_integral_lower hf T x).continuousAt

/-- The inductive step, by FTC-2: `x ↦ -(∫ s in x..T, f s) ^ (n + 1) / (n + 1)` is an
antiderivative of `x ↦ f x * (∫ s in x..T, f s) ^ n`, and it vanishes at `T`. -/
lemma integral_mul_integral_pow (hf : Continuous f) (T t : ℝ) (n : ℕ) :
    (∫ x in t..T, f x * (∫ s in x..T, f s) ^ n) = (∫ s in t..T, f s) ^ (n + 1) / (n + 1) := by
  have hne : (-((n : ℝ) + 1)) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have key : ∀ x : ℝ, HasDerivAt
      (fun u : ℝ => (∫ s in u..T, f s) ^ (n + 1) / (-((n : ℝ) + 1)))
      (f x * (∫ s in x..T, f s) ^ n) x := by
    intro x
    have hp : HasDerivAt (fun u : ℝ => (∫ s in u..T, f s) ^ (n + 1))
        (((n + 1 : ℕ) : ℝ) * (∫ s in x..T, f s) ^ (n + 1 - 1) * -f x) x :=
      (hasDerivAt_integral_lower hf T x).fun_pow (n + 1)
    have h := hp.div_const (-((n : ℝ) + 1))
    have heq : ((n + 1 : ℕ) : ℝ) * (∫ s in x..T, f s) ^ (n + 1 - 1) * -f x / (-((n : ℝ) + 1))
        = f x * (∫ s in x..T, f s) ^ n := by
      rw [div_eq_iff hne]
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
    rw [heq] at h
    exact h
  have hint : IntervalIntegrable (fun x : ℝ => f x * (∫ s in x..T, f s) ^ n) volume t T :=
    (hf.mul ((continuous_integral_lower hf T).pow n)).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => key x) hint]
  simp only [integral_same, zero_pow n.succ_ne_zero, zero_div, div_neg, neg_zero, zero_sub,
    neg_neg]

/-- **The ordered-simplex identity.** The `n`-fold integral of `f t₁ * ⋯ * f tₙ` over the
descending region `T > t₁ > ⋯ > tₙ > t` is `1 / n !` times the `n`-th power of the single
integral `∫ s in t..T, f s`.

No inequality between `t` and `T` is required: `intervalIntegral` is signed, and both sides
change sign together when the endpoints are swapped. -/
theorem orderedProdIntegral_eq (hf : Continuous f) (T : ℝ) (n : ℕ) (t : ℝ) :
    orderedProdIntegral f T n t = (∫ s in t..T, f s) ^ n / n ! := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [orderedProdIntegral_succ]
    have hrw : ∀ x : ℝ,
        f x * orderedProdIntegral f T n x = f x * (∫ s in x..T, f s) ^ n / (n ! : ℝ) := by
      intro x
      rw [ih x]
      ring
    simp_rw [hrw]
    rw [intervalIntegral.integral_div, integral_mul_integral_pow hf, Nat.factorial_succ,
      div_div]
    push_cast
    ring

end OrderedSimplex
end Physlib
