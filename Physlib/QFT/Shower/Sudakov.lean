/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Sudakov form factors and the veto algorithm

The no-emission probability of a parton shower, and the theorem that makes the veto
algorithm legitimate.

## The problem the veto algorithm solves

A shower emits at ordered scale `t` with density `K t * Δ_K t`, where

  `Δ_K t = exp (-∫_t^T K)`

is the **Sudakov form factor** — the probability of no emission between `t` and the
starting scale `T`.  Sampling that density directly means inverting `Δ_K`, which for a
realistic splitting kernel has no closed form.

The veto algorithm avoids the inversion.  Pick an overestimate `G ≥ K` whose Sudakov *can*
be inverted, propose a scale from the `G`-density, and accept it with probability
`K t / G t`.  On rejection, **continue downward from the rejected scale** rather than
starting over.  The standard claim is that this reproduces the `K`-density *exactly*, not
approximately — the overestimate introduces no bias, and `G` may be as crude as one likes
at the cost only of efficiency.

Standard references assert this and verify it by the calculation below; it is the kind of
claim a formalization is well suited to pin down.

## What is proved here, and what is not

Summing over the number of rejections, the density of accepting at `t` after exactly `n`
rejections is

  `K t * exp (-∫_t^T G) * (1/n!) * (∫_t^T (G - K))^n`,

and the algorithm's total density is the sum over `n`.  **`vetoSeries_eq_exp_neg` proves
that this sum is exactly `exp (-∫_t^T K)`** — the veto chain reproduces the Sudakov factor
it is meant to, with no hypotheses beyond `a` and `b` being real numbers.  That identity is
the whole content of the claim, and `sudakov_veto_eq` and `vetoDensity_eq` state it in the
shower's own vocabulary.

**Not proved: that the algorithm's output law equals that series.** Getting there needs one
further step, worth naming precisely rather than leaving vague. The per-term formula above
comes from an *ordered* `n`-fold integral,

  `∫_{T > t₁ > ... > tₙ > t} ∏ᵢ (G - K) tᵢ dt₁ ... dtₙ = (1/n!) (∫_t^T (G - K))^n`,

which holds because the integrand is symmetric and the `n!` orderings of the simplex
partition the cube.  That symmetrization lemma is the missing piece.  It is a statement of
integral geometry with no physics in it, it is not in `Mathlib` at the pinned revision as
far as a search shows, and proving it is a self-contained project of its own.  Until it
exists, the chain from "the algorithm" to "the series" is arithmetic done on paper, and
only the series-to-Sudakov half is machine-checked.

Everything here is real-valued.  The executable shower is a `Float` transcription and is
not connected to these theorems by any proof; see the generator plan for why that bridge is
deliberately not attempted.
-/

@[expose] public section

namespace Physlib
namespace QFT
namespace Shower

open scoped Nat

/-- `Real.exp` as its defining series, in the form the veto sum needs.

`Mathlib` states this for a general normed algebra (`NormedSpace.exp_eq_tsum_div`) and
separately identifies `Real.exp` with it (`Real.exp_eq_exp_ℝ`); this is the composition,
specialized to the reals. -/
lemma real_exp_eq_tsum (x : ℝ) : Real.exp x = ∑' n : ℕ, x ^ n / n ! := by
  rw [Real.exp_eq_exp_ℝ]
  exact congrFun NormedSpace.exp_eq_tsum_div x

/-- The weight of the veto chain that rejects exactly `n` proposals, as a function of the
integrated overestimate `b` and the integrated excess `d`.

The `n!` is the symmetry factor of the ordered rejection scales; see the module docstring
for the integral identity it comes from, which is the step not proved here. -/
noncomputable def vetoWeight (b d : ℝ) (n : ℕ) : ℝ := d ^ n / n ! * Real.exp (-b)

/-- **The veto identity.** Summing the veto chain over every number of rejections gives
exactly the no-emission factor of the *true* kernel, not of the overestimate.

This is why an overestimated splitting kernel introduces no bias: the `exp (-b)` carried by
the overestimate and the `exp (b - a)` resummed out of the rejections cancel identically to
`exp (-a)`.  Here `a` is the integrated true kernel and `b` the integrated overestimate.
The statement needs no inequality between them. -/
theorem vetoSeries_eq_exp_neg (a b : ℝ) :
    ∑' n : ℕ, vetoWeight b (b - a) n = Real.exp (-a) := by
  unfold vetoWeight
  rw [tsum_mul_right, ← real_exp_eq_tsum, ← Real.exp_add]
  ring_nf

/-- The Sudakov form factor of kernel `K` between `t` and `T`: the probability of no
emission in that range. -/
noncomputable def sudakov (K : ℝ → ℝ) (t T : ℝ) : ℝ :=
  Real.exp (-(∫ s in t..T, K s))

/-- The Sudakov form factor is strictly positive, for any kernel whatsoever.

A no-emission probability never vanishes, which is why a shower terminates rather than
emitting forever. -/
lemma sudakov_pos (K : ℝ → ℝ) (t T : ℝ) : 0 < sudakov K t T :=
  Real.exp_pos _

/-- At the starting scale nothing can have been emitted yet. -/
@[simp]
lemma sudakov_self (K : ℝ → ℝ) (T : ℝ) : sudakov K T T = 1 := by
  simp [sudakov]

/-- A non-negative integrated kernel gives a Sudakov factor that is a probability.

Stated in terms of the integral rather than of `K` pointwise, so that no integrability
hypothesis is needed: whatever the integral evaluates to, if it is non-negative the factor
is at most one. -/
lemma sudakov_le_one {K : ℝ → ℝ} {t T : ℝ} (h : 0 ≤ ∫ s in t..T, K s) :
    sudakov K t T ≤ 1 := by
  rw [sudakov, Real.exp_le_one_iff]
  linarith

/-- The veto identity in the shower's own vocabulary: the veto chain built from the
overestimate `G` sums to the Sudakov factor of the true kernel `K`. -/
theorem sudakov_veto_eq (K G : ℝ → ℝ) (t T : ℝ) :
    ∑' n : ℕ, vetoWeight (∫ s in t..T, G s)
        ((∫ s in t..T, G s) - ∫ s in t..T, K s) n = sudakov K t T :=
  vetoSeries_eq_exp_neg _ _

/-- The emission density the veto algorithm realizes at the point of acceptance.

Multiplying the series by the true kernel gives `K t * Δ_K t`, the density the shower is
supposed to sample.  The overestimate `G` has dropped out entirely; it survives only in the
efficiency. -/
theorem vetoDensity_eq (K G : ℝ → ℝ) (t T : ℝ) :
    K t * ∑' n : ℕ, vetoWeight (∫ s in t..T, G s)
        ((∫ s in t..T, G s) - ∫ s in t..T, K s) n = K t * sudakov K t T := by
  rw [sudakov_veto_eq]

/-- The zero-rejection term is the plain overestimate Sudakov, as it must be: with no
rejections the veto algorithm is direct sampling from `G`. -/
@[simp]
lemma vetoWeight_zero (b d : ℝ) : vetoWeight b d 0 = Real.exp (-b) := by
  simp [vetoWeight]

/-- Every veto term is non-negative when the overestimate dominates, so the series is a
genuine decomposition of the Sudakov factor by rejection count rather than a cancellation
between terms of opposite sign. -/
lemma vetoWeight_nonneg {b d : ℝ} (hd : 0 ≤ d) (n : ℕ) : 0 ≤ vetoWeight b d n := by
  unfold vetoWeight
  positivity

/-- The veto series converges, which lets `vetoSeries_eq_exp_neg` be read as a statement
about a sum of probabilities rather than only as a formal identity. -/
lemma vetoWeight_summable (b d : ℝ) : Summable (vetoWeight b d) := by
  unfold vetoWeight
  exact (Real.summable_pow_div_factorial d).mul_right _

end Shower
end QFT
end Physlib
