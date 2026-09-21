/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.GPD.Basic
/-!

# GPD Moments and Polynomiality Interfaces

This module defines Mellin moments for GPDs and a polynomiality interface,
with concrete low-order consequences.

## Conventions

* **Integration range.** Moments run over the full GPD support `x ∈ [-1, 1]`
  (see `Physlib.Particles.Parton.GPD.Basic`). The half-range integral `∫_0^1` is *not*
  a polynomial in `ξ`, so polynomiality cannot be stated with it.

* **Moment index.** Following `PDF.mellinMoment`, the integrand carries `x ^ n`, i.e.
  `mellinMomentH M n i ξ t = ∫_{-1}^{1} dx x^n H_i(x, ξ, t)`. The literature's *n*-th
  moment is `∫_{-1}^{1} dx x^{n-1} H` (Diehl, *Generalized parton distributions*,
  Phys. Rept. **388** (2003) 41, arXiv:hep-ph/0307382 — general reference; the primary source
  was not consulted directly, so no equation number is cited),
  so the literature index is `n + 1` in the notation used here. Two consequences of the
  shift, both visible in `PolynomialityAssumptions` below:
  - the polynomiality degree bound is `n + 1`, not `n`;
  - the D-term occupies the `ξ^(n+1)` coefficient, which is why the sum runs over
    `Finset.range (n + 2)` rather than `Finset.range (n + 1)`.

* **Skewness range.** Polynomiality is a statement about physical kinematics `|ξ| ≤ 1`;
  outside that range the `[-1, 1]` integral truncates the support of a model and no
  polynomial statement survives. The hypothesis is therefore carried explicitly.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace Particles
namespace Parton
namespace GPD

variable {Flavor : Type}

/-- Mellin moment of a bare GPD function over the full support `x ∈ [-1, 1]`.

The integrand is `x ^ n * H i x ξ t`; see the module docstring for the index convention. -/
def mellinMomentGpd (H : Gpd Flavor) (n : ℕ) (i : Flavor) (xi t : ℝ) : ℝ :=
  ∫ x in Set.Icc (-1 : ℝ) 1, x ^ n * H i x xi t

/-- Mellin moments of `H` over the full GPD support `x ∈ [-1, 1]`. -/
def mellinMomentH (M : Model Flavor) (n : ℕ) (i : Flavor) (xi t : ℝ) : ℝ :=
  mellinMomentGpd M.H n i xi t

/-- Mellin moments of `E` over the full GPD support `x ∈ [-1, 1]`. -/
def mellinMomentE (M : Model Flavor) (n : ℕ) (i : Flavor) (xi t : ℝ) : ℝ :=
  mellinMomentGpd M.E n i xi t

/-- Unfolding lemma for `mellinMomentH` as an explicit integral. -/
lemma mellinMomentH_eq_integral (M : Model Flavor) (n : ℕ) (i : Flavor) (xi t : ℝ) :
    mellinMomentH M n i xi t = ∫ x in Set.Icc (-1 : ℝ) 1, x ^ n * M.H i x xi t :=
  rfl

/-- Polynomiality schema for Mellin moments of `H`.

For physical skewness `|ξ| ≤ 1`, the moment `∫_{-1}^{1} dx x^n H` is a polynomial in `ξ`
of degree at most `n + 1` containing only even powers. The `ξ^(n+1)` coefficient is the
D-term contribution and is nonzero only for odd `n` (equivalently, for even literature
index `n + 1`).

This bundle is retained for models that are not built from a double distribution. For
models that are, `GPD.polynomialityAssumptionsOfDoubleDistribution` constructs it — but
**that bridge is not a discharge**: its `polynomial` field is
`GPD.mellinMomentGpd_ofDoubleDistribution`, which is a tagged `sorry`, so `#print axioms`
on the bridge reports `sorryAx` (verified at `b63a5fcc`). A reader deciding whether this
assumption is "handled" should read it as: handled *modulo* one open measure-theoretic
statement, and otherwise assumed. No unconditional discharge of this bundle exists
anywhere in the repository at present. -/
structure PolynomialityAssumptions (M : Model Flavor) : Type where
  /-- The coefficient of `ξ^k` in the `n`-th moment for flavor `i` at momentum transfer `t`. -/
  coeff : ℕ → Flavor → ℕ → ℝ → ℝ
  /-- Moments are *even* polynomials in `ξ`: odd coefficients vanish. -/
  coeff_eq_zero_of_odd : ∀ n i k t, Odd k → coeff n i k t = 0
  /-- The moment is the polynomial with those coefficients, for physical skewness. -/
  polynomial : ∀ n i xi t, |xi| ≤ 1 →
    mellinMomentH M n i xi t
      = ∑ k ∈ Finset.range (n + 2), coeff n i k t * xi ^ k

/-- Polynomiality makes every moment an even function of the skewness. -/
lemma mellinMomentH_neg_skewness
    (M : Model Flavor)
    (hPoly : PolynomialityAssumptions M)
    (n : ℕ) (i : Flavor) (xi t : ℝ) (hxi : |xi| ≤ 1) :
    mellinMomentH M n i (-xi) t = mellinMomentH M n i xi t := by
  have hneg : |(-xi)| ≤ 1 := by rwa [abs_neg]
  rw [hPoly.polynomial n i (-xi) t hneg, hPoly.polynomial n i xi t hxi]
  refine Finset.sum_congr rfl ?_
  intro k _
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_pow]
  · rw [hPoly.coeff_eq_zero_of_odd n i k t hk, zero_mul, zero_mul]

/-- First nontrivial polynomiality consequence: the zeroth moment is `ξ`-independent.

With the corrected degree bound the `n = 0` moment is `A + C ξ`, and it is the *evenness*
clause, not the degree bound, that kills the linear term. -/
lemma mellinMomentH_n0_eq_at_zero
    (M : Model Flavor)
    (hPoly : PolynomialityAssumptions M)
    (i : Flavor) (xi t : ℝ) (hxi : |xi| ≤ 1) :
    mellinMomentH M 0 i xi t = mellinMomentH M 0 i 0 t := by
  have hodd : hPoly.coeff 0 i 1 t = 0 := hPoly.coeff_eq_zero_of_odd 0 i 1 t odd_one
  have key : ∀ y : ℝ, |y| ≤ 1 → mellinMomentH M 0 i y t = hPoly.coeff 0 i 0 t := by
    intro y hy
    rw [hPoly.polynomial 0 i y t hy]
    simp [Finset.sum_range_succ, hodd]
  rw [key xi hxi, key 0 (by simp)]

end GPD
end Parton
end Particles
end Physlib
