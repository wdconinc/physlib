/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.PDF.Basic
/-!

# Positivity of MS-bar Parton Distributions

Parton distributions in a physical scheme are cross sections and are non-negative. In the
MS-bar scheme they are not cross sections, and whether they inherit non-negativity is
scheme-dependent and contested; the contested part is the *domain of validity* rather
than the algebra.

This module states the conditional and then answers the question the literature is
circling — what is the weakest hypothesis that makes the conclusion follow — with three
proved results rather than with a new interface.

## The finding

1. `msbar_nonneg_iff_correction_dominated`. Given only that the scheme change subtracts a
   correction, non-negativity of the MS-bar distribution on a region is **equivalent** to
   the correction being dominated by the physical distribution there, pointwise. There is
   therefore no weaker sufficient hypothesis of the form "the correction is bounded":
   `correction_dominated` is not a sufficient condition that happens to work, it is the
   conclusion rewritten.

2. `uniform_bound_insufficient`. No *absolute* bound on the correction — no bound of the
   form `|Δ| ≤ ε`, at any order in the coupling, with any coefficient — implies
   non-negativity. The counterexample is explicit and lives at small `x`, where the
   physical distribution is smaller than any fixed `ε`.

3. `correction_dominated_of_lower_bound`. What *does* work is a hypothesis about the
   physical distribution, not about the correction: if the physical distribution is
   bounded below by `fmin` on the region and the correction is bounded by `a * Cmax` with
   `a * Cmax ≤ fmin`, the conclusion follows. And by
   `coupling_bound_degenerate_at_zero`, that hypothesis degenerates the moment `fmin`
   reaches zero.

Read together: MS-bar positivity is a statement about how far the physical distribution
stays from zero on the region, not about how small the perturbative correction is. It
therefore fails exactly where the distribution is small — at small `x` and as `x → 1` —
which is where the argument in the literature is located. A perturbative-smallness
hypothesis alone cannot deliver it.

## What is not claimed

Nothing here computes the scheme-change correction, and nothing here decides the physics
question. `scheme_change` records that the MS-bar distribution differs from a physical
one by a subtraction; which physical scheme, and what the subtraction is at a given order,
are inputs. The Soffer bound and the leading-order positivity statements live elsewhere
(see `Physlib.Particles.Parton.PDF.Basic` for the `nonneg` field these results are about).

Note also that `PDF.Assumptions.nonneg` quantifies over the whole interval `0 ≤ x ≤ 1`.
Nothing below discharges it: every statement here is restricted to a
`PerturbativeRegion`, and by item 2 the unrestricted field is not available from a
perturbative argument. That gap is the content, not an omission.

## References

* arXiv:2308.00025, *On the positivity of MS-bar parton distributions*.
* arXiv:2405.08643, *On the positivity of MS-bar distributions*.
* J. Soffer, Phys. Rev. Lett. **74** (1995) 1292 (arXiv:hep-ph/9409254), for the
  leading-twist bounds that a scheme change must be checked against.

Bibliographic data for the two recent preprints is taken from the task documentation of
`task/frontier-open-targets`; the primary sources were not consulted directly when this
file was written, and no equation is attributed to them.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace Particles
namespace Parton
namespace PDF

variable {Flavor : Type}

/-!

## The perturbative region

-/

/-- The region of `(x, μ)` on which the perturbative expansion underlying a scheme change
is taken to be controlled.

It is a concrete rectangle with named endpoints rather than an opaque predicate: the
domain of validity is the contested quantity, so it has to be something a statement can
be quantified over and a counterexample can violate. -/
structure PerturbativeRegion : Type where
  /-- Lower endpoint in the momentum fraction; strictly positive, since the small-`x`
  expansion is where the argument is known to be delicate. -/
  xMin : ℝ
  /-- Upper endpoint in the momentum fraction. -/
  xMax : ℝ
  /-- Lower endpoint in the renormalization scale. -/
  muMin : ℝ
  /-- The lower endpoint in `x` is strictly positive. -/
  xMin_pos : 0 < xMin
  /-- The upper endpoint in `x` lies in the physical range. -/
  xMax_le_one : xMax ≤ 1
  /-- The scale floor is strictly positive. -/
  muMin_pos : 0 < muMin

/-- Membership in the perturbative region. -/
def PerturbativeRegion.Mem (R : PerturbativeRegion) (x mu : ℝ) : Prop :=
  R.xMin ≤ x ∧ x ≤ R.xMax ∧ R.muMin ≤ mu

/-- A point of the perturbative region lies in the physical range of the momentum
fraction. -/
lemma PerturbativeRegion.mem_unitInterval {R : PerturbativeRegion} {x mu : ℝ}
    (h : R.Mem x mu) :
    0 ≤ x ∧ x ≤ 1 :=
  ⟨le_trans R.xMin_pos.le h.1, le_trans h.2.1 R.xMax_le_one⟩

/-!

## The conditional

-/

/-- Hypotheses under which an MS-bar distribution inherits non-negativity from a physical
scheme on a perturbative region.

`Δ` is the scheme-change correction. The third field is the crux; see
`msbar_nonneg_iff_correction_dominated` for why it cannot be weakened. -/
structure MsbarPositivityHypotheses (fPhys fMsbar : Pdf Flavor)
    (Δ : Flavor → ℝ → ℝ → ℝ) (R : PerturbativeRegion) : Prop where
  /-- The physical-scheme distribution is non-negative on the region. -/
  phys_nonneg : ∀ i x mu, R.Mem x mu → 0 ≤ fPhys i x mu
  /-- The scheme change subtracts the perturbative correction `Δ`. -/
  scheme_change : ∀ i x mu, R.Mem x mu → fMsbar i x mu = fPhys i x mu - Δ i x mu
  /-- The correction is dominated by the distribution it corrects. -/
  correction_dominated : ∀ i x mu, R.Mem x mu → Δ i x mu ≤ fPhys i x mu

/-- **MS-bar positivity, conditionally.** -/
lemma msbar_nonneg {fPhys fMsbar : Pdf Flavor} {Δ : Flavor → ℝ → ℝ → ℝ}
    {R : PerturbativeRegion} (h : MsbarPositivityHypotheses fPhys fMsbar Δ R)
    (i : Flavor) (x mu : ℝ) (hmem : R.Mem x mu) :
    0 ≤ fMsbar i x mu := by
  rw [h.scheme_change i x mu hmem]
  have hdom := h.correction_dominated i x mu hmem
  linarith

/-!

## Sharpness: `correction_dominated` is the conclusion, not a sufficient condition

-/

/-- **The hypothesis cannot be weakened.** Given only the scheme-change relation,
non-negativity of the MS-bar distribution on the region is equivalent to domination of
the correction by the physical distribution.

This is the precise answer to "what is the weakest `correction_bounded` that makes the
conclusion provable": the weakest one is the conclusion itself, transported across the
scheme-change relation. Any genuinely weaker hypothesis must therefore constrain
something other than the correction — see `correction_dominated_of_lower_bound`. -/
theorem msbar_nonneg_iff_correction_dominated {fPhys fMsbar : Pdf Flavor}
    {Δ : Flavor → ℝ → ℝ → ℝ} {R : PerturbativeRegion}
    (hchange : ∀ i x mu, R.Mem x mu → fMsbar i x mu = fPhys i x mu - Δ i x mu) :
    (∀ i x mu, R.Mem x mu → 0 ≤ fMsbar i x mu)
      ↔ ∀ i x mu, R.Mem x mu → Δ i x mu ≤ fPhys i x mu := by
  constructor
  · intro h i x mu hmem
    have hx := h i x mu hmem
    rw [hchange i x mu hmem] at hx
    linarith
  · intro h i x mu hmem
    rw [hchange i x mu hmem]
    have hd := h i x mu hmem
    linarith

/-- Wherever the physical distribution vanishes, the hypothesis forces a *sign* condition
on the correction — a condition perturbation theory does not supply, since the sign of a
scheme-change correction is not fixed order by order. -/
theorem correction_nonpos_of_phys_eq_zero {fPhys fMsbar : Pdf Flavor}
    {Δ : Flavor → ℝ → ℝ → ℝ} {R : PerturbativeRegion}
    (h : MsbarPositivityHypotheses fPhys fMsbar Δ R)
    (i : Flavor) (x mu : ℝ) (hmem : R.Mem x mu) (hzero : fPhys i x mu = 0) :
    Δ i x mu ≤ 0 := by
  have hd := h.correction_dominated i x mu hmem
  rw [hzero] at hd
  exact hd

/-- **No absolute bound on the correction suffices.**

For every `ε` in `(0, 1)` there is a non-negative physical distribution and a correction
bounded in absolute value by `ε` whose difference is negative at an interior point of the
unit interval. The failure point is `x = ε / 2`: the counterexample is a small-`x`
statement, which is where the MS-bar negativity discussion in the literature lives.

Since `ε` is arbitrary, this rules out every hypothesis of the form "the correction is
of order `α_s^k` with a bounded coefficient", at any `k`: such a hypothesis bounds `Δ`
absolutely and says nothing about `fPhys`. -/
theorem uniform_bound_insufficient (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (fPhys : Pdf Unit) (Δ : Unit → ℝ → ℝ → ℝ) (x mu : ℝ),
      (∀ i y m, 0 ≤ y → y ≤ 1 → 0 ≤ fPhys i y m) ∧
      (∀ i y m, |Δ i y m| ≤ ε) ∧
      0 < x ∧ x < 1 ∧ fPhys () x mu - Δ () x mu < 0 := by
  refine ⟨fun _ y _ => y, fun _ _ _ => ε, ε / 2, 1, ?_, ?_, by linarith, by linarith, ?_⟩
  · intro _ _ _ hy0 _
    exact hy0
  · intro _ _ _
    exact (abs_of_pos hε).le
  · show ε / 2 - ε < 0
    linarith

/-!

## What does work: a lower bound on the physical distribution

-/

/-- A scheme-change correction bounded by `a * Cmax` on the region, with `a` standing for
the coupling and `Cmax` for a bound on the coefficient. -/
structure CouplingBoundedCorrection (Δ : Flavor → ℝ → ℝ → ℝ) (a Cmax : ℝ)
    (R : PerturbativeRegion) : Prop where
  /-- The correction is bounded by `a * Cmax` throughout the region. -/
  bound : ∀ i x mu, R.Mem x mu → |Δ i x mu| ≤ a * Cmax

/-- **The hypothesis that does deliver positivity.** If the physical distribution is
bounded below by `fmin` on the region and the correction is bounded by `a * Cmax` with
`a * Cmax ≤ fmin`, then the correction is dominated and `msbar_nonneg` applies.

Note what is being assumed: a property of `fPhys`, not a smallness property of `Δ`
alone. -/
theorem correction_dominated_of_lower_bound {fPhys : Pdf Flavor} {Δ : Flavor → ℝ → ℝ → ℝ}
    {a Cmax fmin : ℝ} {R : PerturbativeRegion}
    (hC : CouplingBoundedCorrection Δ a Cmax R)
    (hfmin : ∀ i x mu, R.Mem x mu → fmin ≤ fPhys i x mu)
    (hsmall : a * Cmax ≤ fmin) :
    ∀ i x mu, R.Mem x mu → Δ i x mu ≤ fPhys i x mu := by
  intro i x mu hmem
  have h1 : Δ i x mu ≤ |Δ i x mu| := le_abs_self _
  have h2 := hC.bound i x mu hmem
  have h3 := hfmin i x mu hmem
  linarith

/-- **And where it degenerates.** If the lower bound on the physical distribution is not
strictly positive, the smallness condition `a * Cmax ≤ fmin` forces the coupling itself
to be non-positive, i.e. there is no positive coupling at which the sufficient condition
of `correction_dominated_of_lower_bound` can be met.

This is the formal statement of where MS-bar positivity is genuinely at risk: not at
large coupling, but wherever the distribution approaches zero. -/
theorem coupling_bound_degenerate_at_zero {a Cmax fmin : ℝ} (hCmax : 0 < Cmax)
    (hfmin : fmin ≤ 0) (hsmall : a * Cmax ≤ fmin) :
    a ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  nlinarith [mul_pos hpos hCmax]

end PDF
end Parton
end Particles
end Physlib
