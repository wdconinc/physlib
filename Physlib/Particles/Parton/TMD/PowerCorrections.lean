/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.TMD.Basic
/-!

# Kinematic Power Corrections to TMD Factorization

A TMD factorization theorem is an approximation, and the phrase *kinematic power
correction* is a claim about how good it is: the leading-power term reproduces a structure
function up to a remainder suppressed by a power of `λ = q_T / Q`, and a correction is a
term that improves that suppression by one further power. This module states that claim
with the remainder bound explicit, and proves the facts that stop the statement from being
empty.

## What is, and is not, formalized here

The anchor papers for this target do something considerably stronger than what is stated
below. arXiv:2510.14496 evaluates the *complete* set of kinematic power corrections to the
leading-power SIDIS TMD factorization theorem, and arXiv:2603.19833 derives the quasi-TMD
factorization theorem with kinematic power corrections to all orders; in both the
corrections are *constructed* out of twist-two TMD distributions, and both emphasise that
the resulting expressions are gauge and frame invariant. None of that construction is
here. This module does not know what a twist-two distribution is, carries no Lorentz frame,
and has no notion of a soft function.

What is here is the *shape* of the resulting statement — an approximation carrying an
explicit remainder bound — together with the results that make a power correction a
determination rather than a convention:

* `coeff_unique`: the coefficient of the order-`n` correction is fixed by the structure
  function and the leading-power term. It is not a scheme choice.
* `not_approximatesToOrder_succ_of_coeff_ne_zero`: if that coefficient is nonzero, the
  leading-power term on its own is *not* accurate at the next order. A correction that
  could be dropped without changing the accuracy order would not be a correction.
* `leadingPower_approximatesToOrder`: the complementary fact that the correction is
  genuinely subleading — adding it does not disturb the accuracy the leading-power term
  already had.
* `monomialKpc` and `monomialKpc_leadingPower_not_approx_succ`: the interface is inhabited
  with a *nonzero* coefficient, so the sharpness statement is not vacuously true.

These are statements of real analysis about the `λ → 0⁺` expansion; they are not statements
about QCD. They are placed in the TMD namespace because the power counting they encode is
the TMD power counting, and because `Kpc` is the interface that a future derivation of a
factorization theorem in this library should be asked to produce. A definition that merely
named a correction term without bounding anything would carry none of this content.

## Not captured

* The all-orders resummation of kinematic power corrections. Only a single order is
  described; `Kpc` bounds the remainder after one correction, not after a series.
* Frame and gauge invariance of the corrected expression, which both anchors stress.
* The observation of arXiv:2603.19833 that once kinematic power corrections are included
  the TMD evolution factor enters as a convolution with the nonperturbative distribution
  rather than multiplicatively. The Collins-Soper system in
  `Physlib.Particles.Parton.TMD.CollinsSoper` is multiplicative and is in that respect a
  leading-power statement.
* Any link to the transverse-momentum integrals of `Physlib.Particles.Parton.TMD.Basic`:
  the structure function here is an abstract function of `λ`, not one built from a `Tmd`.

## References

* arXiv:2510.14496, *Kinematic power corrections for TMD factorization theorem of
  semi-inclusive deep-inelastic scattering*.
* arXiv:2603.19833, *Factorization theorem for quasi-TMD distributions with kinematic power
  corrections*.
* R. Boussarie *et al.*, *TMD Handbook*, arXiv:2304.03302.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace Particles
namespace Parton
namespace TMD
namespace PowerCorrections

open Filter Topology Asymptotics

/-- The TMD power-counting ratio `λ = q_T / Q`. The power expansion of a TMD factorization
theorem is an expansion in this ratio, and the limit in which the theorem is a theorem is
`λ → 0⁺`. -/
def powerRatio (qT Q : ℝ) : ℝ := qT / Q

/-- The filter in which TMD power counting is done: the power-counting ratio tends to zero
from above.

From *above* is not cosmetic. `λ` is a ratio of a transverse momentum to a hard scale and is
positive, and it is positivity that makes `λ ^ n` nonvanishing along the filter, on which
the uniqueness argument below depends. -/
abbrev smallRatio : Filter ℝ := 𝓝[>] (0 : ℝ)

/-- `ApproximatesToOrder W Wapp n` states that `Wapp` reproduces `W` with a remainder
bounded by `λ ^ n` as the power-counting ratio `λ` tends to zero from above,
`W λ - Wapp λ = O(λ ^ n)`.

This is the shape of a factorization theorem carrying a stated accuracy. -/
def ApproximatesToOrder (W Wapp : ℝ → ℝ) (n : ℕ) : Prop :=
  (fun lam => W lam - Wapp lam) =O[smallRatio] fun lam => lam ^ n

/-- Near `0⁺` a higher power of the power-counting ratio is dominated by a lower one. -/
lemma isBigO_pow_of_le {m n : ℕ} (hmn : m ≤ n) :
    (fun lam : ℝ => lam ^ n) =O[smallRatio] fun lam : ℝ => lam ^ m := by
  have hIio : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds (by norm_num)
  have hlt1 : ∀ᶠ lam : ℝ in smallRatio, lam < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hIio
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hlt1] with lam hmem hlt
  have hpos : (0 : ℝ) < lam := hmem
  have hle : lam ^ n ≤ lam ^ m := pow_le_pow_of_le_one hpos.le hlt.le hmn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hpos n),
    abs_of_pos (pow_pos hpos m), one_mul]
  exact hle

/-- An approximation accurate to order `n` is accurate to every lower order. -/
lemma ApproximatesToOrder.mono {W Wapp : ℝ → ℝ} {m n : ℕ}
    (h : ApproximatesToOrder W Wapp n) (hmn : m ≤ n) :
    ApproximatesToOrder W Wapp m :=
  Asymptotics.IsBigO.trans h (isBigO_pow_of_le hmn)

/-- A monomial `c λ ^ n` that is bounded by `λ ^ (n + 1)` as `λ → 0⁺` has vanishing
coefficient.

This is the analytic fact behind every statement in this module. It is what forbids two
different power corrections at the same order, and what makes a nonzero correction
detectable in the accuracy of the leading-power term. -/
lemma eq_zero_of_isBigO_pow_succ {n : ℕ} {c : ℝ}
    (h : (fun lam : ℝ => c * lam ^ n) =O[smallRatio] fun lam : ℝ => lam ^ (n + 1)) :
    c = 0 := by
  by_contra hc
  have : Filter.NeBot smallRatio := nhdsGT_neBot (0 : ℝ)
  have h0 : Tendsto (fun lam : ℝ => lam) smallRatio (𝓝 0) := by
    have hid : Tendsto (fun lam : ℝ => lam) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
    exact hid.mono_left nhdsWithin_le_nhds
  have h1 : (fun lam : ℝ => lam) =o[smallRatio] fun _ : ℝ => (1 : ℝ) :=
    (isLittleO_one_iff ℝ).mpr h0
  have h2 := h1.mul_isBigO (isBigO_refl (fun lam : ℝ => lam ^ n) smallRatio)
  have hstep : (fun lam : ℝ => lam ^ (n + 1)) =o[smallRatio] fun lam : ℝ => lam ^ n := by
    simpa [pow_succ', one_mul] using h2
  have hlo := h.trans_isLittleO hstep
  have hback : (fun lam : ℝ => lam ^ n) =O[smallRatio] fun lam : ℝ => c * lam ^ n := by
    refine ((isBigO_refl (fun lam : ℝ => c * lam ^ n) smallRatio).const_mul_left
      c⁻¹).congr_left ?_
    intro lam
    field_simp
  have hfreq : ∃ᶠ lam : ℝ in smallRatio, c * lam ^ n ≠ 0 := by
    have hev : ∀ᶠ lam : ℝ in smallRatio, c * lam ^ n ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with lam hmem
      have hpos : (0 : ℝ) < lam := hmem
      exact mul_ne_zero hc (pow_ne_zero n hpos.ne')
    exact hev.frequently
  exact hlo.not_isBigO hfreq hback

/-- **The kinematic power correction at a given order is unique.** If two coefficients each
improve the leading-power approximation from order `n` to order `n + 1`, they are equal.

The correction is therefore a determination made by the structure function together with
its leading-power term, and not a convention of whoever writes the expansion down. -/
lemma coeff_unique {W Wlp : ℝ → ℝ} {n : ℕ} {c₁ c₂ : ℝ}
    (h₁ : ApproximatesToOrder W (fun lam => Wlp lam + c₁ * lam ^ n) (n + 1))
    (h₂ : ApproximatesToOrder W (fun lam => Wlp lam + c₂ * lam ^ n) (n + 1)) :
    c₁ = c₂ := by
  have h₁' : (fun lam : ℝ => W lam - (Wlp lam + c₁ * lam ^ n)) =O[smallRatio]
      fun lam : ℝ => lam ^ (n + 1) := h₁
  have h₂' : (fun lam : ℝ => W lam - (Wlp lam + c₂ * lam ^ n)) =O[smallRatio]
      fun lam : ℝ => lam ^ (n + 1) := h₂
  have hdiff : (fun lam : ℝ => (c₂ - c₁) * lam ^ n) =O[smallRatio]
      fun lam : ℝ => lam ^ (n + 1) := by
    refine (h₁'.sub h₂').congr_left ?_
    intro lam
    ring
  have hz := eq_zero_of_isBigO_pow_succ hdiff
  linarith

/-- **A structure function that vanishes at leading power is determined, at the first
nonvanishing order, entirely by its kinematic power correction.**

arXiv:2510.14496 reports exactly this situation for SIDIS: structure functions that vanish
in the leading-power TMD factorization theorem, the longitudinal-photon contributions among
them, receive their first prediction from the kinematic power corrections. What is proved
here is that such a prediction is unique — there is no freedom left in the coefficient. -/
lemma coeff_unique_of_leadingPower_zero {W : ℝ → ℝ} {n : ℕ} {c₁ c₂ : ℝ}
    (h₁ : ApproximatesToOrder W (fun lam => c₁ * lam ^ n) (n + 1))
    (h₂ : ApproximatesToOrder W (fun lam => c₂ * lam ^ n) (n + 1)) :
    c₁ = c₂ := by
  have h₁' : (fun lam : ℝ => W lam - c₁ * lam ^ n) =O[smallRatio]
      fun lam : ℝ => lam ^ (n + 1) := h₁
  have h₂' : (fun lam : ℝ => W lam - c₂ * lam ^ n) =O[smallRatio]
      fun lam : ℝ => lam ^ (n + 1) := h₂
  have hdiff : (fun lam : ℝ => (c₂ - c₁) * lam ^ n) =O[smallRatio]
      fun lam : ℝ => lam ^ (n + 1) := by
    refine (h₁'.sub h₂').congr_left ?_
    intro lam
    ring
  have hz := eq_zero_of_isBigO_pow_succ hdiff
  linarith

/-- **The leading-power term keeps its own accuracy.** If including the order-`n` correction
gives an approximation accurate to order `n + 1`, then the leading-power term on its own is
accurate to order `n`: the correction is genuinely subleading. -/
lemma leadingPower_approximatesToOrder {W Wlp : ℝ → ℝ} {n : ℕ} {c : ℝ}
    (h : ApproximatesToOrder W (fun lam => Wlp lam + c * lam ^ n) (n + 1)) :
    ApproximatesToOrder W Wlp n := by
  have h' : (fun lam : ℝ => W lam - (Wlp lam + c * lam ^ n)) =O[smallRatio]
      fun lam : ℝ => lam ^ (n + 1) := h
  have hlow : (fun lam : ℝ => W lam - (Wlp lam + c * lam ^ n)) =O[smallRatio]
      fun lam : ℝ => lam ^ n := h'.trans (isBigO_pow_of_le (Nat.le_succ n))
  have hcorr : (fun lam : ℝ => c * lam ^ n) =O[smallRatio] fun lam : ℝ => lam ^ n :=
    (isBigO_refl (fun lam : ℝ => lam ^ n) smallRatio).const_mul_left c
  have hsum : (fun lam : ℝ => W lam - Wlp lam) =O[smallRatio] fun lam : ℝ => lam ^ n := by
    refine (hlow.add hcorr).congr_left ?_
    intro lam
    ring
  exact hsum

/-- **A nonvanishing power correction is detectable.** If the order-`n` coefficient is
nonzero then the leading-power term alone is *not* accurate to order `n + 1`.

Together with `coeff_unique` this is what keeps the interface from being empty: the
correction can neither be dropped nor be chosen. -/
lemma not_approximatesToOrder_succ_of_coeff_ne_zero {W Wlp : ℝ → ℝ} {n : ℕ} {c : ℝ}
    (h : ApproximatesToOrder W (fun lam => Wlp lam + c * lam ^ n) (n + 1)) (hc : c ≠ 0) :
    ¬ ApproximatesToOrder W Wlp (n + 1) := by
  intro hlp
  have hlp' : (fun lam : ℝ => W lam - Wlp lam) =O[smallRatio]
      fun lam : ℝ => lam ^ (n + 1) := hlp
  have hzero : ApproximatesToOrder W (fun lam => Wlp lam + 0 * lam ^ n) (n + 1) := by
    have hcast : (fun lam : ℝ => W lam - (Wlp lam + 0 * lam ^ n)) =O[smallRatio]
        fun lam : ℝ => lam ^ (n + 1) := by
      refine hlp'.congr_left ?_
      intro lam
      ring
    exact hcast
  exact hc (coeff_unique h hzero)

/-- The data of a TMD factorization formula at one order in the power counting: a
leading-power term, the coefficient of the kinematic power correction at order `n`, and the
remainder bound that is their joint content.

There is exactly one hypothesis field and it is the bound itself. Nothing here stands in
for physics that has not been done: `leadingPower` is whatever function a factorization
theorem produces, and `remainder` is the claim that adding `coeff * λ ^ n` to it improves
the accuracy by one power of `λ`. -/
structure Kpc (W : ℝ → ℝ) (n : ℕ) where
  /-- The leading-power term of the factorization formula. -/
  leadingPower : ℝ → ℝ
  /-- The coefficient of the order-`n` kinematic power correction. -/
  coeff : ℝ
  /-- The remainder bound: including the correction leaves an error `O(λ ^ (n + 1))`. -/
  remainder : ApproximatesToOrder W (fun lam => leadingPower lam + coeff * lam ^ n) (n + 1)

namespace Kpc

variable {W : ℝ → ℝ} {n : ℕ}

/-- The leading-power term of a `Kpc` is itself accurate to order `n`. -/
lemma leadingPower_approx (K : Kpc W n) : ApproximatesToOrder W K.leadingPower n :=
  leadingPower_approximatesToOrder K.remainder

/-- Two power-correction data for the same structure function with the same leading-power
term carry the same coefficient. -/
lemma coeff_eq (K L : Kpc W n) (h : K.leadingPower = L.leadingPower) : K.coeff = L.coeff := by
  refine coeff_unique (Wlp := K.leadingPower) K.remainder ?_
  rw [h]
  exact L.remainder

/-- A nonzero correction cannot be absorbed into the leading-power term: that term alone is
not accurate to order `n + 1`. -/
lemma leadingPower_not_approx_succ (K : Kpc W n) (hc : K.coeff ≠ 0) :
    ¬ ApproximatesToOrder W K.leadingPower (n + 1) :=
  not_approximatesToOrder_succ_of_coeff_ne_zero K.remainder hc

end Kpc

/-- A structure function whose leading-power term vanishes and whose order-`n` kinematic
power correction is the whole of it.

This witnesses that `Kpc` is inhabited with a *nonzero* coefficient, so that
`Kpc.leadingPower_not_approx_succ` is not vacuously true. -/
def monomialKpc (n : ℕ) : Kpc (fun lam : ℝ => lam ^ n) n where
  leadingPower := fun _ => 0
  coeff := 1
  remainder := by
    have hz : (fun _ : ℝ => (0 : ℝ)) =O[smallRatio] fun lam : ℝ => lam ^ (n + 1) :=
      isBigO_zero _ _
    have hcast : (fun lam : ℝ => lam ^ n - ((fun _ : ℝ => (0 : ℝ)) lam + 1 * lam ^ n))
        =O[smallRatio] fun lam : ℝ => lam ^ (n + 1) := by
      refine hz.congr_left ?_
      intro lam
      ring
    exact hcast

/-- **The order gap is real.** `λ ^ n` is not `O(λ ^ (n + 1))` as `λ → 0⁺`, so the vanishing
leading-power term of `monomialKpc` is accurate to order `n` and no further.

Without a statement of this kind the whole interface would be satisfiable by taking every
correction coefficient to be zero. -/
lemma monomialKpc_leadingPower_not_approx_succ (n : ℕ) :
    ¬ ApproximatesToOrder (fun lam : ℝ => lam ^ n) (fun _ => 0) (n + 1) :=
  (monomialKpc n).leadingPower_not_approx_succ one_ne_zero

/-- The power-counting ratio tends to zero from above as the hard scale grows at fixed
transverse momentum. -/
lemma tendsto_powerRatio_atTop {qT : ℝ} (hqT : 0 < qT) :
    Tendsto (fun Q : ℝ => powerRatio qT Q) atTop smallRatio := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hdiv : Tendsto (fun Q : ℝ => qT / Q) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    exact hdiv
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
    exact div_pos hqT hQ

/-- **Power counting in `λ` is power counting in the hard scale.** An approximation accurate
to order `n` in the power-counting ratio has, at fixed transverse momentum, an error
suppressed by `n` powers of the hard scale as `Q → ∞`.

This is the bridge between the abstract `λ → 0⁺` statement used throughout this module and
the form in which a power correction is quoted in the literature, as a contribution of
relative size `(q_T / Q) ^ n`. -/
lemma isBigO_inv_pow_atTop {W Wapp : ℝ → ℝ} {n : ℕ} (h : ApproximatesToOrder W Wapp n)
    {qT : ℝ} (hqT : 0 < qT) :
    (fun Q : ℝ => W (powerRatio qT Q) - Wapp (powerRatio qT Q)) =O[atTop]
      fun Q : ℝ => (Q ^ n)⁻¹ := by
  have h' : (fun lam : ℝ => W lam - Wapp lam) =O[smallRatio] fun lam : ℝ => lam ^ n := h
  have hcomp := h'.comp_tendsto (tendsto_powerRatio_atTop hqT)
  have hconv : (fun Q : ℝ => powerRatio qT Q ^ n) =O[atTop] fun Q : ℝ => (Q ^ n)⁻¹ := by
    refine ((isBigO_refl (fun Q : ℝ => (Q ^ n)⁻¹) atTop).const_mul_left (qT ^ n)).congr_left ?_
    intro Q
    show qT ^ n * (Q ^ n)⁻¹ = (qT / Q) ^ n
    rw [div_pow, div_eq_mul_inv]
  exact hcomp.trans hconv

end PowerCorrections
end TMD
end Parton
end Particles
end Physlib
