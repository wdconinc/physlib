/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.GPD.DoubleDistribution
/-!

# The D-term Ambiguity of a GPD

This module isolates the part of a generalized parton distribution that is invisible to
data taken in the DGLAP region: the D-term.

## Why this is a separate module

The double-distribution representation of `Physlib.Particles.Parton.GPD.DoubleDistribution`
writes a GPD as the sum of a Radon-type transform of a double distribution `F` and a
D-term piece. The two pieces have *different supports in `x` at fixed `ξ`*: the D-term
piece is a function of `x / ξ` supported on `|x / ξ| ≤ 1`, hence lives entirely inside the
ERBL region `|x| ≤ |ξ|`, while the `F` piece is supported on the whole of `|x| ≤ 1`.

That asymmetry is the formal content of the phrase "up to a D-term" in the GPD
reconstruction literature (arXiv:2401.12013): any statement whose data lives in the
DGLAP region `|ξ| < |x| ≤ 1` is blind to a D-term and can determine a GPD at best up to
one. `gpdOfDTerm_eq_zero_of_inDglapRegion` below is that statement, and it is proved
rather than assumed.

The module also provides the algebra needed to *state* "two models differ by a D-term":
the zero double distribution, the zero and difference D-terms, and the fact that two
models sharing a double distribution differ exactly by the D-term of the difference
(`sub_eq_gpdOfDTerm_of_dd_eq`).

## Scope

Nothing here says that the double-distribution representation of a given model *exists*
or is unique; `AdmitsDoubleDistribution` is a hypothesis bundle carrying a representation
as data. The Polyakov-Weiss gauge freedom in the `(F, D)` split at fixed `H` is not
addressed here — see the note in `NOTES.md` of `task/frontier-open-targets`.

## References

* M. Diehl, *Generalized parton distributions*, Phys. Rept. **388** (2003) 41, §4.3
  (arXiv:hep-ph/0307382).
* M. V. Polyakov and C. Weiss, Phys. Rev. D **60** (1999) 114017 (arXiv:hep-ph/9902451).
* A. V. Belitsky and A. V. Radyushkin, Phys. Rept. **418** (2005) 1, §3
  (arXiv:hep-ph/0504030).

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace Particles
namespace Parton
namespace GPD

variable {Flavor : Type}

/-!

## The trivial double distribution and the D-term algebra

-/

/-- The identically zero double distribution, used to isolate a pure D-term. -/
def DoubleDistribution.zero (Flavor : Type) : DoubleDistribution Flavor where
  F := fun _ _ _ _ => 0
  support := fun _ _ _ _ _ => rfl
  alphaSymm := fun _ _ _ _ => rfl
  integrable := fun _ _ => by simp
  momentIntegrable := fun _ _ _ _ => by simp

@[simp]
lemma DoubleDistribution.zero_F (Flavor : Type) (i : Flavor) (β α t : ℝ) :
    (DoubleDistribution.zero Flavor).F i β α t = 0 := rfl

/-- The identically zero D-term. -/
def DTerm.zero (Flavor : Type) : DTerm Flavor where
  D := fun _ _ _ => 0
  support := fun _ _ _ _ => rfl
  odd := fun _ _ _ => by simp
  momentIntegrable := fun _ _ _ => by simp

@[simp]
lemma DTerm.zero_D (Flavor : Type) (i : Flavor) (u t : ℝ) :
    (DTerm.zero Flavor).D i u t = 0 := rfl

/-- The difference of two D-terms is a D-term: support, oddness in `u` and integrability
of the monomial moments are all closed under subtraction. -/
def DTerm.sub (d₁ d₂ : DTerm Flavor) : DTerm Flavor where
  D := fun i u t => d₁.D i u t - d₂.D i u t
  support := fun i u t hu => by
    rw [d₁.support i u t hu, d₂.support i u t hu, sub_zero]
  odd := fun i u t => by
    rw [d₁.odd i u t, d₂.odd i u t]
    ring
  momentIntegrable := fun i m t => by
    simpa [mul_sub] using (d₁.momentIntegrable i m t).sub (d₂.momentIntegrable i m t)

@[simp]
lemma DTerm.sub_D (d₁ d₂ : DTerm Flavor) (i : Flavor) (u t : ℝ) :
    (DTerm.sub d₁ d₂).D i u t = d₁.D i u t - d₂.D i u t := rfl

/-!

## The GPD carried by a pure D-term

-/

/-- The GPD induced by a D-term alone, i.e. by the double-distribution representation with
`F = 0`. Explicitly `gpdOfDTerm d i x ξ t = (ξ / |ξ|) * D(x / ξ, t)` for `ξ ≠ 0`, and `0`
at `ξ = 0`. -/
def gpdOfDTerm (dt : DTerm Flavor) : Gpd Flavor :=
  gpdOfDoubleDistribution (DoubleDistribution.zero Flavor) dt

/-- The explicit pointwise form of `gpdOfDTerm`. -/
lemma gpdOfDTerm_apply (dt : DTerm Flavor) (i : Flavor) (x xi t : ℝ) :
    gpdOfDTerm dt i x xi t = if xi = 0 then 0 else (xi / |xi|) * dt.D i (x / xi) t := by
  by_cases h : xi = 0
  · simp [gpdOfDTerm, gpdOfDoubleDistribution, h]
  · simp [gpdOfDTerm, gpdOfDoubleDistribution, h]

/-- A pure D-term has vanishing forward limit, so it is invisible to collinear PDF data. -/
lemma gpdOfDTerm_forward (dt : DTerm Flavor) (i : Flavor) (x t : ℝ) :
    gpdOfDTerm dt i x 0 t = 0 := by
  rw [gpdOfDTerm_apply, if_pos rfl]

/-- **The D-term ambiguity lives in the ERBL region.** A pure D-term vanishes identically
on the DGLAP region `|ξ| < |x| ≤ 1`, at every skewness.

This is the precise sense in which GPD data taken in the DGLAP region — which is the data
a DVCS extraction at small skewness provides — cannot constrain a D-term, and hence the
precise content of the qualifier "up to a D-term" in arXiv:2401.12013. -/
theorem gpdOfDTerm_eq_zero_of_inDglapRegion (dt : DTerm Flavor) (i : Flavor) (x xi t : ℝ)
    (h : InDglapRegion x xi) :
    gpdOfDTerm dt i x xi t = 0 := by
  rw [gpdOfDTerm_apply]
  by_cases hxi : xi = 0
  · simp [hxi]
  · have hxipos : 0 < |xi| := abs_pos.mpr hxi
    have hone : 1 < |x / xi| := by
      rw [abs_div]
      exact (one_lt_div hxipos).mpr h.1
    rw [if_neg hxi, dt.support i (x / xi) t hone, mul_zero]

/-- A D-term that vanishes identically induces the zero GPD. -/
lemma gpdOfDTerm_eq_zero_of_dTerm_eq_zero (dt : DTerm Flavor)
    (h : ∀ i u t, dt.D i u t = 0) (i : Flavor) (x xi t : ℝ) :
    gpdOfDTerm dt i x xi t = 0 := by
  rw [gpdOfDTerm_apply]
  by_cases hxi : xi = 0
  · simp [hxi]
  · rw [if_neg hxi, h, mul_zero]

/-!

## The zero model and double-distribution representations

-/

/-- The identically vanishing GPD model, used as a reference point when a statement about
a difference of models is recast as a statement about a single model. -/
def Model.zero (Flavor : Type) : Model Flavor where
  H := fun _ _ _ _ => 0
  E := fun _ _ _ _ => 0

@[simp]
lemma Model.zero_H (Flavor : Type) (i : Flavor) (x xi t : ℝ) :
    (Model.zero Flavor).H i x xi t = 0 := rfl

/-- A double-distribution representation of the `H` component of a GPD model, carried as
data rather than asserted. This is the hypothesis that the reconstruction arguments of the
GPD literature actually use: they invert a Radon transform, which presupposes that one is
there to invert. -/
structure AdmitsDoubleDistribution (M : Model Flavor) : Type where
  /-- The double distribution representing `H`. -/
  ddH : DoubleDistribution Flavor
  /-- The D-term representing `H`. -/
  dtH : DTerm Flavor
  /-- `H` is the GPD induced by `ddH` and `dtH`. -/
  reprH : ∀ i x xi t, M.H i x xi t = gpdOfDoubleDistribution ddH dtH i x xi t

/-- The zero model is represented by the zero double distribution and the zero D-term. -/
def admitsDoubleDistribution_zero (Flavor : Type) :
    AdmitsDoubleDistribution (Model.zero Flavor) where
  ddH := DoubleDistribution.zero Flavor
  dtH := DTerm.zero Flavor
  reprH := fun i x xi t => by
    by_cases h : xi = 0
    · simp [Model.zero, gpdOfDoubleDistribution, h]
    · simp [Model.zero, gpdOfDoubleDistribution, h]

/-- **Two models with the same double distribution differ by exactly one D-term.**

This is the algebraic half of the "uniqueness up to a D-term" statement: once the
double-distribution parts are known to agree, the residual difference is the GPD induced
by the difference of the two D-terms, with no leftover. The analytic half — that
DGLAP-region data at low skewness forces the double distributions to agree — is the part
that is not proved here. -/
theorem sub_eq_gpdOfDTerm_of_dd_eq {M₁ M₂ : Model Flavor}
    (R₁ : AdmitsDoubleDistribution M₁) (R₂ : AdmitsDoubleDistribution M₂)
    (hF : ∀ i β α t, R₁.ddH.F i β α t = R₂.ddH.F i β α t)
    (i : Flavor) (x xi t : ℝ) :
    M₁.H i x xi t = M₂.H i x xi t + gpdOfDTerm (DTerm.sub R₁.dtH R₂.dtH) i x xi t := by
  rw [R₁.reprH, R₂.reprH, gpdOfDTerm_apply]
  by_cases hxi : xi = 0
  · subst hxi
    simp only [gpdOfDoubleDistribution, if_pos rfl, add_zero, hF]
  · simp only [gpdOfDoubleDistribution, if_neg hxi, DTerm.sub_D, hF]
    ring

end GPD
end Parton
end Particles
end Physlib
