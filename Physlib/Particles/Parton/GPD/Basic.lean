/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.PDF.Basic
/-!

# GPD Object Model and Forward Limit

This module introduces generalized parton distribution (GPD) objects `H` and `E`
and a forward-limit bridge to collinear PDFs.

## Support convention

A GPD `H(x, ξ, t)` is supported on `|x| ≤ 1`, not on `x ∈ [0, 1]`. The half `0 < x ≤ 1`
carries the quark distribution and the half `-1 ≤ x < 0` the antiquark distribution,
while the central band `|x| ≤ |ξ|` (the ERBL region) has no density interpretation at
all. Restricting to `x ≥ 0` would make the polynomiality of the `x`-moments, the
evenness of those moments in `ξ`, and the D-term all inexpressible, so the support
condition here is stated as `x < -1 ∨ 1 < x → H = 0`.

Reference: M. Diehl, *Generalized parton distributions*, Phys. Rept. **388** (2003) 41,
§3.1-§3.2 (arXiv:hep-ph/0307382).

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace Particles
namespace Parton
namespace GPD

variable {Flavor : Type}

/-- A GPD family indexed by flavor and variables `(x, ξ, t)`. -/
abbrev Gpd (Flavor : Type) : Type := Flavor → ℝ → ℝ → ℝ → ℝ

/-- Minimal GPD model carrying the standard pair `(H, E)`. -/
structure Model (Flavor : Type) : Type where
  H : Gpd Flavor
  E : Gpd Flavor

/-- Structural assumptions for a GPD model. -/
structure Assumptions (M : Model Flavor) : Prop where
  /-- `H` vanishes outside the physical support `|x| ≤ 1`. -/
  supportH : ∀ i x xi t, x < -1 ∨ 1 < x → M.H i x xi t = 0
  /-- `E` vanishes outside the physical support `|x| ≤ 1`. -/
  supportE : ∀ i x xi t, x < -1 ∨ 1 < x → M.E i x xi t = 0
  /-- Both GPDs vanish outside the physical skewness range `|ξ| ≤ 1`. -/
  skewnessBound : ∀ i x xi t, 1 < |xi| → M.H i x xi t = 0 ∧ M.E i x xi t = 0

/-- The DGLAP region of GPD kinematics, `|ξ| < |x| ≤ 1`.

Here the two active partons carry momentum fractions of the same sign, so the
distribution retains a density interpretation: `x > 0` is the quark region and
`x < 0` the antiquark region. -/
def InDglapRegion (x xi : ℝ) : Prop := |xi| < |x| ∧ |x| ≤ 1

/-- The ERBL region of GPD kinematics, `|x| ≤ |ξ|`.

Here the two active partons carry momentum fractions of opposite sign, the GPD
behaves like a meson distribution amplitude rather than a density, and positivity
bounds do not apply. This is also where the D-term and the shadow GPDs live. -/
def InErblRegion (x xi : ℝ) : Prop := |x| ≤ |xi|

/-- The two kinematic regions are mutually exclusive. -/
lemma not_inErblRegion_of_inDglapRegion {x xi : ℝ} (h : InDglapRegion x xi) :
    ¬ InErblRegion x xi := by
  intro h'
  have h1 : |xi| < |x| := h.1
  have h2 : |x| ≤ |xi| := h'
  linarith

/-- Inside the physical support the two kinematic regions are exhaustive. -/
lemma inDglapRegion_or_inErblRegion {x xi : ℝ} (hx : |x| ≤ 1) :
    InDglapRegion x xi ∨ InErblRegion x xi := by
  rcases lt_trichotomy |xi| |x| with h | h | h
  · exact Or.inl ⟨h, hx⟩
  · exact Or.inr (le_of_eq h.symm)
  · exact Or.inr (le_of_lt h)

/-- Support of `H` in absolute-value form: `H` vanishes whenever `1 < |x|`. -/
lemma H_eq_zero_of_one_lt_abs {M : Model Flavor} (h : Assumptions M)
    (i : Flavor) (x xi t : ℝ) (hx : 1 < |x|) :
    M.H i x xi t = 0 := by
  refine h.supportH i x xi t ?_
  rcases abs_cases x with ⟨hax, _⟩ | ⟨hax, _⟩
  · rw [hax] at hx
    exact Or.inr hx
  · rw [hax] at hx
    exact Or.inl (by linarith)

/-- Support of `E` in absolute-value form: `E` vanishes whenever `1 < |x|`. -/
lemma E_eq_zero_of_one_lt_abs {M : Model Flavor} (h : Assumptions M)
    (i : Flavor) (x xi t : ℝ) (hx : 1 < |x|) :
    M.E i x xi t = 0 := by
  refine h.supportE i x xi t ?_
  rcases abs_cases x with ⟨hax, _⟩ | ⟨hax, _⟩
  · rw [hax] at hx
    exact Or.inr hx
  · rw [hax] at hx
    exact Or.inl (by linarith)

/-- Forward-limit relation at fixed scale `Q2`: `H(x,0,0) = f(x,Q2)`. -/
def ForwardLimitToPdfAtScale
    (M : Model Flavor)
    (fPdf : PDF.Pdf Flavor)
    (Q2 : ℝ) : Prop :=
  ∀ i x, M.H i x 0 0 = fPdf i x Q2

/-- Antiquark forward-limit relation at fixed scale `Q2`: `H(-x, 0, 0) = -f̄(x, Q2)`.

The negative-`x` half of the corrected support carries the antiquark distribution, with
the conventional relative minus sign (Diehl, *Generalized parton distributions*,
Phys. Rept. **388** (2003) 41, arXiv:hep-ph/0307382; see its discussion of GPD support and the
forward limit — no equation number is given here because the primary source was not consulted
directly when this file was written).
This relation is not expressible while the support is restricted to `x ≥ 0`, which is
why it is stated here rather than in the original half-range interface. -/
def AntiquarkForwardLimitToPdfAtScale
    (M : Model Flavor)
    (fBarPdf : PDF.Pdf Flavor)
    (Q2 : ℝ) : Prop :=
  ∀ i x, M.H i (-x) 0 0 = -fBarPdf i x Q2

/-- Forward-limit bridge theorem from GPDs to collinear PDFs. -/
lemma forwardLimit_bridge
    (M : Model Flavor)
    (fPdf : PDF.Pdf Flavor)
    (Q2 : ℝ)
    (hFwd : ForwardLimitToPdfAtScale M fPdf Q2) :
    ∀ i x, M.H i x 0 0 = fPdf i x Q2 :=
  hFwd

/-- A convenient rewrite form for the forward limit in either direction. -/
lemma forwardLimit_bridge_symm
    (M : Model Flavor)
    (fPdf : PDF.Pdf Flavor)
    (Q2 : ℝ)
    (hFwd : ForwardLimitToPdfAtScale M fPdf Q2)
    (i : Flavor) (x : ℝ) :
    fPdf i x Q2 = M.H i x 0 0 := by
  simpa using (hFwd i x).symm

end GPD
end Parton
end Particles
end Physlib
