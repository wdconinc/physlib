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
  supportH : ∀ i x xi t, x < 0 ∨ 1 < x → M.H i x xi t = 0
  supportE : ∀ i x xi t, x < 0 ∨ 1 < x → M.E i x xi t = 0
  skewnessBound : ∀ i x xi t, 1 < |xi| → M.H i x xi t = 0 ∧ M.E i x xi t = 0

/-- Forward-limit relation at fixed scale `Q2`: `H(x,0,0) = f(x,Q2)`. -/
def ForwardLimitToPdfAtScale
    (M : Model Flavor)
    (fPdf : PDF.Pdf Flavor)
    (Q2 : ℝ) : Prop :=
  ∀ i x, M.H i x 0 0 = fPdf i x Q2

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
