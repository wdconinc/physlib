/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.Unified.Basic
/-!

# Unified Cross-Framework Consistency

This module proves bridge theorems relating the unified API back to its TMD
and GPD consistency assumptions.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace Particles
namespace Parton
namespace Unified

variable {Flavor : Type}

/-- TMD-to-PDF consistency theorem in unified API form. -/
lemma tmd_consistency
    (U : Model Flavor)
    (hU : Assumptions U) :
    ∀ i x Q2, tmdCollinear U i x Q2 = pdfAt U i x Q2 :=
  hU.tmdToPdf

/-- GPD-forward-limit consistency theorem in unified API form. -/
lemma gpd_forward_consistency
    (U : Model Flavor)
    (hU : Assumptions U)
    (Q2 : ℝ) :
    ∀ i x, gpdHAt U i x 0 0 = pdfAt U i x Q2 :=
  hU.gpdForward Q2

/-- Bridge theorem: TMD collinear reduction matches GPD forward limit. -/
lemma tmd_gpd_forward_consistency
    (U : Model Flavor)
    (hU : Assumptions U)
    (Q2 : ℝ) :
    ∀ i x, tmdCollinear U i x Q2 = gpdHAt U i x 0 0 := by
  intro i x
  calc
    tmdCollinear U i x Q2 = pdfAt U i x Q2 := hU.tmdToPdf i x Q2
    _ = gpdHAt U i x 0 0 := by
      simpa [gpdHAt, pdfAt] using (hU.gpdForward Q2 i x).symm

end Unified
end Parton
end Particles
end Physlib
