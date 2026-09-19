/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# Fragmentation Function Interfaces (Stage 13)

This module introduces minimal fragmentation-function interfaces for
semi-inclusive DIS extensions.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace Particles
namespace Fragmentation

variable {Hadron Flavor : Type}

/-- Fragmentation-function family `D_h^i(z,Q2)`. -/
abbrev Frag (Hadron Flavor : Type) : Type := Hadron → Flavor → ℝ → ℝ → ℝ

/-- Structural assumptions for fragmentation functions. -/
structure Assumptions (D : Frag Hadron Flavor) : Prop where
  support : ∀ h i z Q2, z < 0 ∨ 1 < z → D h i z Q2 = 0
  nonneg : ∀ h i z Q2, 0 ≤ z → z ≤ 1 → 0 ≤ D h i z Q2

/-- Mellin-like z-moment for fragmentation functions. -/
def zMoment
    (D : Frag Hadron Flavor)
    (n : ℕ)
    (h : Hadron)
    (i : Flavor)
    (Q2 : ℝ) : ℝ :=
  ∫ z in Set.Icc (0 : ℝ) 1, z ^ n * D h i z Q2

/-- Support consequence outside the physical z-interval. -/
lemma eq_zero_of_not_mem_unitInterval
    (D : Frag Hadron Flavor)
    (hD : Assumptions D)
    (h : Hadron)
    (i : Flavor)
    (z Q2 : ℝ)
    (hz : z < 0 ∨ 1 < z) :
    D h i z Q2 = 0 :=
  hD.support h i z Q2 hz

end Fragmentation
end Particles
end Physlib
