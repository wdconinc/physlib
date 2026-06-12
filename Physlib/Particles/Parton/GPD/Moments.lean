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

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace Particles
namespace Parton
namespace GPD

variable {Flavor : Type}

/-- Mellin moments of `H` over the collinear support interval. -/
def mellinMomentH (M : Model Flavor) (n : ℕ) (i : Flavor) (xi t : ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, x ^ n * M.H i x xi t

/-- Polynomiality schema for Mellin moments of `H`. -/
structure PolynomialityAssumptions (M : Model Flavor) : Type where
  coeff : ℕ → Flavor → ℕ → ℝ → ℝ
  polynomial : ∀ n i xi t,
    mellinMomentH M n i xi t
      = Finset.sum (Finset.range (n + 1)) (fun k => coeff n i k t * xi ^ k)

/-- First nontrivial polynomiality consequence: the zeroth moment is `ξ`-independent. -/
lemma mellinMomentH_n0_eq_at_zero
    (M : Model Flavor)
    (hPoly : PolynomialityAssumptions M)
    (i : Flavor) (xi t : ℝ) :
    mellinMomentH M 0 i xi t = mellinMomentH M 0 i 0 t := by
  calc
    mellinMomentH M 0 i xi t = hPoly.coeff 0 i 0 t := by
      simpa using hPoly.polynomial 0 i xi t
    _ = mellinMomentH M 0 i 0 t := by
      simpa using (hPoly.polynomial 0 i 0 t).symm

end GPD
end Parton
end Particles
end Physlib
