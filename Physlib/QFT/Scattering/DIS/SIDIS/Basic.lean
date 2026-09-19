/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.DIS.LO
public import Physlib.Particles.Parton.PDF.Basic
public import Physlib.Particles.Fragmentation.Basic
/-!

# SIDIS Interfaces (Stage 13)

This module defines semi-inclusive DIS observable interfaces based on PDF,
hard-kernel, and fragmentation-function ingredients.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace SIDIS

variable {Flavor Hadron : Type}

/-- A single SIDIS flavor-channel contribution. -/
def sidisChannel
    (C : Factorization.DIS.HardKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (D : Physlib.Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron)
    (i : Flavor)
    (x zHad Q2 : ℝ) : ℝ :=
  Factorization.DIS.loChannel C f i x Q2 * D h i zHad Q2

/-- SIDIS structure-function interface as a flavor sum. -/
def sidisStructureFunction [Fintype Flavor]
    (C : Factorization.DIS.HardKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (D : Physlib.Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron)
    (x zHad Q2 : ℝ) : ℝ :=
  ∑ i, sidisChannel C f D h i x zHad Q2

/-- Inclusive-limit theorem when fragmentation factors are identically one. -/
lemma inclusive_limit_of_unit_fragmentation [Fintype Flavor]
    (C : Factorization.DIS.HardKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (D : Physlib.Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron)
    (x zHad Q2 : ℝ)
    (hUnit : ∀ h' i z Q2', D h' i z Q2' = 1) :
    sidisStructureFunction C f D h x zHad Q2
      = Factorization.DIS.loStructureFunction C f x Q2 := by
  simp [sidisStructureFunction, sidisChannel, Factorization.DIS.loStructureFunction, hUnit]

end SIDIS
end DIS
end Scattering
end QFT
end Physlib
