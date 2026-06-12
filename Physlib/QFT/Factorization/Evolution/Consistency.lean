/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.DIS.LO
public import Physlib.QFT.Factorization.Evolution.Basic
/-!

# Evolution/Factorization Consistency

This module provides consistency checks linking evolved PDFs to factorized
observables across scales.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace QFT
namespace Factorization
namespace Evolution

variable {Flavor : Type}

lemma loStructureFunction_eq_of_pdf_eq [Fintype Flavor]
    (C : DIS.HardKernel Flavor)
    (f g : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (hEq : ∀ i z Q2, f i z Q2 = g i z Q2)
    (x Q2 : ℝ) :
    DIS.loStructureFunction C f x Q2 = DIS.loStructureFunction C g x Q2 := by
  simp [DIS.loStructureFunction, DIS.loChannel, hEq]

/-- If the evolved PDFs agree pointwise at two scales, the LO observable agrees too. -/
lemma loStructureFunction_scaleConsistency [Fintype Flavor]
    (C : DIS.HardKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (Q2a Q2b x : ℝ)
    (hKernelEq : ∀ i x' z, C i x' z Q2a = C i x' z Q2b)
    (hEq : ∀ i z, f i z Q2a = f i z Q2b) :
    DIS.loStructureFunction C f x Q2a = DIS.loStructureFunction C f x Q2b := by
  simp [DIS.loStructureFunction, DIS.loChannel, hKernelEq, hEq]

end Evolution
end Factorization
end QFT
end Physlib
