/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# DIS Hard-Kernel Interface

This module defines coefficient-kernel interfaces for LO factorization statements.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Factorization
namespace DIS

variable {Flavor : Type}

/-- Leading-order coefficient kernels indexed by parton flavor. -/
abbrev HardKernel (Flavor : Type) : Type := Flavor → ℝ → ℝ → ℝ → ℝ

/-- Structural assumptions for a hard kernel used in factorization formulas. -/
structure HardKernelAssumptions (C : HardKernel Flavor) : Prop where
  measurable : ∀ i x Q2, MeasureTheory.AEStronglyMeasurable (fun z : ℝ => C i x z Q2)
  integrableOnUnit : ∀ i x Q2,
    MeasureTheory.Integrable (fun z : ℝ => Set.indicator (Set.Icc (0 : ℝ) 1)
      (fun t => C i x t Q2) z)

end DIS
end Factorization
end QFT
end Physlib
