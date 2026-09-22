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

/-- Continuity in the momentum-fraction variable discharges both structural hard-kernel
assumptions: a continuous real function is almost-everywhere strongly measurable, and it is
integrable on the compact interval `[0, 1]`, hence its `[0, 1]`-indicator is integrable on
all of `ℝ`. -/
lemma hardKernelAssumptions_of_continuous (C : HardKernel Flavor)
    (h : ∀ i x Q2, Continuous fun z : ℝ => C i x z Q2) :
    HardKernelAssumptions C := by
  refine ⟨fun i x Q2 => (h i x Q2).aestronglyMeasurable, fun i x Q2 => ?_⟩
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
    (h i x Q2).integrableOn_Icc

/-- The flavor-weighted regular hard kernel: one weight per parton flavor, constant in the
momentum-fraction variable `z`.

This is the simplest genuinely concrete element of `HardKernel`. It is *not* the Born
coefficient function of deep inelastic scattering: that is `e_i^2 δ(1 - z)`, a distribution,
which is not a member of `HardKernel Flavor = Flavor → ℝ → ℝ → ℝ → ℝ`. -/
def constantHardKernel (w : Flavor → ℝ) : HardKernel Flavor :=
  fun i _x _z _Q2 => w i

/-- The constant hard kernel satisfies the structural hard-kernel assumptions, so
`HardKernelAssumptions` has a concrete model and is not vacuously unsatisfiable. -/
lemma constantHardKernel_hardKernelAssumptions (w : Flavor → ℝ) :
    HardKernelAssumptions (constantHardKernel w) := by
  refine hardKernelAssumptions_of_continuous _ fun i x Q2 => ?_
  simp only [constantHardKernel]
  exact continuous_const

end DIS
end Factorization
end QFT
end Physlib
