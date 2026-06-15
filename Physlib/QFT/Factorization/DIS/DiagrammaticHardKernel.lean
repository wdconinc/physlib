/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.DIS.LO
public import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.Basic
/-!

# Diagrammatic Hard-Kernel Bridge

This module connects Feynman diagram amplitudes to DIS hard-kernel interfaces.

The design follows interface-first principles: diagram-to-amplitude evaluation
is represented as explicit contracts, allowing later replacement with full
perturbative proofs.

Key theorem schema:
- A tree-level quark-target Born process yields a coefficient kernel.
- That kernel matches the DIS hard-kernel interface.
- The kernel is LO-factorizable for DIS structure functions.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Factorization
namespace DIS
namespace DiagrammaticHardKernel

open Physlib.QFT.Scattering.DIS

variable {Flavor : Type}

/-- Placeholder type for tree-level quark-target diagram data. -/
structure TreeLevelQuarkDiagram : Type where
  /-- Placeholder for incoming electron/photon data. -/
  incoming : ℝ
  /-- Placeholder for target quark data. -/
  quarkTarget : ℝ
  /-- Placeholder for outgoing parton data. -/
  outgoing : ℝ

/-- Placeholder for evaluated Born amplitude from a tree diagram. -/
def treeLevelAmplitude (diag : TreeLevelQuarkDiagram) (x Q2 z : ℝ) : ℝ :=
  diag.incoming * diag.quarkTarget * diag.outgoing * x * Q2 * z

/-- Contract: the evaluated amplitude induces a well-formed hard kernel. -/
structure TreeLevelQuarkAmplitudeAssumptions
    (diag : TreeLevelQuarkDiagram)
    (C : HardKernel Flavor) : Prop where
  /-- The amplitude-induced kernel matches the declared kernel coefficient function. -/
  kernel_eq : ∀ i x z Q2,
    C i x z Q2 = treeLevelAmplitude diag x Q2 z
  /-- Measurability contract for the tree-level amplitude kernel. -/
  measurable_tree : ∀ (i : Flavor) (x Q2 : ℝ),
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => treeLevelAmplitude diag x Q2 z)
  /-- Integrability contract on the unit interval for the tree-level amplitude kernel. -/
  integrableOnUnit_tree : ∀ (i : Flavor) (x Q2 : ℝ),
    MeasureTheory.Integrable (fun z : ℝ => Set.indicator (Set.Icc (0 : ℝ) 1)
      (fun t => treeLevelAmplitude diag x Q2 t) z)

/-- Bridge theorem: tree-level amplitude contracts imply hard-kernel assumptions. -/
lemma hardKernelAssumptions_of_treeLevel
    (diag : TreeLevelQuarkDiagram)
    (C : HardKernel Flavor)
    (h : TreeLevelQuarkAmplitudeAssumptions diag C) :
    HardKernelAssumptions C := by
  refine ⟨?_, ?_⟩
  · intro i x Q2
    simpa [h.kernel_eq] using h.measurable_tree i x Q2
  · intro i x Q2
    simpa [h.kernel_eq] using h.integrableOnUnit_tree i x Q2

/-- Contract: Free-quark Born process produces a specific coefficient-kernel form. -/
structure FreeQuarkBornKernelAssumptions
    (diag : TreeLevelQuarkDiagram)
    (C : HardKernel Flavor)
  (f : Physlib.Particles.Parton.PDF.Pdf Flavor) : Type where
  /-- Amplitude matches the declared tree-level form. -/
  hAmplitude : TreeLevelQuarkAmplitudeAssumptions diag C
  /-- Witness that the kernel is physical (placeholder contract). -/
  isPhysical : Prop
  /-- Witness that physicality holds. -/
  hIsPhysical : isPhysical

/-- Main bridge theorem: free-quark Born process yields LO-factorized structure function. -/
lemma freeQuarkBornStructureFunction_isLOFactorized
    [Fintype Flavor]
    (diag : TreeLevelQuarkDiagram)
    (C : HardKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
  (_h : FreeQuarkBornKernelAssumptions diag C f) :
    IsLOFactorized (loStructureFunction C f) C f := by
  exact loStructureFunction_isFactorized C f

/-- Corollary: Free-quark Born amplitudes directly induce LO factorization. -/
lemma freeQuarkBorn_defines_loFactorization
    [Fintype Flavor]
    (diag : TreeLevelQuarkDiagram)
    (C : HardKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
  (_h : FreeQuarkBornKernelAssumptions diag C f) :
    ∀ x Q2, loStructureFunction C f x Q2
      = ∑ i, Convolution.convolveAt (fun x' z => C i x' z Q2) (fun z => f i z Q2) x := by
  intro x Q2
  simp [loStructureFunction, loChannel]

end DiagrammaticHardKernel
end DIS
end Factorization
end QFT
end Physlib
