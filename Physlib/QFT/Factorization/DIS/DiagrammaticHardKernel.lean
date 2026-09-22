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

/-- The tree-level Born amplitude is continuous in the momentum-fraction variable: it is
linear in `z` with a coefficient built from the diagram data and the external kinematics. -/
lemma continuous_treeLevelAmplitude (diag : TreeLevelQuarkDiagram) (x Q2 : ℝ) :
    Continuous fun z : ℝ => treeLevelAmplitude diag x Q2 z := by
  simp only [treeLevelAmplitude]
  fun_prop

/-- Bridge theorem: tree-level amplitude contracts imply hard-kernel assumptions.

Measurability and integrability are *proved* here from continuity of the tree-level
amplitude. They were previously additional fields of
`TreeLevelQuarkAmplitudeAssumptions`, i.e. assumed alongside the kernel identity; the
bundle now carries only the kernel identity itself. -/
lemma hardKernelAssumptions_of_treeLevel
    (diag : TreeLevelQuarkDiagram)
    (C : HardKernel Flavor)
    (h : TreeLevelQuarkAmplitudeAssumptions diag C) :
    HardKernelAssumptions C := by
  refine hardKernelAssumptions_of_continuous C fun i x Q2 => ?_
  have hEq : (fun z : ℝ => C i x z Q2) = fun z : ℝ => treeLevelAmplitude diag x Q2 z := by
    funext z
    exact h.kernel_eq i x z Q2
  rw [hEq]
  exact continuous_treeLevelAmplitude diag x Q2

/-- Main bridge theorem: a free-quark Born process yields a hard kernel that satisfies the
structural hard-kernel assumptions, and an LO-factorized structure function.

The previous statement took a `FreeQuarkBornKernelAssumptions` bundle whose only content
beyond the amplitude contract was an arbitrary `Prop` field with a witness, and used neither
part: it was `loStructureFunction_isFactorized` with unused hypotheses. Both conjuncts here
follow from the amplitude contract alone. -/
lemma freeQuarkBornStructureFunction_isLOFactorized
    [Fintype Flavor]
    (diag : TreeLevelQuarkDiagram)
    (C : HardKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (h : TreeLevelQuarkAmplitudeAssumptions diag C) :
    HardKernelAssumptions C ∧ IsLOFactorized (loStructureFunction C f) C f :=
  ⟨hardKernelAssumptions_of_treeLevel diag C h, loStructureFunction_isFactorized C f⟩

/-- Corollary: free-quark Born amplitudes induce an LO factorization whose channel
convolutions are driven by the explicit tree-level amplitude rather than by an abstract
coefficient kernel. Unlike the previous version, this consumes the amplitude contract. -/
lemma freeQuarkBorn_defines_loFactorization
    [Fintype Flavor]
    (diag : TreeLevelQuarkDiagram)
    (C : HardKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (h : TreeLevelQuarkAmplitudeAssumptions diag C)
    (x Q2 : ℝ) :
    loStructureFunction C f x Q2
      = ∑ i, Convolution.convolveAt (fun x' z => treeLevelAmplitude diag x' Q2 z)
          (fun z => f i z Q2) x := by
  have hK : ∀ i : Flavor,
      (fun x' z : ℝ => C i x' z Q2) = fun x' z : ℝ => treeLevelAmplitude diag x' Q2 z := by
    intro i
    funext x' z
    exact h.kernel_eq i x' z Q2
  simp only [loStructureFunction, loChannel]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hK i]

end DiagrammaticHardKernel
end DIS
end Factorization
end QFT
end Physlib
