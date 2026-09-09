/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.Basic
/-!

# Two-Loop Diagrammatic Bridge

This module scaffolds the future derivation objects for two-loop diagrammatic
calculations. It packages the external diagram domain, the classification map
into a curated finite label set, and the completeness/support properties needed
for downstream renormalization and observable bridges.

The current repository does not yet contain a concrete two-loop evaluation
package analogous to the one-loop self-energy bridge, so this module provides a
reusable certificate object for future derivation work.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace PerturbationTheory
namespace FeynmanDiagrams

open scoped BigOperators

/-- Bridge certificate for a two-loop diagrammatic derivation.

The `Diagram` type is the external analytic diagram domain, `classify` maps it
into the curated finite label set, and `reducedAmplitude` stores the reduced
amplitude assigned to each label. -/
structure TwoLoopDiagrammaticBridge
    (Label : Type)
  (curatedLabels : Finset Label) : Type 2 where
  /-- External analytic diagram domain. -/
  Diagram : Type
  /-- Admissible diagrams in the external domain. -/
  admissible : Diagram → Prop
  /-- Classification map from external diagrams to curated labels. -/
  classify : Diagram → Label
  /-- Admissible diagrams classify into the curated finite label set. -/
  classify_mem :
    ∀ d : Diagram, admissible d → classify d ∈ curatedLabels
  /-- Every curated label is realized by at least one admissible diagram. -/
  covers :
    ∀ l : Label, l ∈ curatedLabels → ∃ d : Diagram, admissible d ∧ classify d = l
  /-- Reduced amplitude attached to each curated label. -/
  reducedAmplitude : Label → ℝ
  /-- Labels outside the curated set have vanishing reduced amplitude. -/
  outsideSupportZero :
    ∀ l : Label, l ∉ curatedLabels → reducedAmplitude l = 0

namespace TwoLoopBridge

variable {Label : Type} {curatedLabels : Finset Label}

/-- The curated two-loop label set is exactly the image of admissible diagrams
under the bridge classification map. -/
theorem completeEnumeration
    (B : TwoLoopDiagrammaticBridge Label curatedLabels) :
    ∀ l : Label,
      l ∈ curatedLabels ↔ ∃ d : B.Diagram, B.admissible d ∧ B.classify d = l := by
  intro l
  constructor
  · intro hl
    exact B.covers l hl
  · intro hWitness
    rcases hWitness with ⟨d, hdAdm, hcls⟩
    exact hcls.symm ▸ B.classify_mem d hdAdm

/-- The bridge certifies vanishing reduced amplitude outside the curated set. -/
theorem supportCompleteness
    (B : TwoLoopDiagrammaticBridge Label curatedLabels)
    (l : Label)
    (hlOut : l ∉ curatedLabels) :
    B.reducedAmplitude l = 0 := by
  exact B.outsideSupportZero l hlOut

/-- Convenience theorem that packages the enumeration certificate and support
completeness into a single interface statement. -/
theorem completeBridgeCertificate
    (B : TwoLoopDiagrammaticBridge Label curatedLabels) :
    (∀ l : Label,
      l ∈ curatedLabels ↔ ∃ d : B.Diagram, B.admissible d ∧ B.classify d = l) ∧
    (∀ l : Label, l ∉ curatedLabels → B.reducedAmplitude l = 0) := by
  exact ⟨completeEnumeration B, supportCompleteness B⟩

end TwoLoopBridge

end FeynmanDiagrams
end PerturbationTheory
end QFT
end Physlib
