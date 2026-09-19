/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.TopologyEnumeration

/-!
# Crossing symmetry for topology graphs

This module collects crossing-symmetry theorems for the generic topology
enumeration layer.  The graph data and permutation action live in
`TopologyEnumeration`; this module provides the named invariant theorem surface.
-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace PerturbationTheory
namespace FeynmanDiagrams

/-- `candidateOfGraph` is invariant under external-leg permutations. -/
theorem candidateOfGraph_permuteExternalLegs
    (graph : TopologyGraph)
    (σ : ExternalLegPerm graph.externalNodeCount)
    (h : graph.hasWellFormedExternalLegs) :
    candidateOfGraph (graph.permuteExternalLegs σ h) = candidateOfGraph graph := by
  rfl

/-- Crossing-equivalent graphs define the same generic topology candidate. -/
theorem candidateOfGraph_eq_of_isCrossingEquivalent {graph other : TopologyGraph}
    (h : graph.IsCrossingEquivalent other) :
    candidateOfGraph graph = candidateOfGraph other := by
  rcases h with ⟨hId, hExt, hNodes, hEdges, hSym, _hPerm⟩
  cases graph
  cases other
  cases hId
  cases hExt
  cases hNodes
  cases hEdges
  cases hSym
  rfl

/-- Named crossing-symmetry theorem for the generic topology classifier. -/
theorem candidateOfGraph_crossingInvariant {graph other : TopologyGraph}
    (h : graph.IsCrossingEquivalent other) :
    candidateOfGraph graph = candidateOfGraph other :=
  candidateOfGraph_eq_of_isCrossingEquivalent h

end FeynmanDiagrams
end PerturbationTheory
end QFT
end Physlib
