/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.FiniteSearch

/-!
# Topology enumeration

This module provides a generic finite enumeration layer for graph/topology
classification workflows. Concrete physics examples instantiate the generic
structures with process-specific labels and constraints.
-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace PerturbationTheory
namespace FeynmanDiagrams

/-- Interaction-node kinds used by a generic topology search. -/
inductive TopologyNodeKind where
  | gaugeInteraction
  | ghostInteraction
  | fermionSelfEnergyInsertion
  | countertermInsertion
  deriving DecidableEq, Repr

/-- Internal-propagator kinds used by a generic topology search. -/
inductive TopologyEdgeKind where
  | gaugePropagator
  | ghostPropagator
  | fermionPropagator
  | countertermEdge
  deriving DecidableEq, Repr

/-- External-particle species carried by a process descriptor. -/
inductive ExternalLegKind where
  | unspecified
  | electron
  | positron
  | photon
  | neutrino
  | quark
  | gluon
  | ghost
  deriving DecidableEq, Repr

/-- Compact graph container for a generated topology. -/
structure TopologyGraph where
  diagramId : ℕ
  externalNodeCount : ℕ
  externalLegs : List ExternalLegKind
  interactionNodes : List TopologyNodeKind
  internalEdgeKinds : List TopologyEdgeKind
  symmetryFactor : ℕ

/-- Default external-leg payload for process-agnostic graphs. -/
def unspecifiedExternalLegs (n : ℕ) : List ExternalLegKind :=
  List.replicate n ExternalLegKind.unspecified

/-- External-leg metadata on a graph is well formed when it has one entry per external node. -/
def TopologyGraph.hasWellFormedExternalLegs (graph : TopologyGraph) : Prop :=
  graph.externalLegs.length = graph.externalNodeCount

/-- Typed permutation group acting on `n` ordered external legs. -/
abbrev ExternalLegPerm (n : ℕ) := Equiv.Perm (Fin n)

/-- Replace the ordered external-leg content of a graph. -/
def TopologyGraph.withExternalLegs
    (graph : TopologyGraph)
    (externalLegs : List ExternalLegKind) : TopologyGraph :=
  { graph with externalLegs := externalLegs }

/-- Permute the ordered external-leg content of a well-formed graph. -/
def TopologyGraph.permuteExternalLegs
    (graph : TopologyGraph)
    (σ : ExternalLegPerm graph.externalNodeCount)
    (h : graph.hasWellFormedExternalLegs) : TopologyGraph :=
  graph.withExternalLegs
    (List.ofFn (fun i : Fin graph.externalNodeCount =>
      graph.externalLegs.get (Fin.cast h.symm (σ i))))

/-- Crossing equivalence between graphs: internal topology data agrees and the
external legs differ only by permutation. -/
def TopologyGraph.IsCrossingEquivalent
    (graph other : TopologyGraph) : Prop :=
  graph.diagramId = other.diagramId ∧
    graph.externalNodeCount = other.externalNodeCount ∧
    graph.interactionNodes = other.interactionNodes ∧
    graph.internalEdgeKinds = other.internalEdgeKinds ∧
    graph.symmetryFactor = other.symmetryFactor ∧
    graph.externalLegs ~ other.externalLegs

theorem TopologyGraph.hasWellFormedExternalLegs_unspecified (n : ℕ) :
    (TopologyGraph.mk 0 n (unspecifiedExternalLegs n) [] [] 1).hasWellFormedExternalLegs := by
  simp [TopologyGraph.hasWellFormedExternalLegs, unspecifiedExternalLegs]

theorem TopologyGraph.hasWellFormedExternalLegs_withExternalLegs
    (graph : TopologyGraph)
    (externalLegs : List ExternalLegKind)
    (h : externalLegs.length = graph.externalNodeCount) :
    (graph.withExternalLegs externalLegs).hasWellFormedExternalLegs := by
  simpa [TopologyGraph.hasWellFormedExternalLegs, TopologyGraph.withExternalLegs] using h

theorem TopologyGraph.hasWellFormedExternalLegs_permuteExternalLegs
    (graph : TopologyGraph)
    (σ : ExternalLegPerm graph.externalNodeCount)
    (h : graph.hasWellFormedExternalLegs) :
    (graph.permuteExternalLegs σ h).hasWellFormedExternalLegs := by
  simp [TopologyGraph.permuteExternalLegs, TopologyGraph.hasWellFormedExternalLegs,
    TopologyGraph.withExternalLegs]

theorem TopologyGraph.permuteExternalLegs_refl
    (graph : TopologyGraph)
    (h : graph.hasWellFormedExternalLegs) :
    graph.permuteExternalLegs (Equiv.refl _) h = graph := by
  cases graph with
  | mk diagramId externalNodeCount externalLegs interactionNodes internalEdgeKinds symmetryFactor =>
      cases h
      simp [TopologyGraph.permuteExternalLegs, TopologyGraph.withExternalLegs]

theorem TopologyGraph.isCrossingEquivalent_refl (graph : TopologyGraph) :
    graph.IsCrossingEquivalent graph := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, List.Perm.refl _⟩

theorem TopologyGraph.isCrossingEquivalent_symm {graph other : TopologyGraph}
    (h : graph.IsCrossingEquivalent other) :
    other.IsCrossingEquivalent graph := by
  rcases h with ⟨hId, hExt, hNodes, hEdges, hSym, hPerm⟩
  exact ⟨hId.symm, hExt.symm, hNodes.symm, hEdges.symm, hSym.symm, hPerm.symm⟩

theorem TopologyGraph.isCrossingEquivalent_trans {graph mid other : TopologyGraph}
    (h₁ : graph.IsCrossingEquivalent mid)
    (h₂ : mid.IsCrossingEquivalent other) :
    graph.IsCrossingEquivalent other := by
  rcases h₁ with ⟨hId₁, hExt₁, hNodes₁, hEdges₁, hSym₁, hPerm₁⟩
  rcases h₂ with ⟨hId₂, hExt₂, hNodes₂, hEdges₂, hSym₂, hPerm₂⟩
  exact ⟨hId₁.trans hId₂, hExt₁.trans hExt₂, hNodes₁.trans hNodes₂,
    hEdges₁.trans hEdges₂, hSym₁.trans hSym₂, hPerm₁.trans hPerm₂⟩

/-- Exact node/edge incidence constraints for a generated topology. -/
structure TopologyConstraint where
  diagramId : ℕ
  externalNodeCount : ℕ
  symmetryFactor : ℕ
  interactionNodeCount : ℕ
  gaugeInteractionCount : ℕ
  ghostInteractionCount : ℕ
  fermionSelfEnergyInsertionCount : ℕ
  countertermInsertionCount : ℕ
  internalEdgeCount : ℕ
  gaugePropagatorCount : ℕ
  ghostPropagatorCount : ℕ
  fermionPropagatorCount : ℕ
  countertermEdgeCount : ℕ

/-- Coarse perturbative-order budget used to constrain admissible topology rows. -/
structure TopologyOrderBudget where
  /-- Maximum loop order allowed by the theory descriptor. -/
  maxLoopOrder : ℕ
  /-- Maximum number of interaction nodes per admissible topology row. -/
  maxInteractionNodeCount : ℕ
  /-- Maximum number of internal propagators per admissible topology row. -/
  maxInternalEdgeCount : ℕ

/-- Coarse loop-order estimate from incidence counts.
For connected scattering topologies this matches `L = I - V + 1`. -/
def TopologyConstraint.estimatedLoopOrder (constraint : TopologyConstraint) : ℕ :=
  constraint.internalEdgeCount + 1 - constraint.interactionNodeCount

/-- Enumerate all quadruples `(a, b, c, d)` of natural numbers with `a + b + c + d = n`. -/
private def splitQuadruples (n : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range (n + 1)).bind (fun a =>
  (List.range (n - a + 1)).bind (fun b =>
  (List.range (n - a - b + 1)).map (fun c =>
    (a, b, c, n - a - b - c))))

/-- Generate all `TopologyConstraint` rows whose node/edge counts lie within `budget`.
Rows are assigned sequential `diagramId`s (1-based) and `symmetryFactor = 1`.
Calling `admissibleConstraintsOfTheory` on these rows applies alphabet and valence
filtering to obtain process-specific admissible rows. -/
def generateConstraintRowsFromBudget
    (externalNodeCount : ℕ)
    (budget : TopologyOrderBudget) : List TopologyConstraint :=
  let rawRows : List TopologyConstraint :=
    (List.range (budget.maxInteractionNodeCount + 1)).bind (fun iN =>
    (List.range (budget.maxInternalEdgeCount + 1)).bind (fun iE =>
    (splitQuadruples iN).bind (fun nodeCounts =>
    (splitQuadruples iE).map (fun edgeCounts =>
      let (gI, ghI, fI, ctI) := nodeCounts
      let (gP, ghP, fP, ctE) := edgeCounts
      { diagramId := 0,
        externalNodeCount := externalNodeCount,
        symmetryFactor := 1,
        interactionNodeCount := iN,
        gaugeInteractionCount := gI,
        ghostInteractionCount := ghI,
        fermionSelfEnergyInsertionCount := fI,
        countertermInsertionCount := ctI,
        internalEdgeCount := iE,
        gaugePropagatorCount := gP,
        ghostPropagatorCount := ghP,
        fermionPropagatorCount := fP,
        countertermEdgeCount := ctE }))))
  rawRows.mapIdx (fun idx row => { row with diagramId := idx + 1 })

/-- External-leg metadata is well formed when it is omitted or when it has one
entry per external node. -/
def TheoryDescriptor.hasWellFormedExternalLegs (descriptor : TheoryDescriptor) : Bool :=
  descriptor.externalLegs.isEmpty ||
    descriptor.externalLegs.length = descriptor.externalNodeCount

/-- Theory descriptor for topology enumeration.
The interface captures the interaction alphabet, admissibility policy, and order budget
for a concrete theory or process.  When `constraintRows` is empty (the default) the
full budget-generated search space is used; supply a non-empty list to restrict
enumeration to a hand-curated subset for backward compatibility. -/
structure TheoryDescriptor where
  /-- Human-readable descriptor name for diagnostics and scripts. -/
  name : String
  /-- Fixed external-node count expected for admissible rows. -/
  externalNodeCount : ℕ
  /-- Ordered external-particle content for the process.
  Leave empty to keep the descriptor process-agnostic on external species. -/
  externalLegs : List ExternalLegKind := []
  /-- Interaction-node alphabet for this theory. -/
  nodeAlphabet : List TopologyNodeKind
  /-- Internal-propagator alphabet for this theory. -/
  edgeAlphabet : List TopologyEdgeKind
  /-- Allowed interaction-node valences (coarse count-level policy by node kind). -/
  allowedNodeValence : TopologyNodeKind → ℕ → Bool
  /-- Allowed internal-propagator valences (coarse count-level policy by edge kind). -/
  allowedEdgeValence : TopologyEdgeKind → ℕ → Bool
  /-- Perturbative order and size budget for admissible rows. -/
  orderBudget : TopologyOrderBudget
  /-- Optional hand-curated candidate rows.  Leave empty to derive the search space
  automatically from `orderBudget` via `generateConstraintRowsFromBudget`. -/
  constraintRows : List TopologyConstraint := []

/-- Check row-internal node and edge count consistency. -/
def TopologyConstraint.isCountConsistent (constraint : TopologyConstraint) : Bool :=
  (constraint.interactionNodeCount =
      constraint.gaugeInteractionCount +
      constraint.ghostInteractionCount +
      constraint.fermionSelfEnergyInsertionCount +
      constraint.countertermInsertionCount) &&
    (constraint.internalEdgeCount =
      constraint.gaugePropagatorCount +
      constraint.ghostPropagatorCount +
      constraint.fermionPropagatorCount +
      constraint.countertermEdgeCount)

/-- Test whether a topology row is admissible under a theory descriptor. -/
def constraintRespectsTheoryDescriptor
    (descriptor : TheoryDescriptor)
    (constraint : TopologyConstraint) : Bool :=
  let budgetOk :=
    (constraint.interactionNodeCount <= descriptor.orderBudget.maxInteractionNodeCount) &&
      (constraint.internalEdgeCount <= descriptor.orderBudget.maxInternalEdgeCount) &&
      (constraint.estimatedLoopOrder <= descriptor.orderBudget.maxLoopOrder)
  let nodeOk :=
    ((constraint.gaugeInteractionCount = 0 ||
      (descriptor.nodeAlphabet.contains TopologyNodeKind.gaugeInteraction &&
        descriptor.allowedNodeValence TopologyNodeKind.gaugeInteraction
          constraint.gaugeInteractionCount)) &&
    (constraint.ghostInteractionCount = 0 ||
      (descriptor.nodeAlphabet.contains TopologyNodeKind.ghostInteraction &&
        descriptor.allowedNodeValence TopologyNodeKind.ghostInteraction
          constraint.ghostInteractionCount)) &&
    (constraint.fermionSelfEnergyInsertionCount = 0 ||
      (descriptor.nodeAlphabet.contains TopologyNodeKind.fermionSelfEnergyInsertion &&
        descriptor.allowedNodeValence TopologyNodeKind.fermionSelfEnergyInsertion
          constraint.fermionSelfEnergyInsertionCount)) &&
    (constraint.countertermInsertionCount = 0 ||
      (descriptor.nodeAlphabet.contains TopologyNodeKind.countertermInsertion &&
        descriptor.allowedNodeValence TopologyNodeKind.countertermInsertion
          constraint.countertermInsertionCount)))
  let edgeOk :=
    ((constraint.gaugePropagatorCount = 0 ||
      (descriptor.edgeAlphabet.contains TopologyEdgeKind.gaugePropagator &&
        descriptor.allowedEdgeValence TopologyEdgeKind.gaugePropagator
          constraint.gaugePropagatorCount)) &&
    (constraint.ghostPropagatorCount = 0 ||
      (descriptor.edgeAlphabet.contains TopologyEdgeKind.ghostPropagator &&
        descriptor.allowedEdgeValence TopologyEdgeKind.ghostPropagator
          constraint.ghostPropagatorCount)) &&
    (constraint.fermionPropagatorCount = 0 ||
      (descriptor.edgeAlphabet.contains TopologyEdgeKind.fermionPropagator &&
        descriptor.allowedEdgeValence TopologyEdgeKind.fermionPropagator
          constraint.fermionPropagatorCount)) &&
    (constraint.countertermEdgeCount = 0 ||
      (descriptor.edgeAlphabet.contains TopologyEdgeKind.countertermEdge &&
        descriptor.allowedEdgeValence TopologyEdgeKind.countertermEdge
          constraint.countertermEdgeCount)))
  descriptor.hasWellFormedExternalLegs &&
    (constraint.externalNodeCount = descriptor.externalNodeCount) &&
    constraint.isCountConsistent && budgetOk && nodeOk && edgeOk

/-- Descriptor-admissible topology rows.
When `descriptor.constraintRows` is non-empty it is used as the candidate pool
(backward-compatible path).  When it is empty the full budget-generated search
space produced by `generateConstraintRowsFromBudget` is filtered instead. -/
def admissibleConstraintsOfTheory
    (descriptor : TheoryDescriptor) : List TopologyConstraint :=
  let pool :=
    if descriptor.constraintRows.isEmpty then
      generateConstraintRowsFromBudget descriptor.externalNodeCount descriptor.orderBudget
    else
      descriptor.constraintRows
  pool.filter (constraintRespectsTheoryDescriptor descriptor)

/-- Topology candidate obtained from a graph record. -/
structure TopologyCandidate where
  diagramId : ℕ
  propagatorCount : ℕ
  vertexCount : ℕ
  symmetryFactor : ℕ
  hasGhostLine : Bool
  hasCountertermInsertion : Bool
  isVertexBoxInterference : Bool
  fermionSelfEnergyInsertions : ℕ
  hasNestedGaugeSelfEnergy : Bool

/-- Canonical node alphabet for the generic topology search. -/
def topologyNodeAlphabet : List TopologyNodeKind :=
  [TopologyNodeKind.gaugeInteraction,
   TopologyNodeKind.ghostInteraction,
   TopologyNodeKind.fermionSelfEnergyInsertion,
   TopologyNodeKind.countertermInsertion]

/-- Canonical edge alphabet for the generic topology search. -/
def topologyEdgeAlphabet : List TopologyEdgeKind :=
  [TopologyEdgeKind.gaugePropagator,
   TopologyEdgeKind.ghostPropagator,
   TopologyEdgeKind.fermionPropagator,
   TopologyEdgeKind.countertermEdge]

/-- Build a graph from exact incidence constraints by filtering a finite
search space of node and edge signatures. -/
def graphOfConstraint
    (constraint : TopologyConstraint) : TopologyGraph :=
  let nodeMatches : List TopologyNodeKind → Bool := fun nodes =>
    let gaugeCount :=
      (nodes.filter (fun n => decide (n = TopologyNodeKind.gaugeInteraction))).length
    let ghostCount :=
      (nodes.filter (fun n => decide (n = TopologyNodeKind.ghostInteraction))).length
    let fermionCount :=
      (nodes.filter (fun n =>
        decide (n = TopologyNodeKind.fermionSelfEnergyInsertion))).length
    let countertermCount :=
      (nodes.filter (fun n => decide (n = TopologyNodeKind.countertermInsertion))).length
    (nodes.length = constraint.interactionNodeCount) &&
      (gaugeCount = constraint.gaugeInteractionCount) &&
      (ghostCount = constraint.ghostInteractionCount) &&
      (fermionCount = constraint.fermionSelfEnergyInsertionCount) &&
      (countertermCount = constraint.countertermInsertionCount)
  let edgeMatches : List TopologyEdgeKind → Bool := fun edges =>
    let gaugeCount :=
      (edges.filter (fun e => decide (e = TopologyEdgeKind.gaugePropagator))).length
    let ghostCount :=
      (edges.filter (fun e => decide (e = TopologyEdgeKind.ghostPropagator))).length
    let fermionCount :=
      (edges.filter (fun e => decide (e = TopologyEdgeKind.fermionPropagator))).length
    let countertermCount :=
      (edges.filter (fun e => decide (e = TopologyEdgeKind.countertermEdge))).length
    (edges.length = constraint.internalEdgeCount) &&
      (gaugeCount = constraint.gaugePropagatorCount) &&
      (ghostCount = constraint.ghostPropagatorCount) &&
      (fermionCount = constraint.fermionPropagatorCount) &&
      (countertermCount = constraint.countertermEdgeCount)
  match firstMatching (allListsOfLength constraint.interactionNodeCount topologyNodeAlphabet)
      nodeMatches,
    firstMatching (allListsOfLength constraint.internalEdgeCount topologyEdgeAlphabet)
      edgeMatches with
  | some nodes, some edges =>
      TopologyGraph.mk constraint.diagramId constraint.externalNodeCount
        (unspecifiedExternalLegs constraint.externalNodeCount)
        nodes edges constraint.symmetryFactor
  | _, _ =>
      TopologyGraph.mk constraint.diagramId constraint.externalNodeCount
        (unspecifiedExternalLegs constraint.externalNodeCount) [] []
        constraint.symmetryFactor

/-- Canonical graph enumeration produced by filtering a list of exact
constraints through the generic search space. -/
def enumerateGraphs : List TopologyConstraint → List TopologyGraph :=
  List.map graphOfConstraint

/-- Enumerate graphs using descriptor-admissible topology rows. -/
def enumerateGraphsFromTheoryDescriptor
    (descriptor : TheoryDescriptor) : List TopologyGraph :=
  let graphs := enumerateGraphs (admissibleConstraintsOfTheory descriptor)
  if descriptor.externalLegs.isEmpty then
    graphs
  else
    graphs.map (fun graph => graph.withExternalLegs descriptor.externalLegs)

/-- Derive candidates from graphs. Concrete instances can replace this with a
process-specific classifier. -/
def candidateOfGraph (graph : TopologyGraph) : TopologyCandidate :=
  { diagramId := graph.diagramId,
    propagatorCount := graph.internalEdgeKinds.length,
    vertexCount := graph.interactionNodes.length,
    symmetryFactor := graph.symmetryFactor,
    hasGhostLine := graph.internalEdgeKinds.any (fun e =>
      decide (e = TopologyEdgeKind.ghostPropagator)),
    hasCountertermInsertion := graph.interactionNodes.any (fun n =>
      decide (n = TopologyNodeKind.countertermInsertion)) ||
      graph.internalEdgeKinds.any (fun e =>
        decide (e = TopologyEdgeKind.countertermEdge)),
    isVertexBoxInterference :=
      decide (graph.internalEdgeKinds.length = 4) &&
        decide (graph.interactionNodes.length = 4) &&
        decide ((graph.internalEdgeKinds.filter (fun e =>
          decide (e = TopologyEdgeKind.gaugePropagator))).length = 4),
    fermionSelfEnergyInsertions := (graph.interactionNodes.filter (fun n =>
      decide (n = TopologyNodeKind.fermionSelfEnergyInsertion))).length,
    hasNestedGaugeSelfEnergy :=
      decide (graph.internalEdgeKinds.length = 3) &&
        decide (graph.interactionNodes.length = 2) &&
        decide ((graph.internalEdgeKinds.filter (fun e =>
          decide (e = TopologyEdgeKind.gaugePropagator))).length = 3) }

theorem candidateOfGraph_withExternalLegs
    (graph : TopologyGraph)
    (externalLegs : List ExternalLegKind) :
    candidateOfGraph (graph.withExternalLegs externalLegs) = candidateOfGraph graph := by
  rfl

/-- Enumerate candidates from a list of exact constraints. -/
def enumerateCandidates : List TopologyConstraint → List TopologyCandidate :=
  fun constraints =>
    (constraints.map graphOfConstraint).map candidateOfGraph

/-- Enumerate candidates using descriptor-admissible topology rows. -/
def enumerateCandidatesFromTheoryDescriptor
    (descriptor : TheoryDescriptor) : List TopologyCandidate :=
  enumerateCandidates (admissibleConstraintsOfTheory descriptor)

/-- Enumerate class blocks from a canonical class order and classifier.
Each block contains the candidates classified into the corresponding class. -/
def enumerateClassBlocks {α β : Type} [DecidableEq α]
    (classOrder : List α)
    (classify : β → Option α)
    (candidates : List β) : List (α × List β) :=
  classOrder.map (fun cls =>
    (cls, candidates.filter (fun candidate => classify candidate = some cls)))

/-- The class labels in `enumerateClassBlocks` preserve the given class order. -/
theorem enumerateClassBlocks_map_fst {α β : Type} [DecidableEq α]
    (classOrder : List α)
    (classify : β → Option α)
    (candidates : List β) :
    (enumerateClassBlocks classOrder classify candidates).map Prod.fst = classOrder := by
  simp [enumerateClassBlocks]

/-!
Compatibility naming map (transition phase):

Current concrete APIs (kept stable):
- `graphOfConstraint`
- `enumerateGraphs`
- `candidateOfGraph`
- `enumerateCandidates`

New generic/scaffold APIs (preferred for new classifier instances):
- `TopologyClassifierSpec`
- `enumerateClassBlocks` / `enumerateClassBlocksWithSpec`
- `enumerateItemClassBlocks`

The concrete APIs remain supported so downstream modules do not need immediate
renames while adapter migrations proceed.
-/

/-- Classifier specification for a signature space and class taxonomy. -/
structure TopologyClassifierSpec (ClassLabel Signature : Type) where
  classOrder : List ClassLabel
  classify : Signature → Option ClassLabel

/-- Enumerate class blocks from a classifier specification. -/
def enumerateClassBlocksWithSpec {ClassLabel Signature : Type} [DecidableEq ClassLabel]
    (spec : TopologyClassifierSpec ClassLabel Signature)
    (signatures : List Signature) : List (ClassLabel × List Signature) :=
  enumerateClassBlocks spec.classOrder spec.classify signatures

/-- Enumerate class blocks on source items via a signature extractor and classifier spec. -/
def enumerateItemClassBlocks {ClassLabel Signature Item : Type} [DecidableEq ClassLabel]
    (spec : TopologyClassifierSpec ClassLabel Signature)
    (extract : Item → Signature)
    (items : List Item) : List (ClassLabel × List Item) :=
  enumerateClassBlocks spec.classOrder (fun item => spec.classify (extract item)) items

/-- The class labels in `enumerateClassBlocksWithSpec` preserve the class order. -/
theorem enumerateClassBlocksWithSpec_map_fst {ClassLabel Signature : Type}
    [DecidableEq ClassLabel]
    (spec : TopologyClassifierSpec ClassLabel Signature)
    (signatures : List Signature) :
    (enumerateClassBlocksWithSpec spec signatures).map Prod.fst = spec.classOrder := by
  simpa [enumerateClassBlocksWithSpec] using
    enumerateClassBlocks_map_fst
      (classOrder := spec.classOrder)
      (classify := spec.classify)
      (candidates := signatures)

/-- The class labels in `enumerateItemClassBlocks` preserve the class order. -/
theorem enumerateItemClassBlocks_map_fst {ClassLabel Signature Item : Type}
    [DecidableEq ClassLabel]
    (spec : TopologyClassifierSpec ClassLabel Signature)
    (extract : Item → Signature)
    (items : List Item) :
    (enumerateItemClassBlocks spec extract items).map Prod.fst = spec.classOrder := by
  simpa [enumerateItemClassBlocks] using
    enumerateClassBlocks_map_fst
      (classOrder := spec.classOrder)
      (classify := fun item => spec.classify (extract item))
      (candidates := items)

/-- Preferred explicit name for deriving candidates from an already-enumerated graph list.
Compatibility shim: equivalent to mapping `candidateOfGraph`. -/
def deriveCandidatesFromGraphs (graphs : List TopologyGraph) : List TopologyCandidate :=
  graphs.map candidateOfGraph

/-- Preferred explicit name for candidate enumeration from constraints.
Compatibility shim: equal to `enumerateCandidates`. -/
def enumerateCandidatesFromConstraints : List TopologyConstraint → List TopologyCandidate :=
  fun constraints =>
    deriveCandidatesFromGraphs (enumerateGraphs constraints)

/-- One-loop topology classes represented in the generic search layer. -/
inductive OneLoopTopologyClass where
  | gaugeSelfEnergy
  | ghostSelfEnergy
  | fermionSelfEnergy
  deriving DecidableEq, Repr

/-- Canonical one-loop constraints for gauge, ghost, and fermion self-energy classes. -/
def oneLoopTopologyConstraints : List TopologyConstraint :=
  --                                  id ext sym  iN  gI ghI  fI ctI  iE  gP ghP  fP ctE
  [ TopologyConstraint.mk             1   2   1   1   1   0   0   0   1   1   0   0   0,
    TopologyConstraint.mk             2   2   1   1   0   1   0   0   1   0   1   0   0,
    TopologyConstraint.mk             3   2   1   1   0   0   1   0   1   0   0   1   0 ]

/-- One-loop candidates generated from the canonical one-loop constraints. -/
def oneLoopTopologyCandidates : List TopologyCandidate :=
  enumerateCandidates oneLoopTopologyConstraints

/-- Classifier for one-loop topology candidates. -/
def classifyOneLoopTopologyCandidate
    (candidate : TopologyCandidate) : Option OneLoopTopologyClass :=
  if candidate.hasGhostLine then
    some OneLoopTopologyClass.ghostSelfEnergy
  else if 0 < candidate.fermionSelfEnergyInsertions then
    some OneLoopTopologyClass.fermionSelfEnergy
  else if candidate.propagatorCount = 1 then
    some OneLoopTopologyClass.gaugeSelfEnergy
  else
    none

/-- Canonical class order for one-loop topology grouping. -/
def oneLoopTopologyClassOrder : List OneLoopTopologyClass :=
  [OneLoopTopologyClass.gaugeSelfEnergy,
   OneLoopTopologyClass.ghostSelfEnergy,
   OneLoopTopologyClass.fermionSelfEnergy]

/-- Grouped one-loop topology enumeration in canonical class order. -/
def oneLoopTopologyClassEnumeration :
    List (OneLoopTopologyClass × List TopologyCandidate) :=
  enumerateClassBlocks oneLoopTopologyClassOrder
    classifyOneLoopTopologyCandidate oneLoopTopologyCandidates

/-- The grouped one-loop class enumeration preserves canonical class order. -/
theorem oneLoopTopologyClassEnumeration_map_fst :
    oneLoopTopologyClassEnumeration.map Prod.fst = oneLoopTopologyClassOrder := by
  simpa [oneLoopTopologyClassEnumeration] using
    enumerateClassBlocks_map_fst
      (classOrder := oneLoopTopologyClassOrder)
      (classify := classifyOneLoopTopologyCandidate)
      (candidates := oneLoopTopologyCandidates)

end FeynmanDiagrams
end PerturbationTheory
end QFT
end Physlib
