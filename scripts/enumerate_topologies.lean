/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.TopologyEnumeration
import Physlib.QFT.Scattering.DIS.PVES.Examples.Moller

/-!
# Lean executable: Møller two-loop topology enumeration

Run with:
```
lake build enumerate_topologies && lake exe enumerate_topologies
```

Output:
- Graph records generated from descriptor-admissible Møller rows.
- Tree-level and one-loop generic topology records extracted from the
  descriptor-driven search.
- One-loop topology candidates classified by Møller one-loop label.
- For each two-loop topology class, all concrete diagrams with their
  momentum assignments, integrand shape, and evaluated master integral.
-/

open Physlib.QFT.PerturbationTheory.FeynmanDiagrams
open Physlib.QFT.PerturbationTheory.DimensionalRegularization
open Physlib.QFT.Scattering.DIS.PVES.Examples

/-! ## Møller theory descriptor

The descriptor captures the interaction alphabet, allowed valences, and order budget
for the Møller ee→ee two-loop process.  Admissible topology rows are derived
automatically from the budget via `generateConstraintRowsFromBudget`; no hand-curated
row list is required. -/

def mollerTheoryDescriptor : TheoryDescriptor :=
  { name := "Moller ee->ee two-loop"
    externalNodeCount := 4
    externalLegs :=
      [ExternalLegKind.electron,
       ExternalLegKind.electron,
       ExternalLegKind.electron,
       ExternalLegKind.electron]
    nodeAlphabet := topologyNodeAlphabet
    edgeAlphabet := topologyEdgeAlphabet
    allowedNodeValence := fun node n =>
      match node with
      | .gaugeInteraction           => n <= 4
      | .ghostInteraction           => n <= 2
      | .fermionSelfEnergyInsertion => n <= 2
      | .countertermInsertion       => n <= 1
    allowedEdgeValence := fun edge n =>
      match edge with
      | .gaugePropagator   => n <= 4
      | .ghostPropagator   => n <= 2
      | .fermionPropagator => n <= 2
      | .countertermEdge   => n <= 1
    orderBudget :=
      { maxLoopOrder          := 2
        maxInteractionNodeCount := 4
        maxInternalEdgeCount    := 4 }
    -- constraintRows intentionally omitted: derived from orderBudget automatically
  }

def mollerConstraints : List TopologyConstraint :=
  admissibleConstraintsOfTheory mollerTheoryDescriptor

/-! ## Loop-order helpers -/

def loopOrderOfCounts (internalEdgeCount interactionNodeCount : ℕ) : ℕ :=
  internalEdgeCount + 1 - interactionNodeCount

def graphLoopOrder (g : TopologyGraph) : ℕ :=
  loopOrderOfCounts g.internalEdgeKinds.length g.interactionNodes.length

def candidateLoopOrder (c : TopologyCandidate) : ℕ :=
  loopOrderOfCounts c.propagatorCount c.vertexCount

def loopOrderLabel (n : ℕ) : String :=
  match n with
  | 0 => "tree-level"
  | 1 => "one-loop"
  | 2 => "two-loop"
  | k => s!"{k}-loop"

/-! ## Pretty-printing helpers — graph/candidate layer -/

def reprNodeKind (n : TopologyNodeKind) : String :=
  match n with
  | .gaugeInteraction           => "gauge"
  | .ghostInteraction           => "ghost"
  | .fermionSelfEnergyInsertion => "fermion-SE"
  | .countertermInsertion       => "counterterm"

def reprEdgeKind (e : TopologyEdgeKind) : String :=
  match e with
  | .gaugePropagator   => "gauge"
  | .ghostPropagator   => "ghost"
  | .fermionPropagator => "fermion"
  | .countertermEdge   => "counterterm"

def reprGraph (g : TopologyGraph) : String :=
  let nodes := "[" ++ (", ".intercalate (g.interactionNodes.map reprNodeKind)) ++ "]"
  let edges := "[" ++ (", ".intercalate (g.internalEdgeKinds.map reprEdgeKind)) ++ "]"
  s!"  id={g.diagramId}  loop={graphLoopOrder g} ({loopOrderLabel (graphLoopOrder g)})" ++
  s!"  ext={g.externalNodeCount}  sym={g.symmetryFactor}" ++
  s!"  nodes={nodes}  edges={edges}"

def reprBool (b : Bool) : String := if b then "yes" else "no"

def reprCandidate (c : TopologyCandidate) : String :=
  s!"  id={c.diagramId}" ++
  s!"  loop={candidateLoopOrder c} ({loopOrderLabel (candidateLoopOrder c)})" ++
  s!"  propagators={c.propagatorCount}" ++
  s!"  vertices={c.vertexCount}" ++
  s!"  sym={c.symmetryFactor}" ++
  s!"  ghost={reprBool c.hasGhostLine}" ++
  s!"  counterterm={reprBool c.hasCountertermInsertion}" ++
  s!"  vertexBox={reprBool c.isVertexBoxInterference}" ++
  s!"  fermionSE={c.fermionSelfEnergyInsertions}" ++
  s!"  nestedGauge={reprBool c.hasNestedGaugeSelfEnergy}"

def topologyLabel (c : TopologyCandidate) : String :=
  if c.hasCountertermInsertion then "counterterm-inserted-one-loop"
  else if c.isVertexBoxInterference then "vertex-corrected-box-interference"
  else if c.fermionSelfEnergyInsertions == 2 then "double-fermion-self-energy"
  else if c.hasNestedGaugeSelfEnergy then "nested-gauge-boson-self-energy"
  else if c.hasGhostLine then "gauge-ghost-mixed"
  else "unclassified"

def reprOneLoopLabel (l : MollerOneLoopDiagramLabel) : String :=
  match l with
  | .gaugeBosonSelfEnergy => "gauge-boson-self-energy"
  | .ghostSelfEnergy => "ghost-self-energy"
  | .fermionSelfEnergy => "fermion-self-energy"

/-! ## Pretty-printing helpers — two-loop diagram layer -/

def reprMomentum (m : Momentum) : String :=
  s!"(E={m.E}, px={m.p.1}, py={m.p.2.1}, pz={m.p.2.2})"

def reprTwoLoopLabel (l : MollerTwoLoopDiagramLabel) : String :=
  match l with
  | .nestedGaugeBosonSelfEnergy       => "nested-gauge-boson-self-energy"
  | .gaugeGhostMixed                  => "gauge-ghost-mixed"
  | .vertexCorrectedBoxInterference   => "vertex-corrected-box-interference"
  | .doubleFermionSelfEnergy          => "double-fermion-self-energy"
  | .countertermInsertedOneLoop       => "counterterm-inserted-one-loop"

def reprTwoLoopMaster (I : TwoLoopMasterIntegral) : String :=
  s!"poleCoeff={I.poleCoeff}  finitePart={I.finitePart}"

def reprTwoLoopDiagram (d : MollerTwoLoopDiagramData) : String :=
  let integ := d.integrand
  s!"  label       : {reprTwoLoopLabel d.label}\n" ++
  s!"  k1          : {reprMomentum d.loopMomentum1}\n" ++
  s!"  k2          : {reprMomentum d.loopMomentum2}\n" ++
  s!"  p_ext       : {reprMomentum d.externalMomentum}\n" ++
  s!"  denominators: {integ.denominators.length}\n" ++
  s!"  numerator   : {integ.numeratorTerms.length} term(s)\n" ++
  s!"  master      : {reprTwoLoopMaster integ.reducedMaster}"

def reprTwoLoopEvaluation (e : MollerTwoLoopDiagramEvaluation) : String :=
  reprTwoLoopDiagram e.diagram ++
  s!"\n  target      : {reprTwoLoopMaster e.target}"

/-! ## Main -/

def main : IO Unit := do
  IO.println "=== Møller two-loop topology enumeration ==="
  IO.println ""

  -- Section 1: graphs from constraints
  let graphs := enumerateGraphsFromTheoryDescriptor mollerTheoryDescriptor
  let treeGraphs := graphs.filter (fun g => graphLoopOrder g == 0)
  let oneLoopGraphs := graphs.filter (fun g => graphLoopOrder g == 1)
  let twoLoopGraphs := graphs.filter (fun g => graphLoopOrder g == 2)
  IO.println
    s!"Generated {graphs.length} graphs from {mollerConstraints.length} descriptor-admissible constraints."
  IO.println
    s!"Loop-order split: tree={treeGraphs.length}, one-loop={oneLoopGraphs.length}, two-loop={twoLoopGraphs.length}"
  IO.println ""
  IO.println "--- Graphs ---"
  for g in graphs do
    IO.println (reprGraph g)
  IO.println ""

  IO.println "--- Tree-level descriptor diagrams ---"
  if treeGraphs.isEmpty then
    IO.println "  none"
  else
    for g in treeGraphs do
      IO.println (reprGraph g)
  IO.println ""

  IO.println "--- One-loop descriptor diagrams ---"
  if oneLoopGraphs.isEmpty then
    IO.println "  none"
  else
    for g in oneLoopGraphs do
      IO.println (reprGraph g)
  IO.println ""

  -- Section 2: candidates classified by topology
  let candidates := enumerateCandidatesFromTheoryDescriptor mollerTheoryDescriptor
  let treeCandidates := candidates.filter (fun c => candidateLoopOrder c == 0)
  let oneLoopCandidates := candidates.filter (fun c => candidateLoopOrder c == 1)
  IO.println "--- Candidates ---"
  for c in candidates do
    IO.println s!"[{topologyLabel c}]"
    IO.println (reprCandidate c)
  IO.println ""

  IO.println "--- Tree-level topology candidates ---"
  if treeCandidates.isEmpty then
    IO.println "  none"
  else
    for c in treeCandidates do
      IO.println s!"[{topologyLabel c}]"
      IO.println (reprCandidate c)
  IO.println ""

  IO.println "--- One-loop topology candidates ---"
  if oneLoopCandidates.isEmpty then
    IO.println "  none"
  else
    for c in oneLoopCandidates do
      let label :=
        match mollerClassifyOneLoopTopologyCandidate c with
        | some cls => reprOneLoopLabel cls
        | none => topologyLabel c
      IO.println s!"[{label}]"
      IO.println (reprCandidate c)
  IO.println ""

  IO.println "--- One-loop class blocks (from Moller one-loop class enumeration) ---"
  for (cls, classCandidates) in mollerOneLoopTopologyClassEnumeration do
    IO.println s!"{reprOneLoopLabel cls}: {classCandidates.length} candidate(s)"
  IO.println ""

  IO.println "--- Two-loop class blocks (from Moller class enumeration) ---"
  for (cls, classCandidates) in mollerTopologyClassEnumeration do
    IO.println s!"{reprTwoLoopLabel cls}: {classCandidates.length} candidate(s)"
  IO.println ""

  -- Section 3: all two-loop diagrams grouped by topology class
  IO.println "--- Two-loop diagrams by topology class ---"
  IO.println ""
  let evals := mollerCanonicalTwoLoopEvaluations
  let classOrder := mollerTopologyClassOrder
  for cls in classOrder do
    let inClass := evals.filter (fun e => e.diagram.label == cls)
    IO.println s!"=== {reprTwoLoopLabel cls} ({inClass.length} diagram(s)) ==="
    for e in inClass do
      IO.println (reprTwoLoopEvaluation e)
      IO.println ""

  -- Section 4: summary table
  IO.println "--- Summary: topology class → diagram count → master ---"
  for cls in classOrder do
    let inClass := evals.filter (fun e => e.diagram.label == cls)
    match inClass.head? with
    | some e =>
      IO.println s!"  {reprTwoLoopLabel cls}: {inClass.length} diagram(s), master pole={e.target.poleCoeff}"
    | none =>
      IO.println s!"  {reprTwoLoopLabel cls}: 0 diagrams"
  IO.println ""
  IO.println "Done."
