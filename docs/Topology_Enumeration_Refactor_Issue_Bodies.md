# Topology Enumeration Refactor Issue Bodies

Copy and paste each section into a GitHub issue.

## TE-00: Interface Freeze and Naming Map

Title:
Topology refactor: freeze names and compatibility policy

Body:
### Scope
- Finalize names for generic pipeline interfaces in TopologyEnumeration.
- Finalize alias strategy for existing public symbols.

### Files
- Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean
- docs/Topology_Enumeration_Refactor_Design.md

### Tasks
1. Add code comment block documenting old-to-new naming map.
2. Mark compatibility shims clearly as transitional.
3. Confirm no downstream rename required in this PR.

### Acceptance Criteria
1. Naming map present in docs and source comment.
2. No behavior changes in enumeration output.

### Validation
1. lake build Physlib.QFT.PerturbationTheory.FeynmanDiagrams.TopologyEnumeration

## TE-01: Generic Core Types and Pipeline Scaffolding

Title:
Topology refactor: add generic graph/signature/classifier scaffolding

Body:
### Scope
- Add generic abstractions for graph payloads, signature extraction, and class partition.

### Files
- Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean

### Tasks
1. Introduce generic helper definitions (type-parameterized where needed).
2. Preserve current concrete topology instance as compatibility layer.
3. Ensure old APIs remain source-compatible for adapters.

### Acceptance Criteria
1. Existing importers compile without edits.
2. New generic symbols are available for adapter migration.

### Validation
1. lake build Physlib.QFT.PerturbationTheory.FeynmanDiagrams.TopologyEnumeration
2. scripts/lint-style.sh

## TE-02: One-Loop Generic Signature Path

Title:
Topology refactor: define generic one-loop signature/classification path

Body:
### Scope
- Represent one-loop class extraction as generic signature plus classifier flow.

### Files
- Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean

### Tasks
1. Introduce one-loop signature definition (minimal invariants only).
2. Add one-loop class order and classifier over signature.
3. Add class-order theorem for grouped class enumeration.

### Acceptance Criteria
1. One-loop grouped class output is stable.
2. Theorem proving class-order preservation compiles.

### Validation
1. lake build Physlib.QFT.PerturbationTheory.FeynmanDiagrams.TopologyEnumeration

## TE-03: Moller One-Loop Adapter Migration

Title:
Topology refactor: migrate Moller one-loop to generic topology pipeline

Body:
### Scope
- Bind generic one-loop classes into Moller one-loop labels.

### Files
- Physlib/QFT/Scattering/DIS/PVES/Examples/Moller.lean

### Tasks
1. Keep canonical order map from generic one-loop classes to Moller labels.
2. Keep or restore canonical-order theorem for Moller one-loop labels.
3. Keep or restore toFinset completeness theorem against curated set.

### Acceptance Criteria
1. Existing one-loop Moller theorem consumers require no semantic changes.
2. Canonical order remains gauge, ghost, fermion.

### Validation
1. lake build Physlib.QFT.Scattering.DIS.PVES.Examples.Moller
2. scripts/lint-style.sh

## TE-04: QCD One-Loop Beta Adapter Migration

Title:
Topology refactor: migrate QCD one-loop beta class bookkeeping to generic topology pipeline

Body:
### Scope
- Use shared one-loop topology source for gluon, ghost, quark class partition.

### Files
- Physlib/QFT/QCD/OneLoopDiagrammaticBridge.lean

### Tasks
1. Keep mapping from generic one-loop classes to QCD beta classes.
2. Keep class-order theorem for QCD class blocks.
3. Keep classwise primitive-pole decomposition lemma and total-sum link.

### Acceptance Criteria
1. Existing QCD beta theorems remain intact.
2. Class order remains gluon, ghost, quark.

### Validation
1. lake build Physlib.QFT.QCD.OneLoopDiagrammaticBridge
2. scripts/lint-style.sh

## TE-05: Moller Two-Loop Signature Migration

Title:
Topology refactor: move Moller two-loop classifier to signature-based interface

Body:
### Scope
- Separate two-loop signature extraction from class decision logic.

### Files
- Physlib/QFT/Scattering/DIS/PVES/Examples/Moller.lean
- Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean (if needed)

### Tasks
1. Define Moller two-loop signature type and extractor.
2. Refactor classifier to consume signature values.
3. Preserve canonical-order and bundle-reconstruction theorem statements.

### Acceptance Criteria
1. Existing two-loop theorem names remain available.
2. Behavior of classified labels is unchanged.

### Validation
1. lake build Physlib.QFT.Scattering.DIS.PVES.Examples.Moller

## TE-06: Proof Hardening and Theorem Normalization

Title:
Topology refactor: standardize classifier theorem suite

Body:
### Scope
- Add consistent theorem patterns across migrated adapters.

### Files
- Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean
- Physlib/QFT/Scattering/DIS/PVES/Examples/Moller.lean
- Physlib/QFT/QCD/OneLoopDiagrammaticBridge.lean

### Tasks
1. Ensure each classifier instance has order theorem.
2. Ensure each classifier instance has completeness theorem.
3. Add optional non-overlap lemmas where cheap to prove.

### Acceptance Criteria
1. Uniform theorem naming pattern exists across one-loop and two-loop paths.
2. No theorem regressions in downstream modules.

### Validation
1. Targeted module builds for touched files.

## TE-07: Script and Documentation Migration

Title:
Topology refactor: migrate scripts and docs to stable generic API names

Body:
### Scope
- Align scripts and docs with final API surface.

### Files
- scripts/enumerate_topologies.lean
- docs/Topology_Enumeration_Refactor_Design.md
- docs/Topology_Enumeration_Refactor_Issue_Bodies.md

### Tasks
1. Update script to use stable post-refactor names only.
2. Document migration notes for maintainers.
3. Record command outputs expected from class enumeration sections.

### Acceptance Criteria
1. Script compiles and runs with expected class-block output.
2. Docs contain no stale symbol references.

### Validation
1. lake build enumerate_topologies
2. lake exe enumerate_topologies
