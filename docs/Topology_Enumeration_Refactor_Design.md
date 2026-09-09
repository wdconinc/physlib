# Topology Enumeration Refactor Design

## 1. Purpose

This document defines an implementation-ready refactor plan to make topology
enumeration in Physlib more extensible and more domain-agnostic while preserving
existing Moller and QCD one-loop/two-loop workflows.

Primary outcome:
- Move from a fixed candidate schema toward a parameterized pipeline:
  Graph Enumeration -> Feature Extraction -> Classifier -> Class Partition.

Secondary outcomes:
- Keep existing public APIs usable during migration.
- Preserve current theorem behavior (canonical order, completeness) for Moller
  and QCD adapters.

## 2. Scope

In scope:
- Refactor in `Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean`.
- Adapter updates for:
  - `Physlib/QFT/Scattering/DIS/PVES/Examples/Moller.lean`
  - `Physlib/QFT/QCD/OneLoopDiagrammaticBridge.lean`
- Proof-layer upgrades for class-order and completeness statements.
- Validation and migration strategy.

Out of scope:
- Replacing physical assumptions with full analytic loop-integral derivations.
- Full graph isomorphism/canonical-form normalization across arbitrary loops.
- Broad model-file ingestion (QGRAF/FeynArts parsers).

## 3. Current State Summary

Current architecture already has strong foundations:
- Generic finite graph generation from exact incidence constraints.
- Candidate derivation with a fixed `TopologyCandidate` record.
- Generic class-block helper (`enumerateClassBlocks`).
- Process-specific adapters for Moller and QCD one-loop classes.

Current limitation:
- Candidate features are hardcoded for present use cases (nested gauge, vertex-box,
  etc.), so extension to new processes requires editing core candidate structure.

## 4. Design Goals

1. Generality
- Allow new class systems without modifying core data structures.

2. Backward compatibility
- Keep current APIs available via aliases/shims during migration.

3. Proof stability
- Preserve existing canonical order and completeness theorems, then strengthen.

4. Incremental rollout
- Avoid large risky all-at-once replacement.

5. Build practicality
- Support targeted checks and avoid unnecessary heavy rebuild fanout.

## 5. Target Architecture

## 5.1 Generic pipeline abstraction

Introduce a parameterized pipeline with independent type roles:
- `NodeKind`, `EdgeKind` for graph alphabet.
- `Graph` for enumerated graph payload.
- `Signature` for extracted classification features.
- `ClassLabel` for class taxonomy.

Core functions:
- enumerate graphs from constraints over arbitrary node/edge alphabets.
- extract signatures from graphs.
- classify signatures into optional class labels.
- partition signatures (or source items) by canonical class order.

## 5.2 Classifier specification contract

Introduce a classifier specification record (conceptual):
- `classOrder : List ClassLabel`
- `classify : Signature -> Option ClassLabel`
- Optional proof obligations per instance:
  - determinism (already by function type)
  - order witness
  - completeness over target finite set
  - optional disjointness/covariance lemmas

## 5.3 Adapter layer

Keep domain modules small by only defining:
- process-local signature extraction.
- process-local label mapping.
- process-local theorems linking to existing curated sets.

## 6. Refactor Plan (Phased)

## Phase 0: Interface Freeze and Naming

Goals:
- Freeze naming conventions for new generic abstractions.
- Define migration policy and compatibility aliases.

Tasks:
1. Add refactor notes and naming map to this design doc.
2. Agree on canonical names for:
   - generic graph enumerator interface
   - signature extractor interface
   - classifier spec and class partition helpers
3. Mark existing fixed-schema APIs as compatibility layer (not deprecated yet).

Deliverables:
- This document approved.
- Name map section added to code comments during implementation.

Exit criteria:
- No unresolved naming disputes.

Dependencies:
- none.

## Phase 1: Generic Core Parameterization in TopologyEnumeration

Goals:
- Introduce type-parameterized abstractions while preserving existing behavior.

Tasks:
1. Add generic constraint/graph helper utilities where type parameters are explicit.
2. Introduce signature-agnostic class partition APIs (reuse and generalize current helper).
3. Keep existing `TopologyNodeKind`, `TopologyEdgeKind`, `TopologyConstraint`,
   `TopologyGraph`, `TopologyCandidate` as one concrete instance.
4. Add compatibility wrappers so current call sites compile unchanged.

Deliverables:
- Updated `TopologyEnumeration.lean` with new generic layer plus old shim layer.

Acceptance criteria:
- Existing files compile unchanged.
- New generic APIs are used by at least one migrated adapter in later phases.

Dependencies:
- Phase 0.

## Phase 2: One-Loop Migration (Moller + QCD)

Goals:
- Rebuild one-loop enumeration on top of generic signatures/classes.

Tasks:
1. Define one-loop signature extraction using only generic candidate features needed for
   gauge/ghost/fermion classes.
2. Retain canonical one-loop class order and class completeness theorems in Moller:
   - class order theorem
   - `toFinset` completeness theorem
3. Retain QCD beta class mapping (gluon/ghost/quark) from same generic one-loop source.
4. Add adapter-local theorem linking classwise decomposition to existing primitive pole
   decomposition.

Deliverables:
- Updated one-loop adapters in Moller and QCD bridge.

Acceptance criteria:
- Same class order and class set as current behavior.
- No regression in existing one-loop theorem consumers.

Dependencies:
- Phase 1.

## Phase 3: Two-Loop Migration (Moller)

Goals:
- Move two-loop Moller classifier to generic signature/classifier spec style.

Tasks:
1. Define Moller two-loop signature type with only required invariants.
2. Replace direct if-chain over fixed candidate record with classifier over signature.
3. Preserve current canonical label order theorem and bundle reconstruction theorem.
4. Keep aliases for existing names so scripts and docs remain valid.

Deliverables:
- Updated two-loop classification path in Moller.

Acceptance criteria:
- Existing canonical order theorem still proves.
- Existing bundle map theorem still proves.

Dependencies:
- Phase 1.

## Phase 4: Proof Hardening

Goals:
- Standardize theorem suite for each classifier instance.

Tasks:
1. Add reusable theorem templates for classifier instances:
   - class-order preservation from class-block enumeration
   - filtered-label order theorem where applicable
   - finite-set completeness
2. Add optional non-overlap/disjointness lemmas for priority classifiers.
3. Add extensional equivalence theorem when migrating from old classifier implementation.

Deliverables:
- Uniform theorem pattern in Moller and QCD one-loop adapters.

Acceptance criteria:
- Every classifier instance has order + completeness theorem pair.

Dependencies:
- Phases 2 and 3.

## Phase 5: Tooling and Documentation Updates

Goals:
- Update scripts/docs to use new API names and remove confusion.

Tasks:
1. Update `scripts/enumerate_topologies.lean` to consume new stable APIs only.
2. Add short migration notes to docs for maintainers.
3. Record validation commands and expected outputs.

Deliverables:
- Updated script output path and docs references.

Acceptance criteria:
- Script still prints class blocks and class-ordered summaries.
- No stale references to removed internals.

Dependencies:
- Phases 2 and 3.

## 7. File-Level Work Plan

Core:
- `Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean`

Adapters:
- `Physlib/QFT/Scattering/DIS/PVES/Examples/Moller.lean`
- `Physlib/QFT/QCD/OneLoopDiagrammaticBridge.lean`

Optional script:
- `scripts/enumerate_topologies.lean`

Potential export/wiring files (only if needed):
- `Physlib/QFT/PerturbationTheory/FeynmanDiagrams/Basic.lean`
- `Physlib.lean`

## 8. Compatibility and Migration Strategy

1. Keep old public names as aliases for at least one migration cycle.
2. Introduce new generic names first; switch call sites second.
3. Remove aliases only after all internal call sites and docs migrate.
4. Avoid behavior changes in class order unless explicitly planned.

## 9. Risks and Mitigations

Risk 1: Over-generalizing too early increases proof complexity.
- Mitigation: keep concrete instances first, abstract second.

Risk 2: Classifier drift changes canonical order.
- Mitigation: lock order through explicit `classOrder` values and theorem checks.

Risk 3: Large rebuild fanout in constrained environments.
- Mitigation: prefer targeted diagnostics (`get_errors`) during iterations,
  reserve full builds for phase gates.

Risk 4: API confusion during transition.
- Mitigation: add compatibility aliases and short code comments near shim definitions.

## 10. Validation Plan

Per-phase checks:
1. File-level diagnostics on touched files.
2. Targeted builds for touched modules.
3. Final integration build after Phase 5.

Recommended commands:
1. `scripts/lint-style.sh`
2. `lake build Physlib.QFT.PerturbationTheory.FeynmanDiagrams.TopologyEnumeration`
3. `lake build Physlib.QFT.Scattering.DIS.PVES.Examples.Moller`
4. `lake build Physlib.QFT.QCD.OneLoopDiagrammaticBridge`
5. `lake build`

## 11. Implementation Checklist

- [x] Phase 0 complete
- [x] Phase 1 complete
- [x] Phase 2 complete
- [x] Phase 3 complete
- [x] Phase 4 complete
- [x] Phase 5 complete
- [ ] Final lint/build gates complete

## 11.1 Current Status Snapshot

| Item | Status | Notes |
| --- | --- | --- |
| TE-00 Interface freeze and naming map | Completed | Naming map and transition guidance added in core module comments. |
| TE-01 Generic core scaffolding | Completed | Generic classifier spec and item/signature class-block helpers added. |
| TE-02 One-loop generic path | Completed | Shared one-loop class model and class-block enumeration present. |
| TE-03 Moller one-loop migration | Completed | Generic one-loop mapping, canonical order, and completeness theorems in place. |
| TE-04 QCD one-loop migration | Completed | Generic one-loop mapping to gluon/ghost/quark with class-order theorem and sum lemma. |
| TE-05 Moller two-loop signature migration | Completed | Two-loop signature extraction and signature-level classifier spec now drive candidate classification. |
| TE-06 Proof hardening | Completed | Normalized class-order and completeness theorem names added for migrated two-loop and QCD one-loop paths. |
| TE-07 Script/docs migration | Completed | Script now uses stable generic candidate-enumeration APIs and neutral class-enumeration aliases; docs status synchronized. |

## 12. Definition of Done

This refactor is complete when:
1. Generic signature/classifier pipeline is in place in topology enumeration core.
2. Moller one-loop and two-loop classification use the new architecture (with compatibility aliases as needed).
3. QCD one-loop beta class enumeration uses the same generic one-loop source.
4. Canonical order and completeness theorems are preserved (or strengthened) for all migrated adapters.
5. Style lint and targeted build gates pass, followed by full build under adequate resources.

## 13. Execution Backlog (Issue-Level)

Each issue below is written to be directly copied into a tracker.

## Issue TE-00: Interface Freeze and Naming Map

Title:
- Topology refactor: freeze names and compatibility policy

Scope:
- Finalize names for generic pipeline interfaces in `TopologyEnumeration.lean`.
- Finalize alias strategy for existing public symbols.

Files:
- `docs/Topology_Enumeration_Refactor_Design.md`
- `Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean`

Tasks:
1. Add code comment block documenting old-to-new naming map.
2. Mark compatibility shims clearly as transitional.
3. Confirm no downstream rename required in this PR.

Acceptance criteria:
1. Naming map present in both docs and source comment.
2. No behavior changes in enumeration output.

Validation:
1. `lake build Physlib.QFT.PerturbationTheory.FeynmanDiagrams.TopologyEnumeration`

## Issue TE-01: Generic Core Types and Pipeline Scaffolding

Title:
- Topology refactor: add generic graph/signature/classifier scaffolding

Scope:
- Add generic abstractions for graph payloads, signature extraction, and class partition.

Files:
- `Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean`

Tasks:
1. Introduce generic helper definitions (type-parameterized where needed).
2. Preserve current concrete topology instance as compatibility layer.
3. Ensure old APIs remain source-compatible for adapters.

Acceptance criteria:
1. Existing importers compile without edits.
2. New generic symbols are available for adapter migration.

Validation:
1. `lake build Physlib.QFT.PerturbationTheory.FeynmanDiagrams.TopologyEnumeration`
2. `scripts/lint-style.sh`

## Issue TE-02: One-Loop Generic Signature Path

Title:
- Topology refactor: define generic one-loop signature/classification path

Scope:
- Represent one-loop class extraction as generic signature + classifier flow.

Files:
- `Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean`

Tasks:
1. Introduce one-loop signature definition (minimal invariants only).
2. Add one-loop class order and classifier over signature.
3. Add class-order theorem for grouped class enumeration.

Acceptance criteria:
1. One-loop grouped class output is stable.
2. Theorem proving class-order preservation compiles.

Validation:
1. `lake build Physlib.QFT.PerturbationTheory.FeynmanDiagrams.TopologyEnumeration`

## Issue TE-03: Moller One-Loop Adapter Migration

Title:
- Topology refactor: migrate Moller one-loop to generic topology pipeline

Scope:
- Bind generic one-loop classes into Moller one-loop labels.

Files:
- `Physlib/QFT/Scattering/DIS/PVES/Examples/Moller.lean`

Tasks:
1. Keep canonical order map from generic one-loop classes to Moller labels.
2. Keep/restore canonical-order theorem for Moller one-loop labels.
3. Keep/restore `toFinset` completeness theorem against curated set.

Acceptance criteria:
1. Existing one-loop Moller theorem consumers require no semantic changes.
2. Canonical order remains gauge, ghost, fermion.

Validation:
1. `lake build Physlib.QFT.Scattering.DIS.PVES.Examples.Moller`
2. `scripts/lint-style.sh`

## Issue TE-04: QCD One-Loop Beta Adapter Migration

Title:
- Topology refactor: migrate QCD one-loop beta class bookkeeping to generic topology pipeline

Scope:
- Use shared one-loop topology source for gluon/ghost/quark class partition.

Files:
- `Physlib/QFT/QCD/OneLoopDiagrammaticBridge.lean`

Tasks:
1. Keep mapping from generic one-loop classes to QCD beta classes.
2. Keep class-order theorem for QCD class blocks.
3. Keep classwise primitive-pole decomposition lemma and total-sum link.

Acceptance criteria:
1. Existing QCD beta theorems remain intact.
2. Class order remains gluon, ghost, quark.

Validation:
1. `lake build Physlib.QFT.QCD.OneLoopDiagrammaticBridge`
2. `scripts/lint-style.sh`

## Issue TE-05: Moller Two-Loop Signature Migration

Title:
- Topology refactor: move Moller two-loop classifier to signature-based interface

Scope:
- Separate two-loop signature extraction from class decision logic.

Files:
- `Physlib/QFT/Scattering/DIS/PVES/Examples/Moller.lean`
- `Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean` (only if helper extensions are required)

Tasks:
1. Define Moller two-loop signature type and extractor.
2. Refactor classifier to consume signature values.
3. Preserve canonical-order and bundle-reconstruction theorem statements.

Acceptance criteria:
1. Existing two-loop theorem names remain available.
2. Behavior of classified labels is unchanged.

Validation:
1. `lake build Physlib.QFT.Scattering.DIS.PVES.Examples.Moller`

## Issue TE-06: Proof Hardening and Theorem Normalization

Title:
- Topology refactor: standardize classifier theorem suite

Scope:
- Add consistent theorem patterns across migrated adapters.

Files:
- `Physlib/QFT/PerturbationTheory/FeynmanDiagrams/TopologyEnumeration.lean`
- `Physlib/QFT/Scattering/DIS/PVES/Examples/Moller.lean`
- `Physlib/QFT/QCD/OneLoopDiagrammaticBridge.lean`

Tasks:
1. Ensure each classifier instance has order theorem.
2. Ensure each classifier instance has completeness theorem.
3. Add optional non-overlap lemmas where cheap to prove.

Acceptance criteria:
1. Uniform theorem naming pattern exists across one-loop and two-loop paths.
2. No theorem regressions in downstream modules.

Validation:
1. Targeted module builds for touched files.

## Issue TE-07: Script and Documentation Migration

Title:
- Topology refactor: migrate scripts/docs to stable generic API names

Scope:
- Align scripts and docs with final API surface.

Files:
- `scripts/enumerate_topologies.lean`
- `docs/Topology_Enumeration_Refactor_Design.md`
- optional related docs if references appear

Tasks:
1. Update script to use stable post-refactor names only.
2. Document migration notes for maintainers.
3. Record command outputs expected from class enumeration sections.

Acceptance criteria:
1. Script compiles and runs with expected class-block output.
2. Docs contain no stale symbol references.

Validation:
1. `lake build enumerate_topologies`
2. `lake exe enumerate_topologies`

## 14. PR Slicing Strategy

Use small PRs with strict dependency order.

PR-1:
1. Issue TE-00
2. Issue TE-01

PR-2:
1. Issue TE-02
2. Issue TE-03
3. Issue TE-04

PR-3:
1. Issue TE-05

PR-4:
1. Issue TE-06
2. Issue TE-07

Notes:
1. PR-2 depends on PR-1 merge.
2. PR-3 depends on PR-1 (and may optionally depend on PR-2 if helper reuse is preferred).
3. PR-4 depends on PR-2 and PR-3.

## 15. Merge Gates and Review Checklist

Every PR must satisfy all gates:
1. Style lint passes.
2. Targeted builds for touched modules pass.
3. New or changed theorem statements include short docstrings.
4. No removal of compatibility aliases unless explicitly scheduled.
5. No behavior drift in canonical class order.

Reviewer checklist:
1. Are class-order lists explicit and documented?
2. Do class-partition theorems prove order preservation?
3. Are completeness theorems retained for curated finite sets?
4. Are adapters thin (mapping + local theorem glue) rather than duplicating core logic?

## 16. Rollback and Contingency

If a phase causes proof instability:
1. Keep old concrete classifier path active behind compatibility definitions.
2. Land generic scaffolding without adapter migration.
3. Re-introduce migration in smaller deltas (one adapter at a time).

If environment resources block full validation:
1. Use targeted file diagnostics and targeted module builds.
2. Defer full `lake build` to a dedicated validation window.

## 17. Suggested Milestone Cadence

Milestone A:
1. PR-1 merged.
2. Generic scaffolding available, no behavior change.

Milestone B:
1. PR-2 merged.
2. One-loop Moller and QCD adapters both running on shared generic one-loop source.

Milestone C:
1. PR-3 merged.
2. Moller two-loop uses signature-based classifier flow.

Milestone D:
1. PR-4 merged.
2. Theorem suite normalized, script/docs finalized, full validation complete.
