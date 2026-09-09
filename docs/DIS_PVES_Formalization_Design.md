# DIS PVES Formalization Design

## 1. Purpose

This document defines the implementation plan for adding bottoms-up support for parity-violating electron scattering (PVES) in Physlib.

Scope:
- Extend scattering interfaces with electroweak neutral-current ingredients.
- Formalize gamma-Z interference contracts relevant for parity violation.
- Connect interference-level matrix-element decompositions to beam-helicity asymmetries for:
  - electron-electron (Moller-like) scattering,
  - electron-proton scattering.

This is an interface-first formalization plan: contract structures and bridge theorems come first, with explicit assumptions where full dynamics are deferred.

## 2. Design Principles

- Reuse existing abstractions where possible:
  - DIS kinematics and tensors,
  - exclusive decomposition and asymmetry interface style,
  - perturbative gauge-rule contracts.
- Isolate model dependence in assumption bundles.
- Keep first implementation tree-level and neutral-current focused.
- Preserve compatibility with existing QCD/DIS pipeline and module exports.
- Maintain lint and build cleanliness at each stage.

## 3. Target Architecture

### 3.1 New module subtree (planned)

- `Physlib/QFT/Scattering/DIS/PVES/Basic.lean`
- `Physlib/QFT/Scattering/DIS/PVES/Electroweak/Parameters.lean`
- `Physlib/QFT/Scattering/DIS/PVES/Electroweak/NeutralCurrent.lean`
- `Physlib/QFT/Scattering/DIS/PVES/Interference/Basic.lean`
- `Physlib/QFT/Scattering/DIS/PVES/Processes/EE.lean`
- `Physlib/QFT/Scattering/DIS/PVES/Processes/EP.lean`
- `Physlib/QFT/Scattering/DIS/PVES/Examples/Basic.lean`

### 3.2 Export integration

- Add PVES exports through `Physlib/QFT/Scattering/DIS/Basic.lean`.
- Keep PVES APIs orthogonal to current DVCS/DVMP paths.

## 4. Concrete Task List

### Task 1: Scaffold PVES namespace and export wiring

Deliverables:
- Create PVES directory and base `Basic.lean`.
- Add imports/exports through DIS umbrella module.

Acceptance criteria:
- New PVES modules compile standalone.
- DIS umbrella export compiles with PVES included.

### Task 2: Add electroweak parameter and coupling interfaces

Deliverables:
- Define an electroweak parameter record containing:
  - couplings (`g`, `g'`, `e`),
  - weak-mixing controls (`sin2ThetaW`-style field),
  - mediator mass (`mZ`),
  - effective vector/axial couplings for electrons and quark flavors.
- Add consistency/interface lemmas for coupling conventions.

Acceptance criteria:
- Coupling definitions are centralized in one record.
- Core coupling identities are available as reusable lemmas.

### Task 3: Extend neutral-current Feynman-rule contracts

Deliverables:
- Introduce mediator-tagged neutral-current contract layer (photon vs Z).
- Add vector/axial fermion-current assumption bundles.
- Provide interfaces for gamma, Z, and gamma-Z mixed contributions.

Acceptance criteria:
- Contracts support decomposition into EM, weak, and interference pieces.
- Existing QCD and DIS modules remain unaffected.

### Task 4: Add parity-violating interference decomposition interfaces

Deliverables:
- Formal decomposition contract for squared matrix elements:
  - pure electromagnetic,
  - pure weak neutral current,
  - interference (`2 Re(M_gamma M_Z^*)`).
- Define parity-even and parity-odd extraction interfaces.
- Add bridge assumptions isolating helicity-odd dependence to interference term.

Acceptance criteria:
- Helicity-even/odd pieces are separately represented.
- Parity-violating asymmetry source is explicitly captured by interface theorem(s).

### Task 5: Implement electron-electron PVES bridge

Deliverables:
- Define ee helicity-resolved cross-section proxies (`sigmaPlus`, `sigmaMinus`).
- Define left-right asymmetry interface:

  `A_LR = (sigmaPlus - sigmaMinus) / (|sigmaPlus + sigmaMinus| + regularizer)`.

- Prove bridge theorem reducing asymmetry to interference-over-total ratio under decomposition assumptions.

Acceptance criteria:
- End-to-end theorem from decomposition assumptions to ee `A_LR` exists.
- Result parameterized by electroweak coupling record.

### Task 6: Implement electron-proton PVES bridge

Deliverables:
- Define ep process-level assumptions for hadronic weak neutral current response.
- Introduce ep helicity-resolved observable proxies compatible with DIS kinematics.
- Prove ep asymmetry bridge theorem analogous to ee case.

Acceptance criteria:
- ep asymmetry theorem parallels ee theorem structure.
- Hadronic uncertainty is isolated in explicit assumption bundles.

### Task 7: Add examples/sanity checks

Deliverables:
- Add minimal ee and ep instantiations with simple model placeholders.
- Include executable theorem statements demonstrating API usability.

Acceptance criteria:
- At least one ee and one ep example theorem compile.
- No additional axioms beyond declared assumptions.

### Task 8: Lint/build quality gate

Deliverables:
- Run style lint and targeted builds after each phase.
- Final full build validation.

Acceptance criteria:
- No new style-lint failures.
- Targeted PVES module builds pass.
- Full `lake build` passes.

## 5. Required Theorem Milestones

The following theorem milestones define minimum functional completion:

1. Neutral-current coupling consistency theorem(s).
2. Gamma-Z interference decomposition theorem.
3. Helicity-difference extraction theorem.
4. ee asymmetry bridge theorem.
5. ep asymmetry bridge theorem.

## 6. Suggested Execution Order

1. Task 1 (scaffold/export wiring).
2. Task 2 (electroweak parameter layer).
3. Task 3 (neutral-current contracts).
4. Task 4 (interference decomposition interfaces).
5. Task 5 (ee bridge).
6. Task 6 (ep bridge).
7. Task 7 (examples).
8. Task 8 (final lint/build gate).

## 7. Definition of Done

PVES support is considered complete for this phase when:

- PVES modules are integrated into DIS exports.
- ee and ep beam-helicity asymmetry bridge theorems are present.
- Interference-to-asymmetry linkage is formalized and reusable.
- Repository style lint and full build remain green.

## 8. Implementation Status

Task completion status:

- [x] Task 1: Scaffold PVES namespace and export wiring
- [x] Task 2: Add electroweak parameter and coupling interfaces
- [x] Task 3: Extend neutral-current Feynman-rule contracts
- [x] Task 4: Add parity-violating interference decomposition interfaces
- [x] Task 5: Implement electron-electron PVES bridge
- [x] Task 6: Implement electron-proton PVES bridge
- [x] Task 7: Add examples/sanity checks
- [x] Task 8: Lint/build quality gate

## 9. Task 8 Validation Record

Validation run date:
- 2026-06-14

Commands executed:

1. `scripts/lint-style.sh`
2. `lake build Physlib.QFT.Scattering.DIS.PVES.Electroweak.Parameters Physlib.QFT.Scattering.DIS.PVES.Electroweak.NeutralCurrent Physlib.QFT.Scattering.DIS.PVES.Interference.Basic Physlib.QFT.Scattering.DIS.PVES.Processes.EE Physlib.QFT.Scattering.DIS.PVES.Processes.EP Physlib.QFT.Scattering.DIS.PVES.Examples.Basic Physlib.QFT.Scattering.DIS.PVES.Basic Physlib.QFT.Scattering.DIS.Basic`
3. `lake build`

Observed outcomes:

- Style lint completed without reported violations.
- Targeted PVES build completed successfully (`8563 jobs`).
- Full repository build completed successfully (`9051 jobs`).
