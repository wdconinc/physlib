# Deep Inelastic Scattering Formalization Design

## 1. Purpose and Scope

This document defines a staged implementation plan for adding formal support for deep inelastic scattering (DIS) to physlib, with a progression toward:

- Collinear parton distribution functions (PDFs)
- Transverse momentum dependent distributions (TMDs)
- Generalized parton distributions (GPDs)

The design emphasizes:

- Incremental theorem-proving milestones
- Explicit dependencies for parallel execution
- Reusable mathematical infrastructure
- A clear separation between physics assumptions and derived consequences

## 2. High-Level Outcomes

When complete, the new framework should support:

- Machine-checked DIS kinematics and tensor decompositions
- Formal definitions of PDF, TMD, and GPD objects with support and normalization structure
- A reusable factorization and convolution layer
- Evolution-equation infrastructure (first DGLAP, later extensions)
- Theorem-level bridges between frameworks (TMD to PDF, GPD forward limit to PDF)

## 3. Design Principles

### 3.1 Layering

Use strict layering so lower levels remain domain-agnostic:

1. Mathematical infrastructure
2. Kinematics and tensors
3. Distribution objects
4. Factorization and evolution
5. Specialized frameworks (TMD, GPD)
6. Physics-facing derivations and examples

### 3.2 Assumption Management

Every major theorem should clearly separate:

- Structural assumptions (measurability, integrability, support, positivity)
- Physics assumptions (factorization validity, perturbative regime, truncation order)
- Derived identities

### 3.3 Parallelization by Contract

Parallel work is allowed when shared interfaces are stable. Each stage therefore defines:

- Interface freeze points
- Data-model contracts
- Exit criteria required to unblock dependent teams

## 4. Repository Placement and Module Strategy

Recommended structure (new modules shown conceptually):

- Physlib/Mathematics/Distribution/
  - Measurable kernels, convolution, moment transforms, support lemmas
- Physlib/QFT/Scattering/DIS/
  - Kinematics, tensors, structure functions
- Physlib/Particles/Parton/
  - PDF, TMD, GPD data models and core axioms
- Physlib/QFT/Factorization/
  - Hard kernels, convolution representation, matching logic
- docs/
  - Physics assumptions, theorem map, implementation status

Import policy:

- Keep Parton object definitions independent of heavy QFT imports where possible
- Keep analytic lemmas in Mathematics modules so they can be reused by non-DIS projects

## 5. Stage Plan

## Stage 0: Architecture and Convention Freeze

### Goals

- Define naming conventions and notation for variables and tensors
- Freeze module boundaries and interface contracts
- Select initial theorem scope (unpolarized inclusive DIS first)

### Detailed Tasks

- Define canonical variable symbols and names:
  - xBj, yInel, q, Q2, W2, nu, zHad, xiSkew, tMom, kT
- Define Lean naming conventions:
  - Lower-case defs for scalar invariants
  - Suffixes for assumptions and hypotheses
  - Prefixes for conversion and rewrite lemmas
- Write assumptions policy:
  - Which theorems are purely mathematical
  - Which theorems require physical regime assumptions
- Produce preliminary theorem inventory with identifiers and dependency notes

### Deliverables

- Design note in docs with agreed notation and scope
- Import graph proposal for new modules
- Initial theorem backlog tagged by stage

### Exit Criteria

- All leads agree on symbols, naming, and module boundaries
- No unresolved ambiguity in scope for Stage 1 and Stage 2
- The theorem backlog has owners and stage tags

### Dependencies

- None (root stage)

### Parallelization

- Fully parallelizable internal drafting tasks
- Must converge into one approved architecture document before Stage 1/3 coding begins

### Stage 0 Implementation Artifacts

- Architecture and conventions: [docs/DIS_Stage0_Architecture.md](docs/DIS_Stage0_Architecture.md)
- Import graph proposal: [docs/DIS_Import_Graph_Stage0.md](docs/DIS_Import_Graph_Stage0.md)
- Stage-tagged theorem inventory: [docs/DIS_Theorem_Backlog.md](docs/DIS_Theorem_Backlog.md)

### Stage 0 Implementation Status

- Implemented in documentation and planning artifacts
- Pending explicit team sign-off and named-owner assignment

## Stage 1: DIS Kinematics Foundation

### Goals

- Formalize basic lepton-hadron scattering kinematics
- Provide robust rewrite lemmas between common equivalent formulas
- Encode physically meaningful domain constraints

### Detailed Tasks

- Define process-level kinematic record:
  - Incoming and outgoing lepton momentum
  - Target hadron momentum
  - Momentum transfer q
- Define invariants and relations:
  - Q2 = -q^2, xBj, yInel, W2
  - Relations among q dot P, xBj, Q2
- Add positivity and bounds lemmas under assumptions:
  - Q2 > 0 in DIS regime
  - 0 < xBj <= 1 under standard hypotheses
- Build simplification toolkit:
  - Ring-normalization lemmas for scalar-product expressions
  - Canonical rewrite set for later tensor proofs

### Deliverables

- Kinematics module with definitions and theorem set
- Regression examples proving standard textbook identities

### Exit Criteria

- All Stage 2 tensor statements compile using Stage 1 symbols only
- At least one canonical formula can be proven in two equivalent forms using rewrite lemmas
- No unresolved notation conflicts from Stage 0

### Dependencies

- Requires Stage 0 completion

### Parallelization

- Parallel task A: invariant definitions and type-level structure
- Parallel task B: inequality and positivity lemmas
- Parallel task C: simplification/rewrite lemma library
- Merge gate: canonical naming and statement forms

### Stage 1 Implementation Artifacts

- Export module: [Physlib/QFT/Scattering/DIS/Basic.lean](Physlib/QFT/Scattering/DIS/Basic.lean)
- Kinematics definitions and rewrite lemmas:
  [Physlib/QFT/Scattering/DIS/Kinematics/Basic.lean](Physlib/QFT/Scattering/DIS/Kinematics/Basic.lean)
- Positivity and unit-interval bounds under explicit assumptions:
  [Physlib/QFT/Scattering/DIS/Kinematics/Bounds.lean](Physlib/QFT/Scattering/DIS/Kinematics/Bounds.lean)
- Top-level library wiring:
  [Physlib.lean](Physlib.lean)

### Stage 1 Implementation Status

- Implemented: process-level kinematic record, canonical invariants (`Q2`, `xBj`, `yInel`, `W2`),
  rewrite lemmas for `W2`, and baseline bounds under assumption bundles.
- Pending full Stage 1 exit validation: Stage 2 tensor statements are not yet present to run
  compatibility checks against Stage 1 APIs.

## Stage 2: Leptonic/Hadronic Tensor Framework

### Goals

- Define leptonic and hadronic tensors for inclusive DIS
- Formalize decomposition of hadronic tensor into structure functions
- Prove symmetry and gauge constraints for decomposition basis

### Detailed Tasks

- Define L_mu_nu object for lepton current contraction
- Define abstract W_mu_nu with assumptions:
  - Lorentz covariance
  - Current conservation
  - Symmetry properties
- Build tensor basis decomposition theorem:
  - F1 and F2 decomposition
  - Optional extension to FL from F1 and F2 relation
- Prove basis uniqueness under assumptions
- Provide contraction lemmas for cross-section expressions

### Deliverables

- Tensor decomposition module
- Proof scripts for basis constraints and contraction identities

### Exit Criteria

- F1/F2 decomposition theorem is complete and reusable
- Contraction pipeline from L_mu_nu and W_mu_nu to scalar observables compiles
- Assumptions appear explicitly in theorem signatures

### Dependencies

- Requires Stage 1

### Parallelization

- Parallel task A: leptonic tensor and algebraic contraction lemmas
- Parallel task B: hadronic tensor assumptions and decomposition basis
- Parallel task C: uniqueness and gauge-invariance proof path
- Integration point: shared tensor index conventions from Stage 0/1

### Stage 2 Implementation Artifacts

- Tensor framework and decomposition lemmas:
  [Physlib/QFT/Scattering/DIS/Tensors/Basic.lean](Physlib/QFT/Scattering/DIS/Tensors/Basic.lean)
- DIS export module updated to include tensors:
  [Physlib/QFT/Scattering/DIS/Basic.lean](Physlib/QFT/Scattering/DIS/Basic.lean)
- Top-level import ordering updated:
  [Physlib.lean](Physlib.lean)

### Stage 2 Implementation Status

- Implemented: leptonic tensor model, abstract hadronic assumptions, `F1`/`F2`
  decomposition interface, uniqueness theorem under probe-vector assumptions,
  and pointwise contraction lemma scaffolding.
- Pending full Stage 2 exit validation: Stage 2 to Stage 3/4 integration checks
  are pending because those modules are not yet implemented.

## Stage 3: Collinear PDF Object Model

### Goals

- Introduce first-class formal objects for collinear PDFs
- Encode support, positivity, and normalization assumptions cleanly
- Provide sum-rule and moment interfaces

### Detailed Tasks

- Define flavor index and scale index conventions
- Define PDF object type:
  - Function signature f_i(x, Q2)
  - Measurability and integrability constraints
  - Support in x interval
- Add theorem families:
  - Positivity and support consequences
  - Momentum sum-rule interface
  - Valence sum-rule interface
- Define moments and Mellin transform hooks for evolution work

### Deliverables

- PDF core module with assumptions and basic lemmas
- Sum-rule and moment theorem skeletons with reusable hypotheses bundles

### Exit Criteria

- PDF object can be used directly in Stage 4 convolution statements
- At least two independent sum-rule statements proven from assumptions
- Moment interface compiles and supports Stage 5 prototypes

### Dependencies

- Requires Stage 0
- Can start in parallel with Stage 2 once Stage 1 variable conventions are fixed

### Parallelization

- Parallel task A: data model and support/positivity framework
- Parallel task B: sum-rule theorem development
- Parallel task C: moments and transform interface
- Integration point: shared variable naming and measure conventions

### Stage 3 Implementation Artifacts

- Collinear PDF object model and assumptions:
  [Physlib/Particles/Parton/PDF/Basic.lean](Physlib/Particles/Parton/PDF/Basic.lean)
- DIS export module updated to include Stage 3 PDF interfaces:
  [Physlib/QFT/Scattering/DIS/Basic.lean](Physlib/QFT/Scattering/DIS/Basic.lean)

### Stage 3 Implementation Status

- Implemented: PDF object type `f_i(x,Q2)`, structural assumptions
  (support/positivity/measurability/integrability), Mellin-moment definition,
  and sum-rule interface theorems for momentum and valence constraints.
- Stage 3 interfaces are now consumed directly by Stage 4 factorization modules.

## Stage 4: Factorization and Convolution Layer

### Goals

- Create reusable convolution machinery and hard-kernel interfaces
- Formalize leading-order factorized expressions for structure functions
- Separate mathematical proofs from physics assumptions

### Detailed Tasks

- Define convolution operators and prove algebraic properties:
  - Linearity
  - Support propagation
  - Integrability transfer conditions
- Define hard coefficient function interface for perturbative kernels
- Prove LO factorization representation for selected structure functions
- Add modular theorem form:
  - Generic theorem parameterized by kernel assumptions
  - Concrete corollaries for specific LO kernels

### Deliverables

- Convolution math module and factorization module
- End-to-end LO representation theorem from assumptions to observable

### Exit Criteria

- At least one structure function identity proven in factorized form
- Convolution API is reused by at least two independent theorem files
- Physics assumptions and analytic assumptions are separated in signatures

### Dependencies

- Requires Stage 2 and Stage 3
- Requires relevant Mathematics support lemmas

### Parallelization

- Parallel task A: pure convolution library
- Parallel task B: coefficient-kernel interfaces and assumptions
- Parallel task C: physics-facing factorization theorem assembly
- Critical sync: shared integrability/support theorem contracts

### Stage 4 Implementation Artifacts

- Convolution API and linearity/support/integrability interfaces:
  [Physlib/QFT/Factorization/Convolution/Basic.lean](Physlib/QFT/Factorization/Convolution/Basic.lean)
- Additional reusable convolution theorem file:
  [Physlib/QFT/Factorization/Convolution/Properties.lean](Physlib/QFT/Factorization/Convolution/Properties.lean)
- LO hard-kernel assumptions interface:
  [Physlib/QFT/Factorization/DIS/HardKernel.lean](Physlib/QFT/Factorization/DIS/HardKernel.lean)
- LO factorized DIS representation theorems:
  [Physlib/QFT/Factorization/DIS/LO.lean](Physlib/QFT/Factorization/DIS/LO.lean)
- Stage export wiring:
  [Physlib/QFT/Scattering/DIS/Basic.lean](Physlib/QFT/Scattering/DIS/Basic.lean)

### Stage 4 Implementation Status

- Implemented: convolution operators, linearity/properties lemmas, hard-kernel
  assumptions, and LO factorization representation theorem schemas with explicit
  analytic-vs-physics assumption separation in signatures.
- Pending full Stage 4 exit validation: concrete process-specific kernels and
  phenomenological corollaries are deferred to later stages.

## Stage 5: Evolution Equations (DGLAP First)

### Goals

- Introduce scale-evolution formalism for collinear PDFs
- Support theorem-level statements for DGLAP dynamics
- Provide usable solved prototypes in restricted settings

### Detailed Tasks

- Define splitting-kernel operators and action on PDFs
- State DGLAP equation in scale-log variable
- Prove operator properties required for well-posedness in chosen function classes
- Implement restricted solved examples:
  - Toy kernels
  - Moment-space simplifications
  - Fixed-coupling simplification
- Add consistency checks against Stage 4 formulas across scales

### Deliverables

- Evolution module with DGLAP statement and support lemmas
- Example solved evolution cases

### Exit Criteria

- DGLAP equation expressed over Stage 3 PDF objects without adapter hacks
- At least one nontrivial solved case theorem is complete
- Scale-consistency theorem connects Stage 4 observable representation across Q2 values

### Dependencies

- Requires Stage 3 and Stage 4

### Parallelization

- Parallel task A: operator and kernel infrastructure
- Parallel task B: existence and boundedness lemmas in restricted spaces
- Parallel task C: solved model examples and validation theorems
- Merge point: unified evolution operator typeclass/record

### Stage 5 Implementation Artifacts

- DGLAP operator and log-scale equation schema:
  [Physlib/QFT/Factorization/Evolution/Basic.lean](Physlib/QFT/Factorization/Evolution/Basic.lean)
- Toy solved evolution examples:
  [Physlib/QFT/Factorization/Evolution/Solutions.lean](Physlib/QFT/Factorization/Evolution/Solutions.lean)
- Stage 4/5 consistency theorem layer:
  [Physlib/QFT/Factorization/Evolution/Consistency.lean](Physlib/QFT/Factorization/Evolution/Consistency.lean)
- Stage export wiring:
  [Physlib/QFT/Factorization/Basic.lean](Physlib/QFT/Factorization/Basic.lean)
  and [Physlib/QFT/Scattering/DIS/Basic.lean](Physlib/QFT/Scattering/DIS/Basic.lean)

### Stage 5 Implementation Status

- Implemented: splitting-kernel operator, DGLAP equation schema in logarithmic
  scale variable, a solved toy kernel/coupling example, and a scale-consistency
  theorem connecting Stage 4 LO observables under explicit cross-scale hypotheses.
- Pending full Stage 5 exit validation: analytic well-posedness and nontrivial
  physical kernels remain deferred to future refinement stages.

## Stage 6: TMD Formalization

### Goals

- Extend from collinear distributions to transverse-momentum-dependent distributions
- Add rapidity-scale structure and reduction to collinear limit
- Prepare for future SIDIS and related observables

### Detailed Tasks

- Define TMD object signature:
  - f_i(x, kT, Q2, zeta)
  - Support and regularity assumptions
- Add soft-factor and rapidity parameter interfaces (abstract first)
- Define transverse-momentum integration operation and prove bridge theorem:
  - Integral over kT recovers collinear PDF under assumptions
- Add minimal theorem set for positivity/support in kT domain

### Deliverables

- TMD core module
- TMD to PDF reduction theorem suite

### Exit Criteria

- Reduction theorem to Stage 3 PDFs is complete and reusable
- TMD assumptions are explicit and composable with Stage 4 style theorems
- At least one cross-check theorem compares TMD-integrated observable with collinear form

### Dependencies

- Requires Stage 3 and Stage 4
- Benefits from Stage 5 but does not strictly require full DGLAP completion

### Parallelization

- Parallel task A: TMD object model and domain structure
- Parallel task B: rapidity/soft-factor abstraction interfaces
- Parallel task C: reduction-to-collinear proof chain
- Integration gate: common measure conventions for kT integration

### Stage 6 Implementation Artifacts

- TMD object model and structural assumptions:
  [Physlib/Particles/Parton/TMD/Basic.lean](Physlib/Particles/Parton/TMD/Basic.lean)
- TMD-to-PDF reduction and Stage 4 cross-check theorem:
  [Physlib/Particles/Parton/TMD/Reduction.lean](Physlib/Particles/Parton/TMD/Reduction.lean)
- Stage export wiring:
  [Physlib/QFT/Factorization/Basic.lean](Physlib/QFT/Factorization/Basic.lean)
  and [Physlib/QFT/Scattering/DIS/Basic.lean](Physlib/QFT/Scattering/DIS/Basic.lean)

### Stage 6 Implementation Status

- Implemented: TMD object type `f_i(x,kT,Q2,ζ)`, support/positivity assumptions,
  truncated `kT` integration map, TMD-to-PDF reduction interface theorem, and a
  Stage 4 LO observable cross-check theorem under the reduction hypothesis.
- Pending full Stage 6 exit validation: nontrivial rapidity/soft-factor dynamics
  are deferred to later stages.

## Stage 7: GPD Formalization

### Goals

- Define generalized parton distributions with off-forward kinematics
- Establish core structural theorems and forward-limit relations
- Prepare exclusive-process formal reasoning

### Detailed Tasks

- Define GPD object signature:
  - H(x, xi, t), E(x, xi, t) and extension points for polarized analogs
- Encode support and symmetry assumptions in x and xi
- Add polynomiality statement framework for Mellin moments
- Prove forward-limit bridges to Stage 3 PDFs
- Add first-moment interfaces for form-factor relations

### Deliverables

- GPD core module
- Forward-limit theorem set
- Moment/polynomiality theorem skeletons

### Exit Criteria

- Forward-limit theorem to PDF is complete
- At least one polynomiality or moment relation theorem is proven in nontrivial form
- GPD definitions integrate with Stage 1 kinematics conventions for xi and t

### Dependencies

- Requires Stage 1 and Stage 3
- Benefits from Stage 4 moment/convolution infrastructure

### Parallelization

- Parallel task A: GPD data model and assumptions
- Parallel task B: forward-limit theorem work
- Parallel task C: moment and polynomiality framework
- Sync point: shared variable and moment conventions with Stage 3/4

### Stage 7 Implementation Artifacts

- GPD object model (`H`, `E`) and forward-limit bridge:
  [Physlib/Particles/Parton/GPD/Basic.lean](Physlib/Particles/Parton/GPD/Basic.lean)
- Mellin moments and polynomiality interfaces:
  [Physlib/Particles/Parton/GPD/Moments.lean](Physlib/Particles/Parton/GPD/Moments.lean)
- Stage export wiring:
  [Physlib/QFT/Factorization/Basic.lean](Physlib/QFT/Factorization/Basic.lean)
  and [Physlib/QFT/Scattering/DIS/Basic.lean](Physlib/QFT/Scattering/DIS/Basic.lean)

### Stage 7 Implementation Status

- Implemented: GPD objects `H(x,ξ,t)` and `E(x,ξ,t)` with assumptions,
  forward-limit bridge theorem to Stage 3 PDFs at fixed scale, polynomiality
  schema for Mellin moments, and a first nontrivial zeroth-moment consequence.
- Pending full Stage 7 exit validation: physics-rich polynomiality/form-factor
  corollaries are deferred to later refinement stages.

## Stage 8: Unified Interfaces and Cross-Framework Consistency

### Goals

- Harmonize PDF, TMD, and GPD APIs
- Prove consistency relations between frameworks
- Expose clean top-level entry points for downstream users

### Detailed Tasks

- Define common abstractions:
  - Shared distribution class/interface
  - Shared sum-rule and moment API shape
- Prove compatibility relations:
  - TMD to PDF reduction consistency
  - GPD forward-limit consistency
- Add top-level import module and user-facing theorem index
- Standardize notation wrappers and simplification hints

### Deliverables

- Unified API layer and bridge theorem collection
- Top-level theorem map documentation

### Exit Criteria

- Users can import one top-level module for core parton-formalism objects
- Bridge theorems compile without private helper dependencies
- No duplicated incompatible definitions of shared variables or moments

### Dependencies

- Requires Stage 6 and Stage 7
- Uses Stage 3/4 as shared foundations

### Parallelization

- Parallel task A: API harmonization and wrappers
- Parallel task B: cross-framework theorem proofs
- Parallel task C: documentation and theorem index generation
- Merge gate: naming and typeclass coherence checks

### Stage 8 Implementation Artifacts

- Unified interface model and API wrappers:
  [Physlib/Particles/Parton/Unified/Basic.lean](Physlib/Particles/Parton/Unified/Basic.lean)
- Cross-framework consistency theorem suite:
  [Physlib/Particles/Parton/Unified/Consistency.lean](Physlib/Particles/Parton/Unified/Consistency.lean)
- Single import entry point for core parton formalisms:
  [Physlib/Particles/Parton/Basic.lean](Physlib/Particles/Parton/Basic.lean)
- Stage export wiring updates:
  [Physlib/QFT/Factorization/Basic.lean](Physlib/QFT/Factorization/Basic.lean),
  [Physlib/QFT/Scattering/DIS/Basic.lean](Physlib/QFT/Scattering/DIS/Basic.lean),
  and [Physlib.lean](Physlib.lean)

### Stage 8 Implementation Status

- Implemented: a shared Stage 8 model combining PDF/TMD/GPD objects, unified
  accessor wrappers, a shared sum-rule interface shape, and bridge theorems for
  TMD-to-PDF, GPD-forward-to-PDF, and TMD-to-GPD-forward consistency.
- Exit-criteria coverage: one-module import path for core parton formalisms is
  provided and bridge theorems compile via public interfaces.

## Stage 9: Validation, Examples, and External Integration Hooks

### Goals

- Turn formalization into practical workflows
- Add example pipelines and test harnesses
- Prepare integration with numerical or Monte Carlo ecosystems

### Detailed Tasks

- Build curated examples:
  - Minimal PDF model to observable theorem chain
  - TMD integration consistency example
  - GPD forward-limit example
- Add property-test style theorem checks for assumptions violations
- Define export hooks for numerically evaluated kernels/tables
- Add guidance for external consumers (event generators, analysis pipelines)

### Deliverables

- Example modules and docs walkthrough
- Validation checklist and CI theorem targets
- Integration notes for external numerical code paths

### Exit Criteria

- At least three end-to-end worked examples compile in CI
- Validation checklist is complete and linked from docs
- External consumer guide exists and references stable interfaces only

### Dependencies

- Requires Stage 8
- Can begin partial example work after Stage 4

### Parallelization

- Parallel task A: examples and tutorials
- Parallel task B: validation theorem suite
- Parallel task C: external integration documentation and hooks
- Final synchronization: CI and top-level documentation consistency

### Stage 9 Implementation Artifacts

- Stage 9 worked examples and validation theorem pipelines:
  [Physlib/QFT/Scattering/DIS/Examples/Basic.lean](Physlib/QFT/Scattering/DIS/Examples/Basic.lean)
- Stage export wiring update for examples:
  [Physlib/QFT/Scattering/DIS/Basic.lean](Physlib/QFT/Scattering/DIS/Basic.lean)

### Stage 9 Implementation Status

- Implemented: three worked theorem examples for (1) kinematics-to-LO
  factorized observable representation, (2) TMD-integration consistency at LO,
  and (3) GPD forward-limit consistency to collinear PDFs.
- Exit-criteria coverage: at least three end-to-end worked examples now compile
  through the Stage 9 examples module and are available from the DIS top-level
  export module.

## 6. Dependency Graph and Critical Path

## 6.1 Stage Dependencies

- Stage 0 -> Stage 1, Stage 3
- Stage 1 -> Stage 2, Stage 7
- Stage 2 + Stage 3 -> Stage 4
- Stage 3 + Stage 4 -> Stage 5
- Stage 3 + Stage 4 -> Stage 6
- Stage 1 + Stage 3 (+ Stage 4 preferred) -> Stage 7
- Stage 6 + Stage 7 (+ Stage 3/4 foundations) -> Stage 8
- Stage 8 -> Stage 9

## 6.2 Practical Parallel Lanes

Potential implementation lanes after Stage 0:

- Lane A: Stage 1 -> Stage 2
- Lane B: Stage 3

Then after Stage 2 and Stage 3 converge:

- Lane C: Stage 4 -> Stage 5
- Lane D: Stage 6
- Lane E: Stage 7

Final convergence:

- Lane F: Stage 8 -> Stage 9

## 6.3 Critical Path

The likely critical path is:

Stage 0 -> Stage 1 -> Stage 2 -> Stage 4 -> Stage 6 -> Stage 8 -> Stage 9

The path can shift if Stage 7 (GPD) becomes the longest branch.

## 7. Risk Register and Mitigation

### Risk 1: Overly broad early scope

- Mitigation: unpolarized inclusive DIS first; defer polarized and higher-order complexity

### Risk 2: Interface churn across teams

- Mitigation: interface freeze at the end of Stage 0, Stage 3, and Stage 4

### Risk 3: Analytic prerequisites outgrowing physics work

- Mitigation: maintain a dedicated mathematics backlog and avoid embedding analytic lemmas in physics files

### Risk 4: Hidden assumptions in theorem statements

- Mitigation: enforce theorem template separating structural and physics assumptions

### Risk 5: Slow CI due to heavy theorem sets

- Mitigation: isolate expensive proofs, add smoke-theorem CI tier, and maintain staged proof targets

## 8. Suggested Milestone Cadence

- Milestone M1: Stage 0 + Stage 1 complete
- Milestone M2: Stage 2 + Stage 3 complete
- Milestone M3: Stage 4 complete with one end-to-end LO theorem
- Milestone M4: Stage 5 + Stage 6 + Stage 7 core bridges complete
- Milestone M5: Stage 8 + Stage 9 complete with examples and integration hooks

## 9. Definition of Done for the Program

The full program is complete when:
- PDF, TMD, and GPD are first-class formal objects with documented assumptions
- Core bridge theorems between frameworks are proven
- At least one complete DIS theorem pipeline is available from kinematics to factorized observable
- Example workflows and external integration notes are published in docs
- All designated stage exit criteria have been met and recorded

## 10. Additional Formalization Wave (Post-Stage 9)

This wave expands the baseline DIS framework into phenomenology-facing and
precision-ready capabilities while preserving the staged methodology used so far.

## Stage 10: Polarized DIS and Spin Structure

### Goals

- Extend DIS foundations to polarized observables
- Introduce spin-dependent structure functions in a modular way
- Preserve compatibility with existing unpolarized APIs

### Detailed Tasks

- Add polarized hadronic tensor interfaces with explicit symmetry assumptions
- Define polarized structure-function layer (`g1`, `g2`) at the API level
- Add sum-rule schema interfaces (Bjorken and Ellis-Jaffe style assumptions)
- Provide bridge lemmas between polarized/unpolarized kinematic conventions

### Deliverables

- Polarized tensor module set
- Polarized structure-function interface module
- Sum-rule theorem skeletons with assumption bundles

### Exit Criteria

- Polarized structure-function interfaces compile from Stage 1 kinematics
- At least one nontrivial polarized identity is proven under explicit assumptions
- No breaking change to Stage 1-9 unpolarized imports

### Dependencies

- Requires Stage 1 and Stage 2
- Reuses Stage 3 assumption design patterns

### Parallelization

- Parallel task A: polarized tensor assumptions and decomposition basis
- Parallel task B: polarized structure-function API and theorem statements
- Parallel task C: sum-rule abstraction and consistency checks

## Stage 11: Higher-Order Factorization and Scheme Dependence

### Goals

- Introduce NLO/NNLO-ready coefficient-function interfaces
- Track renormalization/factorization scheme choices explicitly
- Formalize matching and perturbative truncation contracts

### Detailed Tasks

- Extend hard-kernel interfaces to perturbative-order-indexed families
- Define scheme record (`MSbar`, DIS-scheme placeholders) and conversion maps
- Add theorem schemas for truncation consistency and residual-order bookkeeping
- Add matching theorem interfaces for finite renormalization transformations

### Deliverables

- Order-indexed hard-kernel module
- Scheme/matching abstractions
- Truncation and consistency theorem layer

### Exit Criteria

- Stage 4 LO theorems specialize as a strict subcase of the higher-order API
- Scheme-conversion interface compiles with explicit assumptions
- At least one order-by-order consistency theorem is proven

### Dependencies

- Requires Stage 4 and Stage 5
- Benefits from Stage 8 unified interface for downstream use

### Parallelization

- Parallel task A: perturbative-order kernel formalism
- Parallel task B: scheme definitions and conversion operators
- Parallel task C: matching/truncation theorem proofs

## Stage 12: Target-Mass, Higher-Twist, and Power Corrections

### Goals

- Add controlled power-suppressed corrections to baseline DIS formulas
- Separate leading-twist and subleading-twist contributions in theorem signatures
- Prepare precision-analysis workflows with explicit approximation error channels

### Detailed Tasks

- Define target-mass correction interfaces as additive/deformative operators
- Introduce higher-twist placeholder objects with support/integrability assumptions
- Add theorem templates for observable decomposition into twist sectors
- Add bounds/monotonicity interfaces for correction-size control assumptions

### Deliverables

- Power-correction interface module
- Twist-decomposition theorem schema layer
- Precision-assumption bundle templates

### Exit Criteria

- Observable decomposition theorem compiles with explicit twist assumptions
- At least one correction-recovery theorem reduces to Stage 4 LO in the zero-limit
- Correction assumptions are isolated from structural assumptions

### Dependencies

- Requires Stage 4 and Stage 5
- Reuses Stage 1 kinematics and Stage 3 PDF moments

### Parallelization

- Parallel task A: target-mass correction operators
- Parallel task B: higher-twist object model and assumptions
- Parallel task C: reduction-to-baseline and stability lemmas

## Stage 13: Semi-Inclusive and Fragmentation Extensions

### Goals

- Extend DIS framework toward SIDIS-style observables
- Introduce fragmentation-function interfaces compatible with current parton APIs
- Add cross-check theorems between inclusive and semi-inclusive limits

### Detailed Tasks

- Define fragmentation-function object model `D_h^i(z,Q2)` with assumptions
- Introduce SIDIS kinematics placeholders (`zHad`, transverse observables)
- Define mixed convolution interfaces (PDF x hard kernel x FF)
- Prove limit theorem reducing SIDIS observable family to inclusive forms

### Deliverables

- Fragmentation-function module
- SIDIS kinematics extension module
- Mixed-factorization theorem interfaces

### Exit Criteria

- Fragmentation and SIDIS APIs compile without cyclic imports
- At least one inclusive-limit theorem is proven
- Stage 8 unified parton API is reused without duplication

### Dependencies

- Requires Stage 8 and Stage 9
- Benefits from Stage 6 TMD abstractions

### Parallelization

- Parallel task A: FF object model and assumptions
- Parallel task B: SIDIS kinematics and variable conventions
- Parallel task C: mixed-factorization and inclusive-limit proofs

## Stage 14: Statistical Inference and Data-Constraint Layer

### Goals

- Connect formal theorem outputs to fit/inference-style workflows
- Add interfaces for likelihoods, nuisance parameters, and systematic envelopes
- Keep numerical fitting external while formalizing consistency contracts

### Detailed Tasks

- Define abstract data-point and covariance interfaces
- Add likelihood/chi-square contract layer for observable predictions
- Formalize nuisance-parameter propagation assumptions and monotonicity lemmas
- Add theorem schemas for consistency of fitted parameters under model updates

### Deliverables

- Inference contract module
- Systematics/nuisance assumption bundle templates
- Validation theorem suite for prediction-vs-data interfaces

### Exit Criteria

- End-to-end theorem chain from formal observable to inference contract compiles
- At least one stability theorem under bounded nuisance shifts is proven
- External-integration interfaces remain assumption-explicit and implementation-agnostic

### Dependencies

- Requires Stage 9
- Benefits from Stages 11-13 for precision and extended observables

### Parallelization

- Parallel task A: statistical data and covariance abstractions
- Parallel task B: likelihood and nuisance-propagation interfaces
- Parallel task C: stability/consistency theorem proofs

## 11. Additional-Wave Dependency View

Suggested flow for this wave:

- Stage 10 in parallel with early Stage 11 scaffolding
- Stage 11 and Stage 12 as precision-factorization lane
- Stage 13 after Stage 8/9 stabilization, optionally overlapping late Stage 12
- Stage 14 after Stage 9, with stronger coverage once Stage 11-13 mature

Practical critical path candidate:

Stage 10 -> Stage 11 -> Stage 12 -> Stage 13 -> Stage 14

## 12. Immediate Implementation Backlog Seed

Recommended first tickets for this wave:

- DIS-POL-001: polarized tensor assumption record and decomposition interface
- DIS-HO-001: order-indexed hard-kernel record and LO embedding theorem
- DIS-POW-001: power-correction decomposition theorem schema
- DIS-SIDIS-001: fragmentation-function object model and assumptions
- DIS-INF-001: data/likelihood contract interface with explicit covariance assumptions

## 13. Additional-Wave Implementation Artifacts

- Stage 10 polarized interfaces:
  [Physlib/QFT/Scattering/DIS/Polarized/Basic.lean](Physlib/QFT/Scattering/DIS/Polarized/Basic.lean)
- Stage 11 higher-order factorization interfaces:
  [Physlib/QFT/Factorization/HigherOrder/Basic.lean](Physlib/QFT/Factorization/HigherOrder/Basic.lean)
- Stage 12 power-corrections interfaces:
  [Physlib/QFT/Scattering/DIS/Corrections/Basic.lean](Physlib/QFT/Scattering/DIS/Corrections/Basic.lean)
- Stage 13 fragmentation and SIDIS interfaces:
  [Physlib/Particles/Fragmentation/Basic.lean](Physlib/Particles/Fragmentation/Basic.lean)
  and [Physlib/QFT/Scattering/DIS/SIDIS/Basic.lean](Physlib/QFT/Scattering/DIS/SIDIS/Basic.lean)
- Stage 14 inference interfaces:
  [Physlib/QFT/Scattering/DIS/Inference/Basic.lean](Physlib/QFT/Scattering/DIS/Inference/Basic.lean)
- Export wiring updates:
  [Physlib/QFT/Factorization/Basic.lean](Physlib/QFT/Factorization/Basic.lean)
  and [Physlib/QFT/Scattering/DIS/Basic.lean](Physlib/QFT/Scattering/DIS/Basic.lean)

## 14. Additional-Wave Implementation Status

- Implemented Stage 10: polarized tensor/function interfaces and sum-rule schemas.
- Implemented Stage 11: order-indexed hard-kernel families, scheme conversion,
  and LO truncation embedding interfaces.
- Implemented Stage 12: target-mass/higher-twist correction interfaces with
  decomposition and zero-correction recovery theorem.
- Implemented Stage 13: fragmentation-function model plus SIDIS observable and
  inclusive-limit theorem interface.
- Implemented Stage 14: data/covariance/chi-square inference contracts and
  nuisance-shift stability theorem.
