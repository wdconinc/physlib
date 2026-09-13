# DIS Stage 0 Architecture and Conventions

## Status

- Stage 0 artifact status: implemented
- Program status: pending team sign-off and owner assignment finalization

## 1. Scope Freeze (Stage 0 Decision)

The initial formalization scope is:

- Unpolarized inclusive DIS only
- Leading-order structure-function decomposition and factorization interfaces
- Foundational objects that later extend to TMD and GPD

Out of Stage 0 scope:

- Polarized observables
- Higher-order perturbative matching details
- Full nonperturbative operator constructions

## 2. Canonical Variable and Symbol Conventions

## 2.1 Scalars and Invariants

- `Q2`: spacelike virtuality, defined as `Q2 = - q^2`
- `xBj`: Bjorken x
- `yInel`: inelasticity variable
- `W2`: hadronic final-state invariant mass squared
- `nu`: energy transfer proxy in selected frames
- `zHad`: hadron momentum fraction for future semi-inclusive extensions
- `xiSkew`: skewness for GPD formalization
- `tMom`: momentum-transfer invariant for exclusive channels
- `kT`: transverse momentum variable for TMDs

Naming rules:

- Scalar invariants use camel-case short physics names (`Q2`, `xBj`, `W2`)
- Avoid overloaded single-letter globals except local binders in proofs
- Use consistent suffixes for domain-restricted variants, such as `xBjInUnitInterval`

## 2.2 Four-Vectors and Tensors

- Four-momenta use lower-case Latin names: `p`, `k`, `q`, `pPrime`, `kPrime`
- Tensor symbols map to Lean identifiers as:
  - Leptonic tensor: `lMuNu`
  - Hadronic tensor: `wMuNu`
- Index-heavy helper lemmas should use long descriptive names rather than compact symbolic names

## 2.3 Scale Variables

- `Q2` denotes hard scale in collinear DIS context
- Future rapidity-scale variables for TMD use `zeta` and optional Collins-Soper kernel symbols

## 3. Lean Naming Conventions

## 3.1 Definitions

- Scalar definitions: lower-case initial, concise physics mnemonic (`xBj`, `w2` only if style harmonization is required)
- Structures/records: UpperCamelCase (`DisKinematics`, `PdfAssumptions`)
- Namespaces follow file hierarchy and one physics domain per namespace

## 3.2 Theorem and Lemma Names

- Rewrite lemmas end with `_eq_...` or `_rewrite`
- Inequality lemmas end with `_nonneg`, `_pos`, `_le`, `_lt`
- Existence/interface lemmas end with `_exists` or `_wellDefined`

## 3.3 Hypothesis Prefixing

Use grouped assumptions records when possible. If explicit hypotheses are needed, use:

- `hPhys...` for physics-regime assumptions
- `hStruct...` for structural assumptions (measure-theoretic, support, positivity)
- `hAnalytic...` for analytic assumptions (integrability, boundedness)

## 4. Assumption Policy

Every major theorem must present assumptions in three blocks:

1. Structural assumptions:
   - Measurability
  - Integrability
   - Support and positivity
2. Physics assumptions:
   - Regime validity (DIS kinematics, factorization regime)
   - Perturbative truncation context
3. Optional approximation assumptions:
   - Error-model assumptions
   - Model closure assumptions

No theorem should mix these assumption classes without explicit sectioning in the statement or local documentation block.

## 5. Interface Contracts Frozen at Stage 0

Frozen contracts intended to minimize cross-team churn:

- Kinematics contract:
  - A single kinematics record for inclusive DIS variables
  - Canonical definitions for `Q2`, `xBj`, `yInel`, `W2`
- Tensor contract:
  - Abstract `wMuNu` with explicit symmetry and conservation assumptions
  - Explicit contraction entry points for scalar observables
- Distribution contract:
  - PDF object shape `f_i(x, Q2)` and support assumptions in x domain

Any breaking change to these contracts requires an architecture review issue.

## 6. Documentation and Review Requirements

Before merging Stage 1+ implementation work:

- New modules must reference this file in top-level comments
- New theorem files must include assumptions classification section in module docstring
- API additions must update the theorem backlog in docs

## 7. Stage 0 Exit Checklist

- [x] Canonical symbols and variable names defined
- [x] Naming conventions for definitions and theorems defined
- [x] Assumption policy defined
- [x] Interface contracts frozen
- [x] Initial theorem backlog created and stage-tagged
- [ ] Team owner names confirmed
- [ ] Team sign-off meeting completed

## 8. Immediate Next Actions

- Assign concrete owners to backlog items by stage
- Create Stage 1 skeleton modules using frozen names
- Open tracking issues for any requested contract changes
