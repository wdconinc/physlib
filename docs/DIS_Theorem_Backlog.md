# DIS Theorem Backlog (Initial Stage-Tagged Inventory)

## 1. Usage

This backlog defines initial theorem targets, dependencies, and provisional owners by role.

Owner roles (to be mapped to names):

- `KIN`: kinematics lead
- `TEN`: tensor lead
- `PDF`: parton distributions lead
- `ANA`: analysis/math lead
- `FAC`: factorization lead
- `EVO`: evolution lead
- `TMD`: TMD lead
- `GPD`: GPD lead
- `INT`: integration/docs lead

Status values:

- `todo`
- `in-progress`
- `blocked`
- `done`

## 2. Stage 1 Backlog (Kinematics)

| ID | Statement Target | Stage | Depends On | Owner | Status |
| --- | --- | --- | --- | --- | --- |
| DIS-KIN-001 | Define `DisKinematics` record with `p`, `k`, `pPrime`, `kPrime`, `q` | 1 | Stage 0 freeze | KIN | done |
| DIS-KIN-002 | Define `Q2 = - q^2` and prove positivity under DIS assumptions | 1 | DIS-KIN-001 | KIN | done |
| DIS-KIN-003 | Define `xBj`, `yInel`, `W2` from kinematic record | 1 | DIS-KIN-001 | KIN | done |
| DIS-KIN-004 | Prove equivalent forms of `W2` using scalar-product rewrites | 1 | DIS-KIN-002,003 | KIN | done |
| DIS-KIN-005 | Prove `0 < xBj <= 1` under standard DIS domain assumptions | 1 | DIS-KIN-003 | KIN | done |

## 3. Stage 2 Backlog (Tensors)

| ID | Statement Target | Stage | Depends On | Owner | Status |
| --- | --- | --- | --- | --- | --- |
| DIS-TEN-001 | Define leptonic tensor `lMuNu` interface | 2 | DIS-KIN-001 | TEN | done |
| DIS-TEN-002 | Define abstract hadronic tensor `wMuNu` with symmetry/conservation assumptions | 2 | DIS-KIN-001 | TEN | done |
| DIS-TEN-003 | Prove basis decomposition into `F1`, `F2` under assumptions | 2 | DIS-TEN-002 | TEN | done |
| DIS-TEN-004 | Prove decomposition uniqueness in chosen basis | 2 | DIS-TEN-003 | TEN | done |
| DIS-TEN-005 | Provide contraction theorem from `lMuNu` and `wMuNu` to scalar observable form | 2 | DIS-TEN-001,002,003 | TEN | done |

## 4. Stage 3 Backlog (Collinear PDF)

| ID | Statement Target | Stage | Depends On | Owner | Status |
| --- | --- | --- | --- | --- | --- |
| DIS-PDF-001 | Define PDF object type `f_i(x,Q2)` with structured assumptions record | 3 | Stage 0 freeze | PDF | done |
| DIS-PDF-002 | Support theorem: `f_i = 0` outside x support assumptions | 3 | DIS-PDF-001 | PDF | done |
| DIS-PDF-003 | Positivity theorem under positivity assumptions | 3 | DIS-PDF-001 | PDF | done |
| DIS-PDF-004 | Momentum sum-rule interface theorem schema | 3 | DIS-PDF-001, ANA support lemmas | PDF | done |
| DIS-PDF-005 | Mellin moment definition and well-definedness theorem | 3 | DIS-PDF-001, ANA support lemmas | PDF | done |

## 5. Stage 4 Backlog (Factorization and Convolution)

| ID | Statement Target | Stage | Depends On | Owner | Status |
| --- | --- | --- | --- | --- | --- |
| DIS-FAC-001 | Define convolution operator and prove linearity | 4 | ANA core lemmas | FAC | done |
| DIS-FAC-002 | Prove support propagation through convolution | 4 | DIS-FAC-001 | FAC | done |
| DIS-FAC-003 | Define hard-kernel interface at LO | 4 | DIS-TEN-003, DIS-PDF-001 | FAC | done |
| DIS-FAC-004 | Prove LO factorized expression for one structure function | 4 | DIS-FAC-001,003 and DIS-TEN-005 | FAC | done |

## 6. Stage 5 Backlog (Evolution)

| ID | Statement Target | Stage | Depends On | Owner | Status |
| --- | --- | --- | --- | --- | --- |
| DIS-EVO-001 | Define splitting-kernel operator on PDF space | 5 | DIS-PDF-001 | EVO | done |
| DIS-EVO-002 | Formal DGLAP equation statement in log-scale variable | 5 | DIS-EVO-001 | EVO | done |
| DIS-EVO-003 | Prove one solved toy-evolution case | 5 | DIS-EVO-002 | EVO | done |

## 7. Stage 6 Backlog (TMD)

| ID | Statement Target | Stage | Depends On | Owner | Status |
| --- | --- | --- | --- | --- | --- |
| DIS-TMD-001 | Define TMD object `f_i(x,kT,Q2,zeta)` assumptions record | 6 | DIS-PDF-001 | TMD | done |
| DIS-TMD-002 | Define `kT` integration map to collinear object | 6 | DIS-TMD-001 | TMD | done |
| DIS-TMD-003 | Prove TMD-to-PDF reduction theorem under assumptions | 6 | DIS-TMD-002 and DIS-PDF-001 | TMD | done |

## 8. Stage 7 Backlog (GPD)

| ID | Statement Target | Stage | Depends On | Owner | Status |
| --- | --- | --- | --- | --- | --- |
| DIS-GPD-001 | Define GPD objects `H(x,xi,t)` and `E(x,xi,t)` assumptions record | 7 | DIS-KIN-003, DIS-PDF-001 | GPD | done |
| DIS-GPD-002 | Prove forward-limit bridge to collinear PDF | 7 | DIS-GPD-001 and DIS-PDF-001 | GPD | done |
| DIS-GPD-003 | Add polynomiality/moment theorem skeleton and first nontrivial lemma | 7 | DIS-GPD-001 and DIS-PDF-005 | GPD | done |

## 9. Stage 8/9 Backlog (Unification and Validation)

| ID | Statement Target | Stage | Depends On | Owner | Status |
| --- | --- | --- | --- | --- | --- |
| DIS-UNI-001 | Define unified parton-distribution interface | 8 | DIS-TMD-003, DIS-GPD-002 | INT | done |
| DIS-UNI-002 | Prove consistency theorem suite across PDF/TMD/GPD bridges | 8 | DIS-UNI-001 | INT | done |
| DIS-VAL-001 | End-to-end worked example: kinematics to LO factorized observable | 9 | DIS-FAC-004 | INT | done |
| DIS-VAL-002 | End-to-end worked example: TMD integration consistency | 9 | DIS-TMD-003 | INT | done |
| DIS-VAL-003 | End-to-end worked example: GPD forward-limit consistency | 9 | DIS-GPD-002 | INT | done |

## 10. Stage 10-14 Backlog (Additional Wave)

| ID | Statement Target | Stage | Depends On | Owner | Status |
| --- | --- | --- | --- | --- | --- |
| DIS-POL-001 | Define polarized tensor assumption record and decomposition interface | 10 | DIS-TEN-005 | TEN | done |
| DIS-POL-002 | Define polarized structure functions and sum-rule schemas | 10 | DIS-POL-001 | TEN | done |
| DIS-HO-001 | Define perturbative-order-indexed hard-kernel family | 11 | DIS-FAC-004 | FAC | done |
| DIS-HO-002 | Define scheme-conversion interface and identity theorem | 11 | DIS-HO-001 | FAC | done |
| DIS-POW-001 | Define target-mass and higher-twist correction interfaces | 12 | DIS-FAC-004 | ANA | done |
| DIS-POW-002 | Prove zero-correction recovery to baseline observable | 12 | DIS-POW-001 | ANA | done |
| DIS-SIDIS-001 | Define fragmentation-function object model and assumptions | 13 | DIS-PDF-001 | TMD | done |
| DIS-SIDIS-002 | Define SIDIS structure-function interface and inclusive limit theorem | 13 | DIS-SIDIS-001, DIS-FAC-004 | TMD | done |
| DIS-INF-001 | Define data/covariance/chi-square inference contracts | 14 | DIS-VAL-001 | INT | done |
| DIS-INF-002 | Prove nuisance-shift stability theorem schema | 14 | DIS-INF-001 | INT | done |

## 11. Blocking Dependencies Summary

Major blockers for parallel work planning:

- Stage 2 is blocked by Stage 1 kinematics API
- Stage 4 is blocked by Stage 2 and Stage 3
- Stage 6 is blocked by Stage 3 (and partially by Stage 4 for observable checks)
- Stage 7 is blocked by Stage 1 variable conventions and Stage 3 PDF interfaces
- Stage 11 is blocked by Stage 4 factorization interfaces
- Stage 13 is blocked by Stage 8/9 API stabilization

## 12. Stage 0 Completion Marker

Stage 0 deliverable requirements addressed by this file:

- [x] Initial theorem inventory
- [x] Stage tags
- [x] Explicit dependencies
- [x] Provisional owners by role
- [ ] Named owner assignment completed
