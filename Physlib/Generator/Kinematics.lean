/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Numerics.FourMom

/-!
# The DIS kinematic map, in `Float`

`s`, `Q²`, `x`, `y` and `W²` computed from four-momenta, for the generator.

## Correspondence with the `ℝ` definitions

Each definition here is a transcription of one in
`Physlib.QFT.Scattering.DIS.Kinematics.Basic`, which works over an abstract bilinear form
`g : Bilin V`.  Taking `g` to be the Minkowski product, the correspondence is:

| here | there | definition |
|---|---|---|
| `q2 k k'` | `DisKinematics.Q2` | `-(q·q)` with `q = k - k'` |
| `xBj p k k'` | `DisKinematics.xBj` | `Q² / (2 p·q)` |
| `yInel p k k'` | `DisKinematics.yInel` | `(p·q)/(p·k)` |
| `w2 p k k'` | `DisKinematics.W2` | `(p+q)·(p+q)` |

**These are transcriptions, not theorems.** Nothing here is proved equal to anything there,
and §6 of the generator plan explicitly rules out attempting it: a proof would need a
`Float`↔`ℝ` bridge. The table is a claim about intent that a reader must check by eye, and
it is recorded here rather than left implicit precisely because it cannot be machine-checked.

`sTotal` has no counterpart there — `DisKinematics` carries no beam-pair invariant — so it is
defined directly as `(k+p)·(k+p)`.
-/

@[expose] public section

namespace Physlib
namespace Generator

open Numerics

/-- Momentum transfer `q = k - k'`, from incoming and outgoing lepton momenta. -/
def qTransfer (k kPrime : FourMom) : FourMom := FourMom.sub k kPrime

/-- The hard scale `Q² = -q·q`.  Positive for spacelike `q`, which is the physical region. -/
def q2 (k kPrime : FourMom) : Float :=
  let q := qTransfer k kPrime
  0.0 - FourMom.dot q q

/-- The Bjorken variable `x = Q² / (2 p·q)`. -/
def xBj (p k kPrime : FourMom) : Float :=
  let q := qTransfer k kPrime
  q2 k kPrime / (2.0 * FourMom.dot p q)

/-- The inelasticity `y = (p·q)/(p·k)`. -/
def yInel (p k kPrime : FourMom) : Float :=
  let q := qTransfer k kPrime
  FourMom.dot p q / FourMom.dot p k

/-- The hadronic invariant mass squared `W² = (p+q)·(p+q)`. -/
def w2 (p k kPrime : FourMom) : Float :=
  let q := qTransfer k kPrime
  let pq := FourMom.add p q
  FourMom.dot pq pq

/-- The squared beam-pair centre-of-mass energy `s = (k+p)·(k+p)`. -/
def sTotal (k p : FourMom) : Float :=
  let kp := FourMom.add k p
  FourMom.dot kp kp

/-- `Q² = x y s` in the massless limit, used the other way round: given `x`, `y` and `s`,
the hard scale.  This is how the sampler works — it draws `(x, y)` and derives `Q²` — so the
relation is a definition here rather than an identity to be checked. -/
def q2OfXY (s x y : Float) : Float := x * y * s

/-- The inelasticity implied by `x`, `Q²` and `s`, in the massless limit: `y = Q²/(x s)`. -/
def yOfXQ2 (s x q2v : Float) : Float := q2v / (x * s)

/-- The maximum `Q²` kinematically available at given `x`, namely `x s` (attained at `y = 1`). -/
def q2Max (s x : Float) : Float := x * s

end Generator
end Physlib
