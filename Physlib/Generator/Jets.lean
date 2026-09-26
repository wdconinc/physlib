/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Numerics.FourMom

/-!
# Durham jet clustering and the observables built from it

The exclusive `k_T` (Durham) algorithm, jet multiplicities, and the sequence of scales at
which the jet count changes.

## The measure

For two massless partons the Durham distance is

```
y_ij = 2 min(E_i², E_j²) (1 - cos θ_ij) / Q²
```

which for small angles is the squared relative transverse momentum of the softer parton
against the harder, normalized to the hard scale.  That is the same quantity the shower
orders its emissions in, which is why Durham is the natural jet definition to read a shower
with: the `y` at which two jets merge is, up to the approximation, the virtuality at which
the shower produced them.  `y₂₃` — the scale where three jets become two — is therefore a
direct probe of the hardest emission, and the observable most sensitive to whether the
shower's first branching is right.

## Conventions, which are choices and not derivations

* **Recombination is the E-scheme**: merged pseudo-jets are the four-momentum sum, so a
  merged jet is massive even when its constituents are not.  `durhamY` uses energies and
  angles and so remains well defined on massive pseudo-jets, but `1 - cos θ` is then no
  longer the massless relative-angle factor.  The alternatives (p-scheme, E0-scheme) rescale
  to keep jets massless and would give slightly different `y` values.
* **`Q²` is supplied by the caller**, not inferred.  For DIS the sensible choice is the
  photon virtuality, which makes `y` dimensionless against the hard scale that set the top
  of the shower.  Passing the squared total visible energy instead is also common and gives
  different numbers; nothing here can tell which the caller used.
* **The algorithm is exclusive**: clustering stops at `y_cut` and every parton ends in some
  jet.  There is no beam jet and no inclusive variant, so in DIS the beam remnant must be
  excluded by the caller — `Physlib.Generator` does that when it collects the partons.
-/

@[expose] public section

namespace Physlib
namespace Generator

open Physlib.Numerics

/-- The Durham distance `y_ij = 2 min(E_i², E_j²)(1 - cos θ_ij)/Q²`.

Returns `0` for a degenerate pair (either momentum vanishing), which merges it first — the
right behaviour, since a zero-momentum entry carries no information and should not survive
as a jet. -/
def durhamY (a b : FourMom) (q2 : Float) : Float :=
  let na := a.p3
  let nb := b.p3
  if na <= 0.0 || nb <= 0.0 || q2 <= 0.0 then 0.0
  else
    let cosTheta := (a.px * b.px + a.py * b.py + a.pz * b.pz) / (na * nb)
    let emin2 := if a.e < b.e then a.e * a.e else b.e * b.e
    2.0 * emin2 * (1.0 - cosTheta) / q2

/-- The closest pair under `durhamY`, as `(y, i, j)` with `i < j`.  `none` for fewer than
two entries. -/
def closestPair (ps : Array FourMom) (q2 : Float) : Option (Float × Nat × Nat) :=
  let pairs : List (Float × Nat × Nat) :=
    (List.range ps.size).flatMap fun i =>
      (List.range ps.size).filterMap fun j =>
        if i < j then some (durhamY ps[i]! ps[j]! q2, i, j) else none
  pairs.foldl
    (fun best c => match best with
      | none => some c
      | some b => if c.1 < b.1 then some c else some b)
    none

/-- One clustering step: merge the closest pair by four-momentum addition.  `none` when
there is nothing left to merge. -/
def mergeClosest (ps : Array FourMom) (q2 : Float) : Option (Float × Array FourMom) :=
  match closestPair ps q2 with
  | none => none
  | some (y, i, j) =>
    let merged := FourMom.add ps[i]! ps[j]!
    let rest : Array FourMom :=
      ((List.range ps.size).filterMap fun k =>
        if k == i || k == j then none else some ps[k]!).toArray
    some (y, rest.push merged)

/-- Cluster until every pair is separated by more than `yCut`, returning the jets.

Fuel-bounded rather than `partial`: each step removes one entry, so `ps.size` is always
enough and `Physlib.Generator.durhamJets` supplies it. -/
def clusterTo (ps : Array FourMom) (q2 yCut : Float) : Nat → Array FourMom
  | 0 => ps
  | k + 1 =>
    match mergeClosest ps q2 with
    | none => ps
    | some (y, next) => if y > yCut then ps else clusterTo next q2 yCut k

/-- The exclusive Durham jets of `ps` at resolution `yCut`. -/
def durhamJets (ps : List FourMom) (q2 yCut : Float) : Array FourMom :=
  let a := ps.toArray
  clusterTo a q2 yCut a.size

/-- The number of exclusive Durham jets at resolution `yCut`. -/
def jetMultiplicity (ps : List FourMom) (q2 yCut : Float) : Nat :=
  (durhamJets ps q2 yCut).size

/-- Every merge scale, in the order the algorithm merges them — so the `k`-th entry is the
`y` at which the jet count drops from `n - k + 1` to `n - k`.

`y₂₃`, the scale where three jets become two, is `(mergeScales ps q2)[n - 3]!` for `n`
partons; it is the standard probe of the hardest emission. -/
def mergeScales (ps : List FourMom) (q2 : Float) : Array Float :=
  let rec go (a : Array FourMom) (acc : Array Float) : Nat → Array Float
    | 0 => acc
    | k + 1 =>
      match mergeClosest a q2 with
      | none => acc
      | some (y, next) => go next (acc.push y) k
  go ps.toArray #[] ps.length

end Generator
end Physlib
