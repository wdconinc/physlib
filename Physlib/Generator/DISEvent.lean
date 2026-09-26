/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Generator.Config
public import Physlib.Generator.Sampler
public import Physlib.Generator.Jets
public import Physlib.Generator.Shower
public import Physlib.HepMC3.Format
public import Physlib.HepMC3.Graph

/-!
# Assembling a leading-order DIS event

From a sampled `(x, Q², y)` to a HepMC3 event graph.

## Reconstructing the final state

Take the lepton beam along `-z` with energy `E_e` and the hadron beam along `+z` with energy
`E_p`, both massless, so `s = 4 E_e E_p`.  Writing `θ` for the scattered lepton's polar angle
measured from the *incoming lepton* direction, the two defining invariants are

  `Q² = 2 E_e E' (1 - cos θ)`,   `y = 1 - E'(1 + cos θ)/(2 E_e)`.

These are two linear equations in the pair `(E', E' cos θ)`, and solving them gives the
closed form used below:

  `E'       = E_e (1 - y) + Q²/(4 E_e)`
  `E' cos θ = E_e (1 - y) - Q²/(4 E_e)`

so no numerical inversion is needed.  The transverse momentum follows from
`E' sin θ = √(E'² - (E' cos θ)²)`, distributed uniformly in azimuth.

## Why momentum conservation is exact

At leading order the struck parton carries momentum fraction `x`, so the incoming parton is
`x·p` and the beam remnant is `(1-x)·p`.  The outgoing quark is *defined* as `x·p + q` with
`q = k - k'`.  Summing the final state then telescopes:

  `k' + (x p + q) + (1-x) p = k' + x p + k - k' + p - x p = k + p`,

which is the incoming total, term by term.  So conservation holds bit for bit rather than to
a tolerance — the same construction-by-subtraction used in the Phase 0 placeholder, and the
reason the numerical check downstream returns exactly zero rather than something small.

## Topology and what it omits

Two vertices: the proton emits the struck parton and a remnant, and the lepton scatters off
that parton.  The proton vertex has exactly one incoming particle, no position and no status,
so `ofGraph?` elides it under the single-mother rule and the daughters carry the proton's
identifier — a real event exercising the elision path.

Colour flow is recorded as `flow1`/`flow2` attributes: the struck quark carries colour `101`
and the remnant the matching anticolour, making the pair a singlet.  This is the minimal
consistent assignment; it is not a colour-reconnection model, and with no shower there is
nothing yet to reconnect.

**Not modelled:** the remnant is a single particle with the proton's quantum numbers rather
than a diquark plus sea, the struck parton is always assigned the up-quark identifier rather
than being chosen by flavour from the `F₂` decomposition, and there is no intrinsic transverse
momentum.  The first two are straightforward to fix and are deliberately deferred; the flavour
choice in particular should be sampled from the same charge-weighted decomposition that builds
`F₂`, and until it is, the flavour content of the output is wrong even though the kinematics
are right.
-/

@[expose] public section

namespace Physlib
namespace Generator

open Numerics HepMC3 Rand

/-- The scattered lepton's four-momentum, from the sampled point and the beam energy.

`phi` is the azimuth in `[0, 2π)`.  The lepton beam travels along `-z`, so the `z` component
is `-E' cos θ`. -/
def scatteredLepton (eBeam : Float) (pt : HardPoint) (phi : Float) : FourMom :=
  let eP := eBeam * (1.0 - pt.y) + pt.q2 / (4.0 * eBeam)
  let eCos := eBeam * (1.0 - pt.y) - pt.q2 / (4.0 * eBeam)
  let pt2 := eP * eP - eCos * eCos
  let ptr := (if pt2 > 0.0 then pt2 else 0.0).sqrt
  { px := ptr * phi.cos, py := ptr * phi.sin, pz := -eCos, e := eP }

/-- Build the leading-order event graph.  Returns `none` only if the graph is malformed,
which for this fixed topology cannot happen. -/
def loEventOfPoint (c : RunConfig) (n : Nat) (pt : HardPoint) (phi : Float) :
    Option GenEvent :=
  let k : FourMom := { px := 0.0, py := 0.0, pz := -c.lepton.energy, e := c.lepton.energy }
  let p : FourMom := { px := 0.0, py := 0.0, pz := c.hadron.energy, e := c.hadron.energy }
  let kPrime := scatteredLepton c.lepton.energy pt phi
  let q := FourMom.sub k kPrime
  let pIn := FourMom.smul pt.x p
  let qOut := FourMom.add pIn q
  let remnant := FourMom.smul (1.0 - pt.x) p
  let parts : List GraphParticle :=
    [ { id := 1, pdg := c.lepton.pdg, momentum := k.toFourVector,
        mass := 0.0, status := 4 },
      { id := 2, pdg := c.hadron.pdg, momentum := p.toFourVector,
        mass := 0.0, status := 4 },
      -- the struck parton, incoming to the hard vertex
      { id := 3, pdg := 2, momentum := pIn.toFourVector, mass := 0.0, status := 21 },
      -- beam remnant
      { id := 4, pdg := 2101, momentum := remnant.toFourVector, mass := 0.0, status := 1 },
      { id := 5, pdg := c.lepton.pdg, momentum := kPrime.toFourVector,
        mass := 0.0, status := 1 },
      { id := 6, pdg := 2, momentum := qOut.toFourVector, mass := 0.0, status := 1 } ]
  let verts : List GraphVertex :=
    [ -- proton -> struck parton + remnant; one incoming, so this vertex is elided
      { id := -1, incoming := [2], outgoing := [3, 4] },
      -- the hard scattering
      { id := -2, incoming := [1, 3], outgoing := [5, 6] } ]
  let attrs : List Attribute :=
    [ { target := 6, name := "flow1", value := "101" },
      { target := 4, name := "flow2", value := "101" },
      { target := 3, name := "flow1", value := "101" },
      -- `toString` on a `Float` emits only 6 decimal places, which for `x ~ 3e-4` leaves
      -- three significant figures. The momenta in the same file carry 16, so a reader
      -- recomputing `x` from them would disagree with this attribute in the 4th digit.
      -- Use the writer's own exact formatter, at the same 16 digits.
      { target := 0, name := "xBj", value := formatScientific 16 pt.x },
      { target := 0, name := "Q2", value := formatScientific 16 pt.q2 },
      { target := 0, name := "yInel", value := formatScientific 16 pt.y } ]
  GenEvent.ofGraph? (n : Int) parts verts (weights := [1.0]) (attributes := attrs)

/-- Assemble one showered event: the leading-order hard scattering with the outgoing quark
replaced by the parton shower's products.

## Where the momentum imbalance goes, and why there

Shower splittings conserve energy exactly and three-momentum only to collinear accuracy
(`Physlib.Generator.Shower`).  Something in the record must absorb the difference, and the
choice determines which vertex stops balancing:

* absorb it in the **beam remnant** — then the event conserves four-momentum exactly overall,
  and the proton-splitting vertex `-1` no longer balances;
* absorb it at the **shower vertex** — then that vertex is the only unbalanced one, but the
  event total no longer conserves.

This takes the first.  Overall conservation is a property Phase 1 established and validated,
and giving it up would regress a checked invariant to tidy a vertex that is already a
fiction: vertex `-1` has one incoming particle and is elided by the writer, so it carries no
physics.  The consequence is stated plainly because it is easy to be misled by it — **a
four-momentum conservation check on a showered event cannot detect a shower kinematics bug**,
since the remnant is defined to make it pass.  The imbalance is therefore written into the
event as the `showerImbalance` attribute, so the thing the check cannot see is at least on
the record. -/
def showeredEventOfPoint (c : RunConfig) (n : Nat) (pt : HardPoint) (phi : Float)
    (sr : ShowerResult) : Option GenEvent :=
  let k : FourMom := { px := 0.0, py := 0.0, pz := -c.lepton.energy, e := c.lepton.energy }
  let p : FourMom := { px := 0.0, py := 0.0, pz := c.hadron.energy, e := c.hadron.energy }
  let kPrime := scatteredLepton c.lepton.energy pt phi
  let q := FourMom.sub k kPrime
  let pIn := FourMom.smul pt.x p
  let qOut := FourMom.add pIn q
  -- everything the shower produced, quark first
  let products : List FourMom := sr.quark :: sr.gluons
  let visible := products.foldl FourMom.add kPrime
  -- remnant by subtraction: this is what makes the event conserve exactly
  let remnant := FourMom.sub (FourMom.add k p) visible
  -- what the shower failed to conserve, i.e. how far the remnant had to move
  let imbalance :=
    FourMom.sub (products.foldl FourMom.add { px := 0.0, py := 0.0, pz := 0.0, e := 0.0 })
      qOut
  let nG := sr.gluons.length
  let quarkId : Nat := 7
  let gluonIds : List Nat := (List.range nG).map (fun i => 8 + i)
  let fixed : List GraphParticle :=
    [ { id := 1, pdg := c.lepton.pdg, momentum := k.toFourVector, mass := 0.0, status := 4 },
      { id := 2, pdg := c.hadron.pdg, momentum := p.toFourVector, mass := 0.0, status := 4 },
      { id := 3, pdg := 2, momentum := pIn.toFourVector, mass := 0.0, status := 21 },
      { id := 4, pdg := 2101, momentum := remnant.toFourVector, mass := 0.0, status := 1 },
      { id := 5, pdg := c.lepton.pdg, momentum := kPrime.toFourVector, mass := 0.0, status := 1 },
      -- the quark leaving the hard vertex, now an internal line the shower resolves
      { id := 6, pdg := 2, momentum := qOut.toFourVector, mass := 0.0, status := 2 },
      { id := quarkId, pdg := 2, momentum := sr.quark.toFourVector, mass := 0.0, status := 1 } ]
  let gluons : List GraphParticle :=
    (sr.gluons.zip gluonIds).map fun (g, i) =>
      { id := i, pdg := 21, momentum := g.toFourVector, mass := 0.0, status := 1 }
  let verts : List GraphVertex :=
    [ { id := -1, incoming := [2], outgoing := [3, 4] },
      { id := -2, incoming := [1, 3], outgoing := [5, 6] },
      -- the shower, collapsed to a single vertex: the branching history is not recorded,
      -- so this is not a cascade of 1 -> 2 vertices and carries no emission ordering
      { id := -3, incoming := [6], outgoing := quarkId :: gluonIds } ]
  let attrs : List Attribute :=
    [ { target := 0, name := "xBj", value := formatScientific 16 pt.x },
      { target := 0, name := "Q2", value := formatScientific 16 pt.q2 },
      { target := 0, name := "yInel", value := formatScientific 16 pt.y },
      { target := 0, name := "nEmissions", value := toString nG },
      { target := 0, name := "showerTrials", value := toString sr.trials },
      { target := 0, name := "showerImbalance", value := formatScientific 16 (imbalance.p3) },
      -- Durham observables on the shower products, normalized to the photon virtuality.
      -- The beam remnant is excluded: the algorithm is exclusive and has no beam jet.
      { target := 0, name := "nJets",
        value := toString (jetMultiplicity products pt.q2 0.01) },
      { target := 0, name := "y23",
        value := formatScientific 16 (let ms := mergeScales products pt.q2
                                      if ms.size ≥ 1 then ms[ms.size - 1]! else 0.0) } ]
  GenEvent.ofGraph? (n : Int) (fixed ++ gluons) verts (weights := [1.0]) (attributes := attrs)

/-- Sample one showered event: the leading-order point, then the final-state shower off the
struck quark evolved from `Q²` down to the cutoff. -/
def showeredEvent {g : Type} [RandomGen g] [Monad m]
    (c : RunConfig) (r : Region) (sc : ShowerConfig) (wMax : Float) (n : Nat)
    (fuel : Nat := 10000) :
    RandGT g m (Option GenEvent × Nat × Nat × Nat × Bool) := do
  let (pt?, used, viol) ← sampleHardPoint r wMax fuel 0 0
  match pt? with
  | none => pure (none, used, viol, 0, false)
  | some pt => do
    let u ← uniform01
    let phi := 6.283185307179586 * u
    let k : FourMom := { px := 0.0, py := 0.0, pz := -c.lepton.energy, e := c.lepton.energy }
    let p : FourMom := { px := 0.0, py := 0.0, pz := c.hadron.energy, e := c.hadron.energy }
    let kPrime := scatteredLepton c.lepton.energy pt phi
    let qOut := FourMom.add (FourMom.smul pt.x p) (FourMom.sub k kPrime)
    let sr ← evolveQuark sc qOut pt.q2
    pure (showeredEventOfPoint c n pt phi sr, used, viol, sr.gluons.length, sr.exhausted)

/-- Sample one leading-order event.  Returns the event, the trials it cost, and the number of
weight-bound violations seen while producing it. -/
def loEvent {g : Type} [RandomGen g] [Monad m]
    (c : RunConfig) (r : Region) (wMax : Float) (n : Nat) (fuel : Nat := 10000) :
    RandGT g m (Option GenEvent × Nat × Nat) := do
  let (pt?, used, viol) ← sampleHardPoint r wMax fuel 0 0
  match pt? with
  | none => pure (none, used, viol)
  | some pt => do
    let u ← uniform01
    let phi := 6.283185307179586 * u
    pure (loEventOfPoint c n pt phi, used, viol)

/-- Generate a full run of leading-order events, returning the events and the run counters. -/
def loRun (c : RunConfig) : IO (List GenEvent × SampleStats) :=
  let r : Region := { s := c.sTotal, q2Min := c.q2Min }
  let wMax := weightBound r
  IO.runRandWith c.seed do
    let mut evs : List GenEvent := []
    let mut st : SampleStats := {}
    for i in [0:c.nEvents] do
      let (ev?, used, viol) ← loEvent c r wMax (i + 1)
      st := st.record ev?.isSome used viol
      match ev? with
      | some ev => evs := ev :: evs
      | none => pure ()
    -- Prepend and reverse once: `evs ++ [ev]` walks the whole list on every event, which
    -- makes generation quadratic. Measured before the fix: 7649 events/s at N=5000 but
    -- 1283 events/s at N=50000 -- the rate FELL as N grew, which is the signature.
    pure (evs.reverse, st)

/-- Generate a full run of showered events.

Returns the events and, alongside the hard-scattering counters, the total number of
emissions and the number of events whose shower exhausted its fuel.  An exhausted shower
means the event is incompletely evolved, so that count is a correctness signal and not a
performance one — it should be zero. -/
def showerRun (c : RunConfig) (sc : ShowerConfig := {}) :
    IO (List GenEvent × SampleStats × Nat × Nat) :=
  let r : Region := { s := c.sTotal, q2Min := c.q2Min }
  let wMax := weightBound r
  IO.runRandWith c.seed do
    let mut evs : List GenEvent := []
    let mut st : SampleStats := {}
    let mut emissions : Nat := 0
    let mut exhausted : Nat := 0
    for i in [0:c.nEvents] do
      let (ev?, used, viol, nEmit, exh) ← showeredEvent c r sc wMax (i + 1)
      st := st.record ev?.isSome used viol
      emissions := emissions + nEmit
      if exh then exhausted := exhausted + 1
      match ev? with
      | some ev => evs := ev :: evs
      | none => pure ()
    pure (evs.reverse, st, emissions, exhausted)

end Generator
end Physlib
