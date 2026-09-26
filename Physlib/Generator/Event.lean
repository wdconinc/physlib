/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Generator.Config
public import Physlib.HepMC3.Graph
public import Physlib.Numerics.Random

/-!
# A placeholder event, to exercise the pipeline before any physics exists

Phase 0's deliverable is a binary that consumes a configuration and emits a valid `Asciiv3`
file.  That tests seeding, sampling, graph construction, record ordering and serialization
together — everything except the physics, which is Phase 1.

**The kinematics here are not physics and must not be read as physics.** The scattered
lepton's direction and energy are drawn from a uniform distribution with no matrix element
behind them, and the second outgoing particle is *defined* as whatever four-momentum
balances the event.  There is no cross section, no PDF and no `Q²` cut, and `RunConfig.q2Min`
is deliberately ignored.  What the event does have is the right *shape*: two beams with
status 4, a hard vertex, two outgoing particles with status 1, and exact four-momentum
conservation by construction — which is the property Phase 1 will check numerically and
which is worth having under test from the start.

Conservation is exact rather than approximate precisely because the recoil is defined by
subtraction: whatever rounding the scattered lepton's components carry, the balancing
particle carries the complement, so the sum reproduces the incoming total bit for bit.
-/

@[expose] public section

namespace Physlib
namespace Generator

open HepMC3 Numerics Random

/-- Component-wise sum of two four-vectors. -/
def addFV (a b : FourVector) : FourVector :=
  { x := a.x + b.x, y := a.y + b.y, z := a.z + b.z, t := a.t + b.t }

/-- Component-wise difference of two four-vectors. -/
def subFV (a b : FourVector) : FourVector :=
  { x := a.x - b.x, y := a.y - b.y, z := a.z - b.z, t := a.t - b.t }

/-- Draw a placeholder final state and assemble it into a `GenEvent`.

The lepton is given a transverse kick of up to 2 GeV at a uniform azimuth and keeps between
20% and 80% of its energy; it is put on the massless shell.  The recoil particle absorbs the
remainder exactly.  Returns `none` only if the graph is malformed, which for this fixed
topology cannot happen — the `Option` is the honest signature of `ofGraph?`, not a real
failure mode here. -/
def trivialEvent {g : Type} [RandomGen g] [Monad m] (c : RunConfig) (n : Nat) :
    RandGT g m (Option GenEvent) := do
  -- Three independent draws. An earlier version reused `u` for both the transverse kick and
  -- the longitudinal fraction, which silently correlated them: every event with a large `pt`
  -- also had a large `|pz|`. The docstrings described them as separate choices, so the code
  -- and the stated intent disagreed.
  let u ← uniform01
  let v ← uniform01
  let w ← uniform01
  let pIn := addFV c.leptonP c.hadronP
  -- scattered lepton: uniform azimuth, transverse kick, massless shell
  let pt := 2.0 * u
  let phi := 6.283185307179586 * v
  let pz := -c.lepton.energy * (0.2 + 0.6 * w)
  let px := pt * phi.cos
  let py := pt * phi.sin
  let e := (px * px + py * py + pz * pz).sqrt
  let pLep : FourVector := { x := px, y := py, z := pz, t := e }
  -- recoil defined by subtraction, so the event balances exactly
  let pRec := subFV pIn pLep
  let parts : List GraphParticle :=
    [ { id := 1, pdg := c.lepton.pdg, momentum := c.leptonP, mass := c.lepton.mass, status := 4 },
      { id := 2, pdg := c.hadron.pdg, momentum := c.hadronP, mass := c.hadron.mass, status := 4 },
      { id := 3, pdg := c.lepton.pdg, momentum := pLep, mass := 0.0, status := 1 },
      { id := 4, pdg := 2, momentum := pRec, mass := 0.0, status := 1 } ]
  let verts : List GraphVertex :=
    [ { id := -1, incoming := [1, 2], outgoing := [3, 4] } ]
  pure (GenEvent.ofGraph? (n : Int) parts verts (weights := [1.0]))

/-- Generate `c.nEvents` placeholder events from the run seed.

Every event is drawn from the one seeded stream, so the whole run is reproducible from
`c.seed` alone.  Per-stage substreams (`Numerics.substream`) become relevant once there is
more than one stage. -/
def trivialRun (c : RunConfig) : IO (List GenEvent) :=
  IO.runRandWith c.seed do
    let mut out : List GenEvent := []
    for i in [0:c.nEvents] do
      match ← trivialEvent c (i + 1) with
      | some e => out := e :: out
      | none => pure ()
    -- Prepend and reverse once; see the note in DISEvent.loRun. Appending per event is
    -- O(n) each time and makes the whole run O(n^2).
    pure out.reverse

end Generator
end Physlib
