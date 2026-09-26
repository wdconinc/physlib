/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.HepMC3.Basic

/-!
# Building an event record from a graph

`Physlib.HepMC3.Basic` models an event as an *ordered* list of `P` and `V` records, because
that order is part of the `Asciiv3` format.  Producing that order by hand is error-prone: a
vertex's `V` line must follow the `P` lines of its incoming particles and precede those of
its outgoing ones, and some vertices are not written at all.

This module takes the other view — a plain graph of particles and vertices, in any order —
and derives the record sequence.  A generator builds graphs; only this module needs to know
what the serializer expects.

## The two rules it implements

**Topological order.** A particle's `parent` field refers backwards, so every vertex is
emitted only once all of its incoming particles have been emitted.  Particles produced by no
vertex (the beams) come first, carrying `parent = 0`.

**Single-mother elision.** A vertex with exactly one incoming particle, no position and no
status carries no information that the daughters cannot: HepMC3's own writer omits it and
records the *mother particle's* identifier — positive — in each daughter's `parent` field.
`GenEvent.numVertices` already knows to count such vertices by recovering them from the
distinct positive `parent` references, which is why an elided vertex still appears in the
`E` line count.

The elision condition is deliberately conservative: a vertex is elided only when it has
exactly one incoming particle, `position = none`, and `status = 0`.  A vertex carrying a
position or a status is always written, because that information has nowhere else to go.

## Termination

The emission loop is driven by explicit fuel, one unit per vertex, rather than being marked
`partial`.  Each iteration emits at least one vertex, so the fuel bound is tight; exhausting
it means the graph is cyclic or refers to a missing particle, and `ofGraph?` reports that as
`none` rather than looping or silently truncating.

The body-only entry point is `bodyOfGraph?`; `GenEvent.ofGraph?` wraps it into an event.
They are deliberately not both called `ofGraph?`: inside this namespace the bare name would
resolve to the `GenEvent` one, silently passing the particle list where an event number is
expected.
-/

@[expose] public section

namespace Physlib
namespace HepMC3

/-- A vertex of an event graph, before serialization order is decided. -/
structure GraphVertex where
  /-- Object identifier; negative, unique within the event. -/
  id : Int
  /-- Identifiers of the incoming particles. -/
  incoming : List Nat
  /-- Identifiers of the outgoing particles. -/
  outgoing : List Nat
  /-- Status code; `0` carries no information and permits elision. -/
  status : Int := 0
  /-- Optional space-time position; when present the vertex is never elided. -/
  position : Option FourVector := none
deriving Repr, Inhabited

/-- A particle of an event graph.  Unlike `GenParticle` this carries no `parent`: the
production reference is derived from the graph. -/
structure GraphParticle where
  /-- Object identifier; positive, unique within the event. -/
  id : Nat
  /-- PDG Monte Carlo particle identifier. -/
  pdg : Int
  /-- Four-momentum, in the event's momentum unit. -/
  momentum : FourVector
  /-- Generated mass. -/
  mass : Float := 0.0
  /-- HepMC status code. -/
  status : Int := 1
deriving Repr, Inhabited

/-- Is this vertex elidable under the single-mother rule? -/
def GraphVertex.elidable (v : GraphVertex) : Bool :=
  v.incoming.length == 1 && v.position.isNone && v.status == 0

namespace Graph

/-- Turn a graph particle into a `GenParticle` with the given production reference. -/
def toGenParticle (p : GraphParticle) (parent : Int) : GenParticle :=
  { id := p.id, parent := parent, pdg := p.pdg, momentum := p.momentum,
    mass := p.mass, status := p.status }

/-- One emission step: pick the first vertex whose incoming particles have all been emitted,
append its records, and return the extended state.  `none` when no vertex is ready. -/
def step (parts : List GraphParticle) (emitted : List Nat)
    (pending : List GraphVertex) (acc : List EventRecord) :
    Option (List Nat × List GraphVertex × List EventRecord) :=
  match pending.findIdx? (fun v => v.incoming.all (emitted.contains ·)) with
  | none => none
  | some i =>
    match pending[i]? with
    | none => none
    | some v =>
      let rest := (pending.take i) ++ (pending.drop (i + 1))
      -- the production reference the daughters will carry
      let parent : Int := if v.elidable then (v.incoming.headD 0 : Nat) else v.id
      let vrecs : List EventRecord :=
        if v.elidable then []
        else [.vertex { id := v.id, status := v.status,
                        incoming := v.incoming, position := v.position }]
      -- A total traversal, deliberately not `filterMap`: an outgoing identifier with no
      -- matching particle is a malformed graph, and dropping it would silently emit a
      -- truncated body while still marking the identifier as emitted.
      match v.outgoing.mapM (fun pid => parts.find? (fun p => p.id == pid)) with
      | none => none
      | some ps =>
        let precs : List EventRecord := ps.map fun p => .particle (toGenParticle p parent)
        -- `acc` is accumulated REVERSED and flipped once in `bodyOfGraph?`. Appending to
        -- its end here would walk the whole accumulated body at every vertex, making the
        -- conversion quadratic in the particle count. Invisible for a 6-particle
        -- leading-order event; a parton shower produces hundreds, and that is the next
        -- thing due to run through this code.
        some (v.outgoing.reverseAux emitted, rest, (vrecs ++ precs).reverseAux acc)

/-- Drive `step` to exhaustion with explicit fuel. -/
def loop : Nat → List GraphParticle → List Nat → List GraphVertex → List EventRecord →
    Option (List EventRecord)
  | 0, _, _, pending, acc => if pending.isEmpty then some acc else none
  | _ + 1, parts, emitted, [], acc => let _ := parts; let _ := emitted; some acc
  | n + 1, parts, emitted, pending, acc =>
    match step parts emitted pending acc with
    | none => none
    | some (emitted', pending', acc') => loop n parts emitted' pending' acc'

end Graph

/-- Derive the ordered event body from a graph, or `none` if the graph is cyclic or refers to
a particle that is not present.

Beam particles — those produced by no vertex — are emitted first, in the order given, with
`parent = 0`.  Every other particle is emitted immediately after the vertex that produced it,
which is written unless the single-mother rule elides it. -/
def bodyOfGraph? (parts : List GraphParticle) (verts : List GraphVertex) :
    Option (List EventRecord) :=
  let produced : List Nat := verts.flatMap (·.outgoing)
  let beams := parts.filter fun p => !produced.contains p.id
  -- Seed the accumulator reversed, to match `Graph.step`, and flip once at the end.
  let beamRecs : List EventRecord :=
    (beams.map fun p => .particle (Graph.toGenParticle p 0)).reverse
  (Graph.loop verts.length parts (beams.map (·.id)) verts beamRecs).map List.reverse

/-- Build a `GenEvent` from a graph, keeping every other field at its default.

Returns `none` on a graph `bodyOfGraph?` rejects. -/
def GenEvent.ofGraph? (eventNumber : Int) (parts : List GraphParticle)
    (verts : List GraphVertex) (weights : List Float := [])
    (attributes : List Attribute := []) : Option GenEvent :=
  (bodyOfGraph? parts verts).map fun body =>
    { eventNumber := eventNumber, weights := weights, attributes := attributes, body := body }

end HepMC3
end Physlib
