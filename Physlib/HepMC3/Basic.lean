/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

/-!
# HepMC3 event records

The data model of the HepMC3 event record, as far as the `Asciiv3` serialization needs it.
`Physlib.HepMC3.Ascii` turns these into bytes.

## Why `Float` and not `ℝ`

Everywhere else in this library a momentum is a real number, because the statements being
proved are statements about real numbers.  A HepMC3 file, however, holds IEEE-754 doubles:
that is what the format is, and what every reader will parse.  So this module works in
`Float` and draws the boundary explicitly here.  Converting a physical quantity carrying a
proof into the `Float` that represents it is a separate step, belonging with the content
rather than with the format, and is deliberately not attempted here.

## The one structural subtlety

A HepMC3 event is a graph, but the serialization is a flat, *ordered* line sequence in
which `P` and `V` lines interleave: a vertex's `V` line must follow the `P` lines of its
incoming particles and precede those of its outgoing ones, because a particle's second
field refers backwards to what produced it.  That field is not simply a vertex identifier:

* `0` — the particle has no production vertex (a beam particle, or an orphan);
* negative — the object identifier of the `V` line it comes out of;
* positive — the identifier of its **single mother particle**.

The last case is how the format elides a vertex.  A vertex with zero status, no position
and one incoming particle carries no information beyond "these came from that", so the
reference writer emits no `V` line for it at all and points its daughters at the mother
particle instead.  This is why `numVertices` below cannot simply count `V` records.

`GenEvent.body` is therefore an ordered list of records rather than two separate
collections: it is the honest model of what the file contains, and it keeps the writer
total.  Building that order from a particle/vertex graph is a separate concern.

## Main definitions

* `Physlib.HepMC3.GenEvent` — one event.
* `Physlib.HepMC3.GenRunInfo` — the run header shared by all events in a file.
-/

@[expose] public section

namespace Physlib
namespace HepMC3

/-- Momentum unit declared in the `U` line. -/
inductive MomentumUnit
  /-- Giga-electronvolts. -/
  | gev
  /-- Mega-electronvolts. -/
  | mev
deriving Repr, DecidableEq, Inhabited

/-- Length unit declared in the `U` line. -/
inductive LengthUnit
  /-- Millimetres. -/
  | mm
  /-- Centimetres. -/
  | cm
deriving Repr, DecidableEq, Inhabited

/-- The token HepMC3 writes for a momentum unit. -/
def MomentumUnit.symbol : MomentumUnit → String
  | .gev => "GEV"
  | .mev => "MEV"

/-- The token HepMC3 writes for a length unit. -/
def LengthUnit.symbol : LengthUnit → String
  | .mm => "MM"
  | .cm => "CM"

/-- A four-vector, used both for four-momenta `(px, py, pz, E)` and for vertex positions
`(x, y, z, t)`. -/
structure FourVector where
  /-- First spatial component, or `px`. -/
  x : Float
  /-- Second spatial component, or `py`. -/
  y : Float
  /-- Third spatial component, or `pz`. -/
  z : Float
  /-- Time component, or the energy `E`. -/
  t : Float
deriving Repr, Inhabited

/-- A particle, one `P` line. -/
structure GenParticle where
  /-- Object identifier, positive and unique within the event. -/
  id : Nat
  /-- Production reference: `0` for none, negative for a vertex identifier, positive for a
  single mother particle.  See the module docstring. -/
  parent : Int
  /-- PDG Monte Carlo particle identifier. -/
  pdg : Int
  /-- Four-momentum, in the event's momentum unit. -/
  momentum : FourVector
  /-- Generated mass, which need not equal the mass implied by the four-momentum. -/
  mass : Float
  /-- HepMC status code: `1` final state, `2` decayed, `4` beam, generator-specific
  otherwise. -/
  status : Int
deriving Repr, Inhabited

/-- A vertex, one `V` line. -/
structure GenVertex where
  /-- Object identifier, negative and unique within the event. -/
  id : Int
  /-- Status code; `0` carries no information. -/
  status : Int
  /-- Identifiers of the incoming particles, written as a bracketed comma-separated list. -/
  incoming : List Nat
  /-- Optional space-time position; when absent the `@` suffix is omitted. -/
  position : Option FourVector
deriving Repr, Inhabited

/-- One line of the event body.  The order of these records is the order of the output, and
is part of the format — see the module docstring. -/
inductive EventRecord
  /-- A `P` line. -/
  | particle : GenParticle → EventRecord
  /-- A `V` line. -/
  | vertex : GenVertex → EventRecord
deriving Repr, Inhabited

/-- An event-scoped attribute, one `A` line.

`target` is `0` for the event itself, a positive particle identifier, or a negative vertex
identifier.  `value` is already in its serialized form: HepMC3 attributes are typed on the
C++ side but reach the file as opaque text, and this module does not interpret them. -/
structure Attribute where
  /-- `0` for the event, positive for a particle, negative for a vertex. -/
  target : Int
  /-- Attribute name; must not contain whitespace. -/
  name : String
  /-- Serialized attribute value. -/
  value : String
deriving Repr, Inhabited

/-- A generator or tool that contributed to the file, one `T` line. -/
structure Tool where
  /-- Tool name. -/
  name : String
  /-- Tool version. -/
  version : String
  /-- Free-form description. -/
  description : String
deriving Repr, Inhabited

/-- The run header, written once before the first event. -/
structure GenRunInfo where
  /-- Tools, one `T` line each. -/
  tools : List Tool := []
  /-- Weight names, written as a single `W` line; omitted entirely when empty. -/
  weightNames : List String := []
  /-- Run-scoped attributes, written as `A <name> <value>` with no target identifier. -/
  attributes : List (String × String) := []
deriving Repr, Inhabited

/-- A single event. -/
structure GenEvent where
  /-- Event number, as written in the `E` line. -/
  eventNumber : Int
  /-- Momentum unit for this event. -/
  momentumUnit : MomentumUnit := .gev
  /-- Length unit for this event. -/
  lengthUnit : LengthUnit := .mm
  /-- Event weights; the `W` line is omitted entirely when this is empty. -/
  weights : List Float := []
  /-- Event-scoped attributes. -/
  attributes : List Attribute := []
  /-- The ordered body of `P` and `V` records. -/
  body : List EventRecord := []
deriving Repr, Inhabited

/-- Number of particles in the event: one per `P` record. -/
def GenEvent.numParticles (e : GenEvent) : Nat :=
  e.body.countP fun r => match r with | .particle _ => true | .vertex _ => false

/-- Number of vertices in the event, as the `E` line reports it.

This is **not** the number of `V` records.  Vertices elided by the single-mother rule
(module docstring) still count, and each is identified by the mother particle it was folded
into, so the elided ones are recovered as the distinct positive `parent` references. -/
def GenEvent.numVertices (e : GenEvent) : Nat :=
  let explicit := e.body.countP fun r => match r with | .vertex _ => true | .particle _ => false
  let implicit := e.body.foldl (init := ([] : List Int)) fun acc r =>
    match r with
    | .particle p => if p.parent > 0 && !acc.contains p.parent then p.parent :: acc else acc
    | .vertex _ => acc
  explicit + implicit.length

end HepMC3
end Physlib
