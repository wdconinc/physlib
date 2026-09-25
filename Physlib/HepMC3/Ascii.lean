/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.HepMC3.Basic
public import Physlib.HepMC3.Format

/-!
# The HepMC3 `Asciiv3` writer

Serialization of `Physlib.HepMC3.GenEvent` into the `Asciiv3` text format, which is what
HepMC3's `WriterAscii` produces and its `ReaderAscii` consumes.

## The format

A file is a version line, a start marker, the run header, the events, and an end marker:

```text
HepMC::Version 3.02.05
HepMC::Asciiv3-START_EVENT_LISTING
W <weight names>
T <tool>
A <name> <value>
E <event number> <vertices> <particles>
U <momentum unit> <length unit>
W <weights>
A <target> <name> <value>
P <id> <parent> <pdg> <px> <py> <pz> <E> <m> <status>
V <id> <status> [<incoming ids>] @ <x> <y> <z> <t>
HepMC::Asciiv3-END_EVENT_LISTING
```

Three details are worth stating because they are easy to get wrong and the reference
documentation does not spell them out.

**Precision differs by field.**  Momenta, masses and vertex positions are written at 16
digits after the point; weights are written at 22.  Both are `printf`-style `%.Ne`; see
`Physlib.HepMC3.Format`.

**The field separator inside `W` and `T` lines is an escaped newline.**  HepMC3 joins the
subfields with `'\n'` and then escapes the result, mapping `'\\'` to `"\\\\"` and `'\n'` to
`"\\|"`.  The familiar `\|` between a tool's name and version is that escape, not a
separator in its own right.  A literal `|` is consequently *not* escaped and passes
through unchanged, while a literal newline inside a field is indistinguishable from a
separator once written.  That last point is a lossy quirk of the format, reproduced here
deliberately: matching the reference writer matters more than improving on it.

**Empty collections drop their lines.**  With no weights, neither the run-header `W` line
nor the per-event `W` line is written at all, rather than being written empty.

## Main definitions

* `Physlib.HepMC3.Ascii.document` — a whole file as a `String`.
* `Physlib.HepMC3.Ascii.writeFile` — the same, written to disk.
-/

@[expose] public section

namespace Physlib
namespace HepMC3
namespace Ascii

/-- Digits after the point for momenta, masses and positions. -/
def momentumPrecision : Nat := 16

/-- Digits after the point for weights. -/
def weightPrecision : Nat := 22

/-- The HepMC3 version stamped into the header.  Readers accept files written by any 3.x
writer; this is the version whose output this module reproduces. -/
def defaultVersion : String := "3.02.05"

/-- Escape a string for inclusion in a `W` or `T` line: `'\\'` becomes `"\\\\"` and a
newline becomes `"\\|"`. -/
def escapeString (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\|"
    else acc.push c

/-- Join subfields the way HepMC3 does: concatenate with newlines, then escape.  The
escaping is what turns the joining newlines into the `\|` seen in output. -/
def joinFields (parts : List String) : String :=
  escapeString (String.intercalate "\n" parts)

/-- Render a momentum, mass or position component. -/
def fmtMomentum (x : Float) : String := formatScientific momentumPrecision x

/-- Render a weight. -/
def fmtWeight (x : Float) : String := formatScientific weightPrecision x

/-- The `P` line for a particle. -/
def particleLine (p : GenParticle) : String :=
  String.intercalate " "
    [ "P", toString p.id, toString p.parent, toString p.pdg,
      fmtMomentum p.momentum.x, fmtMomentum p.momentum.y,
      fmtMomentum p.momentum.z, fmtMomentum p.momentum.t,
      fmtMomentum p.mass, toString p.status ]

/-- The `V` line for a vertex, with the `@` position suffix when a position is present. -/
def vertexLine (v : GenVertex) : String :=
  let base := String.intercalate " "
    [ "V", toString v.id, toString v.status,
      "[" ++ String.intercalate "," (v.incoming.map toString) ++ "]" ]
  match v.position with
  | none => base
  | some q =>
    base ++ " @ " ++ String.intercalate " "
      [ fmtMomentum q.x, fmtMomentum q.y, fmtMomentum q.z, fmtMomentum q.t ]

/-- The line for one body record. -/
def recordLine : EventRecord → String
  | .particle p => particleLine p
  | .vertex v => vertexLine v

/-- The run header lines, written once before the first event. -/
def runInfoLines (r : GenRunInfo) : List String :=
  (if r.weightNames.isEmpty then [] else ["W " ++ joinFields r.weightNames])
    ++ r.tools.map (fun t => "T " ++ joinFields [t.name, t.version, t.description])
    ++ r.attributes.map (fun a => "A " ++ a.1 ++ " " ++ a.2)

/-- The lines of one event, beginning with its `E` line. -/
def eventLines (e : GenEvent) : List String :=
  [ String.intercalate " "
      ["E", toString e.eventNumber, toString e.numVertices, toString e.numParticles],
    String.intercalate " " ["U", e.momentumUnit.symbol, e.lengthUnit.symbol] ]
    ++ (if e.weights.isEmpty then []
        else ["W " ++ String.intercalate " " (e.weights.map fmtWeight)])
    ++ e.attributes.map (fun a => "A " ++ toString a.target ++ " " ++ a.name ++ " " ++ a.value)
    ++ e.body.map recordLine

/-- A complete `Asciiv3` document: header, run info, every event, and the end marker.

The result ends with a newline after the end marker and one blank line, as the reference
writer's output does. -/
def document (run : GenRunInfo) (events : List GenEvent)
    (version : String := defaultVersion) : String :=
  let body := events.foldr (fun e acc => eventLines e ++ acc) []
  String.intercalate "\n"
    ([ "HepMC::Version " ++ version, "HepMC::Asciiv3-START_EVENT_LISTING" ]
      ++ runInfoLines run ++ body
      ++ [ "HepMC::Asciiv3-END_EVENT_LISTING", "" ]) ++ "\n"

/-- Write a complete `Asciiv3` document to `path`. -/
def writeFile (path : System.FilePath) (run : GenRunInfo) (events : List GenEvent)
    (version : String := defaultVersion) : IO Unit :=
  IO.FS.writeFile path (document run events version)

end Ascii
end HepMC3
end Physlib
