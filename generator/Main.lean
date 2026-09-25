/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
import Physlib.Generator.Event
import Physlib.HepMC3.Ascii

/-!
# The generator executable

Phase 0's deliverable: a binary that takes a run configuration and writes a valid `Asciiv3`
file.  The events it writes are placeholders with no physics in them (see
`Physlib.Generator.Event`); what this exercises is the pipeline — seeding, sampling, graph
construction, record ordering, serialization and file output.

This root lives outside `Physlib/` on purpose.  `check_file_imports` requires every file
under `Physlib/` to be imported into `Physlib.lean`, and an executable root is not a library
module.

Usage:

```
physlib_gen [--events N] [--seed N] [--output PATH] [--ebeam E] [--pbeam E]
```
-/

open Physlib Physlib.Generator

/-- Parse the command line into a `RunConfig`, starting from the defaults.

Unrecognized arguments are reported rather than ignored, so a mistyped flag fails loudly
instead of silently generating a differently-configured run. -/
def parseArgs (args : List String) (c : RunConfig) : Except String RunConfig :=
  match args with
  | [] => .ok c
  | "--events" :: v :: rest =>
    match v.toNat? with
    | some n => parseArgs rest { c with nEvents := n }
    | none => .error s!"--events expects a natural number, got '{v}'"
  | "--seed" :: v :: rest =>
    match v.toNat? with
    | some n => parseArgs rest { c with seed := n }
    | none => .error s!"--seed expects a natural number, got '{v}'"
  | "--output" :: v :: rest => parseArgs rest { c with output := v }
  | "--ebeam" :: v :: rest =>
    match v.toNat? with
    | some n => parseArgs rest { c with lepton := electronBeam n.toFloat }
    | none => .error s!"--ebeam expects a number, got '{v}'"
  | "--pbeam" :: v :: rest =>
    match v.toNat? with
    | some n => parseArgs rest { c with hadron := protonBeam n.toFloat }
    | none => .error s!"--pbeam expects a number, got '{v}'"
  | a :: _ => .error s!"unrecognized argument '{a}'"

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e =>
    IO.eprintln s!"physlib_gen: {e}"
    pure 1
  | .ok cfg =>
    IO.println s!"physlib_gen: {cfg.nEvents} events, seed {cfg.seed}"
    IO.println s!"  lepton: pdg {cfg.lepton.pdg} at {cfg.lepton.energy} GeV"
    IO.println s!"  hadron: pdg {cfg.hadron.pdg} at {cfg.hadron.energy} GeV"
    IO.println s!"  s = {cfg.sHat} GeV^2, sqrt(s) = {cfg.roots} GeV"
    let events ← trivialRun cfg
    if events.length != cfg.nEvents then
      IO.eprintln s!"physlib_gen: built {events.length} of {cfg.nEvents} events"
      pure 1
    else
      HepMC3.Ascii.writeFile cfg.output cfg.runInfo events
      IO.println s!"  wrote {events.length} events to {cfg.output}"
      pure 0
