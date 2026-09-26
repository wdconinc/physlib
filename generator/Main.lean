/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
import Physlib.Generator.DISEvent
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
           [--q2min Q] [--trivial]
```

By default this generates leading-order neutral-current DIS events.  `--trivial` selects the
Phase 0 placeholder instead — kinematically meaningless, but it keeps the pipeline-only path
under test independently of the physics.
-/

open Physlib Physlib.Generator

/-- Parse a decimal number for the physical quantities.

`toNat?` was used here originally, which silently made `--ebeam 18.5` an error reported as
"expects a number" — accurate about the intent and misleading about the behaviour, since
only naturals were accepted. Beam energies and `Q²` cuts are genuinely real-valued. -/
def parseFloat? (s : String) : Option Float :=
  match s.splitOn "." with
  | [w] => w.toNat?.map Nat.toFloat
  | [w, f] => do
    let wn ← w.toNat?
    let fn ← f.toNat?
    let scale := (10 : Nat) ^ f.length
    pure (wn.toFloat + fn.toFloat / scale.toFloat)
  | _ => none

/-- Parse the command line into a `RunConfig`, starting from the defaults.

Unrecognized arguments are reported rather than ignored, so a mistyped flag fails loudly
instead of silently generating a differently-configured run.  Flags that take a value
report a *missing value* distinctly from an unrecognized flag: `--seed` at the end of the
line is a different mistake from `--sed 7`, and conflating them made the first one hard to
read. -/
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
    match parseFloat? v with
    | some e => parseArgs rest { c with lepton := electronBeam e }
    | none => .error s!"--ebeam expects a decimal number in GeV, got '{v}'"
  | "--pbeam" :: v :: rest =>
    match parseFloat? v with
    | some e => parseArgs rest { c with hadron := protonBeam e }
    | none => .error s!"--pbeam expects a decimal number in GeV, got '{v}'"
  | "--q2min" :: v :: rest =>
    match parseFloat? v with
    | some q => parseArgs rest { c with q2Min := q }
    | none => .error s!"--q2min expects a decimal number in GeV^2, got '{v}'"
  | "--trivial" :: rest => parseArgs rest c
  | a :: [] =>
    if a == "--events" || a == "--seed" || a == "--output" || a == "--ebeam"
       || a == "--pbeam" || a == "--q2min" then
      .error s!"{a} expects a value, but the command line ends here"
    else .error s!"unrecognized argument '{a}'"
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
    IO.println s!"  s = {cfg.sTotal} GeV^2, sqrt(s) = {cfg.roots} GeV"
    if args.contains "--trivial" then
      let events ← trivialRun cfg
      IO.println s!"  mode: placeholder (no physics)"
      HepMC3.Ascii.writeFile cfg.output cfg.runInfo events
      IO.println s!"  wrote {events.length} events to {cfg.output}"
      pure (if events.length == cfg.nEvents then 0 else 1)
    else
      IO.println s!"  mode: leading-order neutral current, Q2 > {cfg.q2Min} GeV^2"
      let (events, st) ← loRun cfg
      let eff := if st.trials == 0 then 0.0
                 else st.accepted.toFloat / st.trials.toFloat
      IO.println s!"  accepted {st.accepted} of {st.trials} trials (efficiency {eff})"
      if st.exhausted != 0 then
        IO.eprintln s!"physlib_gen: {st.exhausted} event(s) abandoned on rejection fuel"
      if st.violations != 0 then
        IO.eprintln s!"physlib_gen: WEIGHT BOUND VIOLATED on {st.violations} trial(s) -- \
                       the sample is NOT distributed as the target cross section"
        pure 1
      else
        HepMC3.Ascii.writeFile cfg.output cfg.runInfo events
        IO.println s!"  wrote {events.length} events to {cfg.output}"
        pure (if events.length == cfg.nEvents then 0 else 1)
