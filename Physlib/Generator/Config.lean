/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.HepMC3.Basic

/-!
# Run configuration

What a generator run needs to know before it can produce anything: the beams, how many
events, and the seed.  This is the Lean-level record; parsing it from a file comes later,
and nothing here depends on how it was obtained.

Everything is `Float` and executable — this is Layer N.  The beam energies are per-beam
laboratory energies in GeV, and the two beams are taken head-on along `±z`, which is the
only configuration Phase 1 needs.

## On the massless approximation, and on the name

`sTotal` below uses the massless expression `s = 4 E₁ E₂` for head-on beams.  It is named
`sTotal` rather than with a hatted name: by convention `ŝ` is the *partonic* invariant of the
subsystem that actually collides, which for DIS is a fraction `x` of this one.  Phase 1
introduces that quantity, so reserving the hatted name for it avoids a collision that would
be actively misleading.  For the
reference configuration in the plan — 9 GeV electrons on 100 GeV protons — that gives
`s = 3600 GeV²` and `√s = 60 GeV` exactly, which is a useful arithmetic anchor for the first
test.  The exact expression including masses is `s = (E₁+E₂)² - (p₁+p₂)²`; with masses
restored, 9 × 100 GeV gives `√s ≈ 60.0078 GeV`.  The difference is deliberate and the
massless form is what Phase 1 checks against, so it is named here rather than hidden.
-/

@[expose] public section

namespace Physlib
namespace Generator

open HepMC3

/-- Which beam particle, as a PDG identifier plus a mass. -/
structure BeamSpec where
  /-- PDG Monte Carlo identifier; `11` for the electron, `2212` for the proton. -/
  pdg : Int
  /-- Laboratory energy of this beam, in GeV. -/
  energy : Float
  /-- Rest mass in GeV, used for the exact invariants and for the `P` line. -/
  mass : Float := 0.0
deriving Repr, Inhabited

/-- The electron beam of the plan's reference configuration: 9 GeV. -/
def electronBeam (energy : Float := 9.0) : BeamSpec :=
  { pdg := 11, energy := energy, mass := 0.000510998950 }

/-- The proton beam of the plan's reference configuration: 100 GeV. -/
def protonBeam (energy : Float := 100.0) : BeamSpec :=
  { pdg := 2212, energy := energy, mass := 0.93827208816 }

/-- Everything a run needs.  Defaults describe the plan's reference configuration: 9 GeV
electrons on 100 GeV protons, ten events, seed 0. -/
structure RunConfig where
  /-- The beam travelling along `-z`. -/
  lepton : BeamSpec := electronBeam
  /-- The beam travelling along `+z`. -/
  hadron : BeamSpec := protonBeam
  /-- Number of events to generate. -/
  nEvents : Nat := 10
  /-- Seed for `runRandWith`; a run is reproducible from this alone. -/
  seed : Nat := 0
  /-- Output path for the `Asciiv3` file. -/
  output : System.FilePath := "events.hepmc3"
  /-- Lower cut on `Q²` in GeV², applied once the hard process exists. -/
  q2Min : Float := 1.0
deriving Repr, Inhabited

/-- Squared total centre-of-mass energy in the massless head-on approximation, `s = 4 E₁ E₂`.

This is the **hadronic** invariant; the partonic `ŝ` of Phase 1 is a fraction of it.

For the default configuration this is exactly `3600.0`. -/
def RunConfig.sTotal (c : RunConfig) : Float :=
  4.0 * c.lepton.energy * c.hadron.energy

/-- Centre-of-mass energy `√s` in GeV; exactly `60.0` for the default configuration. -/
def RunConfig.roots (c : RunConfig) : Float := c.sTotal.sqrt

/-- Four-momentum of the lepton beam, travelling along `-z`, in the massless approximation. -/
def RunConfig.leptonP (c : RunConfig) : FourVector :=
  { x := 0.0, y := 0.0, z := -c.lepton.energy, t := c.lepton.energy }

/-- Four-momentum of the hadron beam, travelling along `+z`, in the massless
approximation. -/
def RunConfig.hadronP (c : RunConfig) : FourVector :=
  { x := 0.0, y := 0.0, z := c.hadron.energy, t := c.hadron.energy }

/-- The run header written into the output file. -/
def RunConfig.runInfo (_c : RunConfig) : GenRunInfo :=
  { tools := [{ name := "physlib", version := "0.1",
                description := "DIS event generator in Lean 4" }],
    weightNames := ["Default"] }

end Generator
end Physlib
