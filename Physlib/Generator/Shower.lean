/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Generator.Splitting
public import Physlib.Numerics.Random

/-!
# A final-state parton shower off the struck quark

Virtuality-ordered evolution by the veto algorithm, with `q → qg`, `g → gg` and `g → qq̄`,
from the hard scale down to a fixed cutoff.

## What this implements, and what it does not

All three final-state channels branch, so emitted gluons are themselves evolved and the
result is a cascade rather than a single radiating line.  Still absent, and each changes
real distributions: angular ordering or any other coherence treatment, spin correlations,
and matching to the one-emission matrix element that fixes the hardest emission.  Nothing
here should be compared to a tuned generator and read as agreement or disagreement about
physics.

Initial-state (backward) evolution is not here either, and is a separate phase: it has to
be done against the PDF, which this generator does not yet have.

## The veto loop, and its relation to the proof

`Physlib.QFT.Shower.Sudakov` proves `vetoSeries_eq_exp_neg`: summed over rejection count,
the veto chain gives exactly the Sudakov factor of the *true* kernel, the overestimate
cancelling identically.  `vetoDensity_eq` restates it as the emission density being
`K t · Δ_K t`, with the overestimate absent.

`cascade` below is the algorithm that theorem is about.  The correspondence runs one way
only: the theorem says *if* you draw the next scale from the overestimate's Sudakov and
accept with the ratio, *then* the result is distributed by the true kernel.  It does not
certify this code — the gap named in the plan's Phase 2, that the algorithm's output law
equals the series, needs a symmetrization lemma mathlib does not have.  What it does buy is
that the acceptance rule is pinned rather than tunable: getting it wrong is a bug.

The line carrying the whole argument is the rejection branch, which continues **from the
rejected scale**.  Restarting from the original scale would sample the overestimate's
distribution instead of the true one.

For a gluon the overestimate is a sum over two channels.  The scale is drawn from the
*combined* integral and the channel chosen afterwards in proportion to its share, which is
the multi-channel form of the same argument: the combined overestimate dominates the
combined kernel, so the veto identity applies to the sum.

## Momentum: what is conserved exactly and what is not

Each splitting conserves **energy exactly** and three-momentum only to collinear accuracy.
Given a massless parent of energy `E` along `n̂`, the daughters take energies `zE` and
`(1-z)E` with directions tilted by `±k_T`, `|k_T|² = z(1-z)t`, each renormalized so that
`|p| = E` and every parton stays exactly massless.

Conserving three-momentum instead is not available: two massless momenta at an angle carry
more energy than their massless sum, so `p_q + p_g = p` would force the daughters' energies
above the parent's and the remnant would have to supply negative energy.

The imbalance is absorbed by the beam remnant, which Phase 1 already defines by subtraction,
so the **event** conserves four-momentum identically whatever the shower does.  That is
bookkeeping rather than physics: a conservation check on the final event cannot detect a
shower kinematics bug, which is why the imbalance is reported and written out rather than
left implicit.
-/

@[expose] public section

namespace Physlib
namespace Generator

open Physlib.Numerics

/-- Shower parameters. -/
structure ShowerConfig where
  /-- Evolution stops below this virtuality, in GeV².  Stands in for the hadronization
  scale; the shower has no meaning below it. -/
  tCut : Float := 1.0
  /-- The overestimate samples `z` on `[z0, 1 - z0]`.  A floor that keeps the overestimate's
  integral finite, **not** the physical limit: that is the transverse-momentum cutoff in
  `resolvable`, which depends on the scale and is what regulates the shower. -/
  z0 : Float := 0.01
  /-- Maximum veto-loop iterations for the whole cascade, rejections included.  Shared
  across every parton in the event, so one runaway line cannot be hidden by short ones.
  Exhaustion is reported, never silently truncated. -/
  fuel : Nat := 100000
deriving Repr, Inhabited

/-- A parton waiting to be evolved: its momentum, its identity, and the scale it was
produced at, which is where its own evolution starts. -/
structure ShowerParton where
  /-- Four-momentum, massless. -/
  mom : FourMom
  /-- PDG code: `21` for a gluon, `±1..±5` for a quark or antiquark. -/
  pdg : Int
  /-- Production scale in GeV²; evolution runs downward from here. -/
  tStart : Float
deriving Repr, Inhabited

/-- What one shower produced. -/
structure ShowerResult where
  /-- Final partons, each with its PDG code.  Order is the order they left the cascade and
  carries no physical meaning. -/
  partons : List (FourMom × Int) := []
  /-- Veto-loop iterations consumed across the whole cascade, accepted and rejected
  together.  With the acceptance probability this is what the overestimates cost. -/
  trials : Nat := 0
  /-- True if the cascade ran out of fuel with partons still unevolved.  Such an event never
  reached the cutoff, so it is incompletely evolved and must not be used. -/
  exhausted : Bool := false
deriving Repr, Inhabited

/-- A unit vector perpendicular to `(nx, ny, nz)`, which must be non-zero.

Built by projecting out whichever axis is least aligned with the input, so the subtraction
never cancels to nothing. -/
def perpUnit (nx ny nz : Float) : Float × Float × Float :=
  let (ax, ay, az) := if nz.abs < 0.9 then (0.0, 0.0, 1.0) else (1.0, 0.0, 0.0)
  let d := ax * nx + ay * ny + az * nz
  let (vx, vy, vz) := (ax - d * nx, ay - d * ny, az - d * nz)
  let n := (vx * vx + vy * vy + vz * vz).sqrt
  if n <= 0.0 then (1.0, 0.0, 0.0) else (vx / n, vy / n, vz / n)

/-- Split a massless parton of energy `E` into daughters carrying energy fractions `z` and
`1 - z`, with transverse momentum `|k_T| = √(z(1-z)t)` at azimuth `φ`.

Both daughters come back exactly massless.  Energy is exactly conserved; three-momentum is
not (module docstring). -/
def splitOnce (p : FourMom) (z t phi : Float) : FourMom × FourMom :=
  let e := p.e
  let pmag := p.p3
  if pmag <= 0.0 || e <= 0.0 then (p, { px := 0.0, py := 0.0, pz := 0.0, e := 0.0 })
  else
    let (nx, ny, nz) := (p.px / pmag, p.py / pmag, p.pz / pmag)
    let (ux, uy, uz) := perpUnit nx ny nz
    -- second transverse axis: n̂ × û, already unit since both are unit and orthogonal
    let (wx, wy, wz) := (ny * uz - nz * uy, nz * ux - nx * uz, nx * uy - ny * ux)
    let kt := (z * (1.0 - z) * t).sqrt
    let (cx, cy, cz) :=
      (kt * (phi.cos * ux + phi.sin * wx),
       kt * (phi.cos * uy + phi.sin * wy),
       kt * (phi.cos * uz + phi.sin * wz))
    let e1 := z * e
    let e2 := (1.0 - z) * e
    let d1 := (e1 * nx + cx, e1 * ny + cy, e1 * nz + cz)
    let d2 := (e2 * nx - cx, e2 * ny - cy, e2 * nz - cz)
    let n1 := (d1.1 * d1.1 + d1.2.1 * d1.2.1 + d1.2.2 * d1.2.2).sqrt
    let n2 := (d2.1 * d2.1 + d2.2.1 * d2.2.1 + d2.2.2 * d2.2.2).sqrt
    let a : FourMom :=
      if n1 <= 0.0 then { px := 0.0, py := 0.0, pz := 0.0, e := e1 }
      else { px := e1 * d1.1 / n1, py := e1 * d1.2.1 / n1, pz := e1 * d1.2.2 / n1, e := e1 }
    let b : FourMom :=
      if n2 <= 0.0 then { px := 0.0, py := 0.0, pz := 0.0, e := e2 }
      else { px := e2 * d2.1 / n2, py := e2 * d2.2.1 / n2, pz := e2 * d2.2.2 / n2, e := e2 }
    (a, b)

/-- Whether a splitting at momentum fraction `z` and virtuality `t` is resolvable, i.e. whether
its transverse momentum `k_T² = z(1-z)t` clears the cutoff.

**This is the shower's actual regulator; the `z₀` window is only a floor.**  A fixed `z` cut
does not regulate the soft divergence.  With `z ∈ [0.01, 0.99]` held fixed at every scale, a
gluon's integrated branching probability stays large all the way down to the cutoff: the mean
number of branchings per gluon is 5 to 8 over the range this generator uses, so the cascade is
a *supercritical* branching process and does not terminate.  That was measured, not predicted —
the first cascade implementation consumed its entire fuel budget on every event and the run
produced no events at all.

Requiring `z(1-z)t > t_cut` shrinks the `z` window as `t` falls and closes it completely below
`t = 4 t_cut`, where `z(1-z) ≤ 1/4` can no longer clear the cutoff.  That is what makes the
process terminate: a daughter produced near the cutoff has a vanishing branching probability
rather than a finite one.  The reproduction ratio drops to 0.4 at `t = 10 t_cut`, and although
it exceeds one again at large `t`, each generation starts lower than its parent, so the
multiplicity is finite.

Implemented as a veto rather than by sampling the shrunken window.  The overestimate still
covers all of `[z₀, 1-z₀]` and the true kernel is zero outside the resolvable region, so the
overestimate still dominates and the veto identity still applies — the same argument as for
the two ratio factors, with an indicator as a third factor. -/
def resolvable (cfg : ShowerConfig) (z t : Float) : Bool := z * (1.0 - z) * t > cfg.tCut

/-- Draw the next virtuality from the overestimate's Sudakov factor.

With the coupling frozen at its overestimate `α̂` and the `z` integral `Î` in closed form,
`Δ̂(t) = exp(-(α̂/2π) Î ln(t_prev/t))`, so solving `Δ̂(t) = r` gives
`t = t_prev · r^{2π/(α̂ Î)}`.  This is the step that needs the overestimate to be
invertible, and the only reason it is allowed to be crude. -/
def nextScale (tPrev aHat iHat r : Float) : Float :=
  let c := 2.0 * 3.141592653589793 / (aHat * iHat)
  tPrev * (r.pow c)

/-- Map a uniform draw onto one of the five active flavours, as `(quark, antiquark)` PDG
codes.  Flavour is chosen only after `g → qq̄` is accepted, which is why the overestimate
carries the factor `n_f`. -/
def pickFlavour (r : Float) : Int × Int :=
  let i := (r * nFlavour).floor
  let f : Int := if i < 1.0 then 1 else if i < 2.0 then 2 else if i < 3.0 then 3
                 else if i < 4.0 then 4 else 5
  (f, -f)

/-- Evolve a whole cascade: pop a parton, take one veto step on it, and recurse.

`fuel` counts veto steps across every parton in the event, so the recursion is structural
and one runaway line cannot hide behind short ones.  A parton whose next scale falls below
the cutoff is finished and moves to the output; an accepted branching replaces it with the
continuing daughter and pushes the sibling; a rejected one puts it back at the rejected
scale. -/
def cascade {g : Type} [RandomGen g] [Monad m] (cfg : ShowerConfig) :
    Nat → List ShowerParton → List (FourMom × Int) → Nat →
    RandGT g m (List (FourMom × Int) × Nat × Bool)
  | 0, queue, acc, used =>
    -- out of fuel with work left: report it, and hand back what exists so the caller can
    -- see the event rather than an empty one
    pure (acc ++ queue.map (fun q => (q.mom, q.pdg)), used, true)
  | _ + 1, [], acc, used => pure (acc, used, false)
  | k + 1, p :: rest, acc, used => do
    let aHat := alphaS cfg.tCut
    let isG := p.pdg == 21
    let iHat := if isG then gluonOverIntegral cfg.z0 else pQQOverIntegral cfg.z0
    if aHat <= 0.0 || iHat <= 0.0 then
      cascade cfg k rest ((p.mom, p.pdg) :: acc) (used + 1)
    else do
      let r ← uniform01
      let tNew := nextScale p.tStart aHat iHat r
      if tNew <= cfg.tCut then
        cascade cfg k rest ((p.mom, p.pdg) :: acc) (used + 1)
      else do
        let rz ← uniform01
        let ra ← uniform01
        let coupling := alphaS tNew / aHat
        if isG then do
          -- choose channel in proportion to its share of the combined overestimate
          let rc ← uniform01
          let gg := pGGOverIntegral cfg.z0
          let toGG := rc * gluonOverIntegral cfg.z0 < gg
          let rb ← uniform01
          let z := if toGG then pGGOverSample cfg.z0 rz (rb < 0.5)
                   else cfg.z0 + rz * (1.0 - 2.0 * cfg.z0)
          let w := (if toGG then pGGAccept z else pQGAccept z) * coupling
          if resolvable cfg z tNew && ra < w then do
            let rp ← uniform01
            -- a fresh variate for the flavour: reusing the `z` draw would tie which quark
            -- pair is made to how the momentum was shared between them
            let rf ← uniform01
            let (d1, d2) := splitOnce p.mom z tNew (6.283185307179586 * rp)
            let (pdg1, pdg2) : Int × Int := if toGG then (21, 21) else pickFlavour rf
            cascade cfg k
              ({ mom := d1, pdg := pdg1, tStart := tNew } ::
               { mom := d2, pdg := pdg2, tStart := tNew } :: rest) acc (used + 1)
          else
            cascade cfg k ({ p with tStart := tNew } :: rest) acc (used + 1)
        else do
          let z := pQQOverSample cfg.z0 rz
          if resolvable cfg z tNew && ra < pQQAccept z * coupling then do
            let rp ← uniform01
            let (dq, dg) := splitOnce p.mom z tNew (6.283185307179586 * rp)
            cascade cfg k
              ({ mom := dq, pdg := p.pdg, tStart := tNew } ::
               { mom := dg, pdg := 21, tStart := tNew } :: rest) acc (used + 1)
          else
            cascade cfg k ({ p with tStart := tNew } :: rest) acc (used + 1)

/-- Evolve one massless quark from `tMax` down to the cutoff, showering everything it
produces. -/
def evolveQuark {g : Type} [RandomGen g] [Monad m]
    (cfg : ShowerConfig) (q0 : FourMom) (pdg : Int) (tMax : Float) :
    RandGT g m ShowerResult := do
  let (parts, used, exh) ←
    cascade cfg cfg.fuel [{ mom := q0, pdg := pdg, tStart := tMax }] [] 0
  pure { partons := parts, trials := used, exhausted := exh }

end Generator
end Physlib
