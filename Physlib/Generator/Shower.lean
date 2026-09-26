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

Virtuality-ordered `q → q g` evolution by the veto algorithm, from the hard scale down to a
fixed cutoff.

## What this implements, and what it does not

Only `q → q g`.  Emitted gluons do not branch further: there is no `g → gg` or `g → qq̄`, so
this is a single evolving quark line radiating gluons, not a full cascade.  The other three
kernels exist in `Physlib.Generator.Splitting` and are unused here.  Also absent: angular
ordering or any other coherence treatment, spin correlations, and the matching to the
one-emission matrix element that fixes the hardest emission.  Each of those changes real
distributions, so nothing here should be compared to a tuned generator and read as agreement
or disagreement about physics.

## The veto loop, and its relation to the proof

`Physlib.QFT.Shower.Sudakov` proves `vetoSeries_eq_exp_neg`: summed over rejection count,
the veto chain gives exactly the Sudakov factor of the *true* kernel, with the overestimate
cancelling identically.  `vetoDensity_eq` restates it as the emission density being
`K t · Δ_K t` with the overestimate absent.

`evolveQuark` below is the algorithm that theorem is about, and the correspondence is
one-to-one in one direction only: the theorem says *if* you sample the next scale from the
overestimate's Sudakov and accept with the ratio, *then* the result is distributed by the
true kernel.  It does **not** certify this code — the gap named in the plan's Phase 2, that
the algorithm's output law equals the series, needs a symmetrization lemma mathlib does not
have.  What the theorem does buy is that the acceptance rule below is not a heuristic to be
tuned: it is pinned, and getting it wrong is a bug rather than a modelling choice.

The one line that carries the whole argument is the rejection branch: on a failed acceptance
test the loop continues **from the rejected scale**, not from the original one.  Restarting
from the original would resample the overestimate's distribution instead of the true one.

## Momentum: what is conserved exactly and what is not

Each splitting conserves **energy exactly** and three-momentum only to the accuracy of the
collinear approximation.  Given a massless parent of energy `E` along `n̂`, the daughters get
energies `zE` and `(1-z)E` and directions tilted by `±k_T` with `|k_T|² = z(1-z)t`, each then
normalized so that `|p| = E` and every parton stays exactly massless and on shell.

The alternative — conserving three-momentum exactly by keeping `p_q + p_g = p` — forces the
daughters' energies to sum to *more* than the parent's, since two massless momenta at an
angle have more energy than their massless sum.  The remnant would then have to supply
negative energy.  Conserving energy and letting a small three-momentum imbalance accumulate
is the direction that stays physical.

The imbalance is absorbed by the beam remnant, exactly as Phase 1 already defines the remnant
by subtraction, so the **event as a whole conserves four-momentum identically** whatever the
shower does.  That is bookkeeping, not physics: it means a conservation check on the final
event cannot detect a shower kinematics bug, which is why `showerQuark` reports the imbalance
it generated rather than hiding it.
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
  /-- `z` is sampled on `[z0, 1 - z0]`.  A crude stand-in for the `k_T`-derived limits: the
  physical bound depends on the scale, this does not. -/
  z0 : Float := 0.01
  /-- Maximum veto-loop iterations per quark, counting rejections.  Exhaustion is reported,
  never silently truncated. -/
  fuel : Nat := 10000
deriving Repr, Inhabited

/-- What one shower produced. -/
structure ShowerResult where
  /-- The quark after all emissions. -/
  quark : FourMom
  /-- Emitted gluons, hardest first in emission order (decreasing scale). -/
  gluons : List FourMom
  /-- Veto-loop iterations consumed, accepted and rejected together.  With the acceptance
  probability this is the efficiency the overestimate cost. -/
  trials : Nat := 0
  /-- True if the loop ran out of fuel before reaching the cutoff.  The event is then
  incompletely showered and should not be used. -/
  exhausted : Bool := false
deriving Repr, Inhabited

/-- Euclidean length of the three-momentum. -/
def FourMom.p3 (a : FourMom) : Float :=
  (a.px * a.px + a.py * a.py + a.pz * a.pz).sqrt

/-- A unit vector perpendicular to `(nx, ny, nz)`, which must be non-zero.

Built by projecting out whichever axis is least aligned with the input, so the subtraction
never cancels to nothing. -/
def perpUnit (nx ny nz : Float) : Float × Float × Float :=
  let (ax, ay, az) := if nz.abs < 0.9 then (0.0, 0.0, 1.0) else (1.0, 0.0, 0.0)
  let d := ax * nx + ay * ny + az * nz
  let (vx, vy, vz) := (ax - d * nx, ay - d * ny, az - d * nz)
  let n := (vx * vx + vy * vy + vz * vz).sqrt
  if n <= 0.0 then (1.0, 0.0, 0.0) else (vx / n, vy / n, vz / n)

/-- Split a massless parton of energy `E` along its own direction into a quark carrying
energy fraction `z` and a gluon carrying `1 - z`, with transverse momentum
`|k_T| = √(z(1-z)t)` at azimuth `φ`.

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
    let eq := z * e
    let eg := (1.0 - z) * e
    -- tilt each daughter by ±k_T, then rescale to keep it massless at its assigned energy
    let dirq := (eq * nx + cx, eq * ny + cy, eq * nz + cz)
    let dirg := (eg * nx - cx, eg * ny - cy, eg * nz - cz)
    let nq := (dirq.1 * dirq.1 + dirq.2.1 * dirq.2.1 + dirq.2.2 * dirq.2.2).sqrt
    let ng := (dirg.1 * dirg.1 + dirg.2.1 * dirg.2.1 + dirg.2.2 * dirg.2.2).sqrt
    let q : FourMom :=
      if nq <= 0.0 then { px := 0.0, py := 0.0, pz := 0.0, e := eq }
      else { px := eq * dirq.1 / nq, py := eq * dirq.2.1 / nq, pz := eq * dirq.2.2 / nq, e := eq }
    let g : FourMom :=
      if ng <= 0.0 then { px := 0.0, py := 0.0, pz := 0.0, e := eg }
      else { px := eg * dirg.1 / ng, py := eg * dirg.2.1 / ng, pz := eg * dirg.2.2 / ng, e := eg }
    (q, g)

/-- Draw the next virtuality from the overestimate's Sudakov factor.

With the coupling frozen at its overestimate `α̂` and the `z` integral `Î` done in closed
form, `Δ̂(t) = exp(-(α̂/2π) Î ln(t_max/t))`, so solving `Δ̂(t) = r` gives
`t = t_max · r^{2π/(α̂ Î)}`.  This is the step that needs the overestimate to be invertible,
and the only reason it is allowed to be crude. -/
def nextScale (tPrev aHat iHat r : Float) : Float :=
  let c := 2.0 * 3.141592653589793 / (aHat * iHat)
  tPrev * (r.pow c)

/-- Evolve one massless quark from `tMax` down to the cutoff, emitting gluons.

The veto loop: sample the next scale from the overestimate's Sudakov, sample `z` from the
overestimate in `z`, accept with the product of the two ratios, and **on rejection continue
from the rejected scale** — the line the correctness argument turns on. -/
def evolveQuark {g : Type} [RandomGen g] [Monad m]
    (cfg : ShowerConfig) (q0 : FourMom) (tMax : Float) :
    RandGT g m ShowerResult := do
  let aHat := alphaS cfg.tCut
  let iHat := pQQOverIntegral cfg.z0
  if aHat <= 0.0 || iHat <= 0.0 then
    pure { quark := q0, gluons := [], trials := 0 }
  else
    let rec go (fuel : Nat) (t : Float) (q : FourMom) (acc : List FourMom) (used : Nat) :
        RandGT g m ShowerResult := do
      match fuel with
      | 0 => pure { quark := q, gluons := acc.reverse, trials := used, exhausted := true }
      | k + 1 => do
        let r ← uniform01
        let tNew := nextScale t aHat iHat r
        if tNew <= cfg.tCut then
          pure { quark := q, gluons := acc.reverse, trials := used + 1 }
        else do
          let rz ← uniform01
          let z := pQQOverSample cfg.z0 rz
          let ra ← uniform01
          let w := pQQAccept z * alphaS tNew / aHat
          if ra < w then do
            let rp ← uniform01
            let phi := 6.283185307179586 * rp
            let (qNew, gNew) := splitOnce q z tNew phi
            go k tNew qNew (gNew :: acc) (used + 1)
          else
            -- vetoed: continue from `tNew`, not from `t`
            go k tNew q acc (used + 1)
    go cfg.fuel tMax q0 [] 0

end Generator
end Physlib
