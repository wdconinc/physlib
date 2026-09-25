/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Generator.Kinematics

/-!
# The leading-order cross section, in `Float`

An executable transcription of `Physlib.QFT.Scattering.DIS.loNCdSigma`, together with a toy
parton density to evaluate it with.

## What is proved, and where

Nothing here.  The positivity of the cross section, the Callan–Gross reduction and the
identity with the conventional `1 + (1-y)²` form are theorems, and they live at the `ℝ` level
in `Physlib.QFT.Scattering.DIS.CrossSection`.  This file repeats those definitions in `Float`
so they can be evaluated; the correspondence is by inspection.

## The toy parton density is a toy

`f2Toy` is **not a fitted parton distribution**.  It is a valence-plus-sea shape with
round-number coefficients, no scale dependence at all (no DGLAP evolution, so `F₂` is
independent of `Q²`), no momentum sum rule imposed, and no uncertainty.  It exists so the
sampler has a non-trivial positive function to sample, and so the machinery can be tested
against an analytic answer.  **Any physics conclusion drawn from it would be wrong.**
Replacing it with a real PDF set is Phase 4 of the plan.

Flavour content is `u, d, s` with their antiquarks, charges `+2/3, -1/3, -1/3`; `c, b, t` are
omitted, which at `√s = 60 GeV` is a real omission for charm.
-/

@[expose] public section

namespace Physlib
namespace Generator

/-- The electromagnetic coupling at low scale.  Running is not implemented. -/
def alphaEM : Float := 1.0 / 137.035999084

/-- Valence-like shape `A xᵃ (1-x)ᵇ`, the `betaShape` of the library's PDF module in `Float`. -/
def betaShape (a b x : Float) : Float := x.pow a * (1.0 - x).pow b

/-- Toy up-valence density `u_v(x)`, normalised to roughly two valence quarks. -/
def uValence (x : Float) : Float := 2.6 * betaShape 0.5 3.0 x / x

/-- Toy down-valence density `d_v(x)`, normalised to roughly one valence quark. -/
def dValence (x : Float) : Float := 1.3 * betaShape 0.5 4.0 x / x

/-- Toy sea density, the same for each of `ū, d̄, s, s̄`. -/
def seaDensity (x : Float) : Float := 0.25 * betaShape (-0.2) 8.0 x / x

/-- Toy `F₂(x)` at leading order, `x ∑_f e_f² (f + f̄)`, with no `Q²` dependence.

The `Q²` argument is accepted and ignored, so that the signature is already the one a real,
scale-dependent parton density will need. -/
def f2Toy (x : Float) (_q2 : Float) : Float :=
  let eu2 := 4.0 / 9.0
  let ed2 := 1.0 / 9.0
  let sea := seaDensity x
  -- u + ū = u_v + sea, d + d̄ = d_v + sea, s + s̄ = 2 sea
  x * (eu2 * (uValence x + 2.0 * sea) + ed2 * (dValence x + 2.0 * sea) + ed2 * (2.0 * sea))

/-- The inelasticity factor `1 - y + y²/2`, transcribing `DIS.yFactor`.

Bounded below by `1/2` and above by `1` on `y ∈ [0,1]`; the `ℝ`-level `yFactor_ge_half` proves
the lower bound, and the sampler's overestimate relies on the upper one. -/
def yFactor (y : Float) : Float := 1.0 - y + y * y / 2.0

/-- `d²σ/(dx dQ²)` at leading order, transcribing `DIS.loNCdSigma`.

Units are natural: `α` dimensionless, `Q²` in GeV², the result in GeV⁻⁴ up to the overall
conversion that a total cross section in picobarns would need. -/
def dSigmaDxDQ2 (x q2v y : Float) : Float :=
  4.0 * 3.141592653589793 * alphaEM * alphaEM / (x * q2v * q2v) * f2Toy x q2v * yFactor y

end Generator
end Physlib
