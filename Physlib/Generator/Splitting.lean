/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Generator.Kinematics

/-!
# DGLAP splitting kernels and the running coupling, in `Float`

The unregularized leading-order splitting functions, a one-loop `α_s`, and the overestimates
the veto algorithm needs.

## Relation to the rest of the library

`Physlib.QFT.Factorization.Evolution.Basic` has `SplittingKernel` as an *abstract*
`Flavor → Flavor → ℝ → ℝ → ℝ`; no concrete kernel exists anywhere in the specification
layer, so these are new definitions rather than transcriptions of existing ones.

The colour factors are not new, though, and are not guessed:

| constant | value | proved as |
|---|---|---|
| `cF` | `4/3` | `Physlib.QFT.QCD.RepresentationColor.su3FundamentalStatement` |
| `cA` | `3` | `...su3AdjointStatement` |
| `tR` | `1/2` | `...su3TraceStatement` |

Those are theorems about su(3) in this library, proved for general `N` and specialized.
The `Float` literals below are transcriptions of them and carry no proof, as everywhere in
this layer, but at least the numbers have a derivation behind them rather than a textbook.

## Why the overestimates are here

The veto algorithm needs, for the kernel it samples, an overestimate that is integrable and
invertible in closed form.  `Physlib.QFT.Shower.Sudakov.vetoSeries_eq_exp_neg` proves that
using one introduces **no bias** — the overestimate cancels identically, surviving only in
the efficiency — which is exactly the licence to pick something as crude as
`2 C_F / (1 - z)` because it inverts, rather than something tight.

Two separate overestimates are used by the sampler, and both need to dominate:

* in `z`, `P_qq(z) ≤ 2 C_F / (1 - z)`, since `1 + z² ≤ 2` on `[0,1]`;
* in the scale, `α_s(t) ≤ α_s(t_min)` for `t ≥ t_min`, since the one-loop coupling falls
  with scale.

Sampling the product analytically and accepting with the ratio of each is a textbook use of
the veto algorithm and the reason the theorem was worth proving first.
-/

@[expose] public section

namespace Physlib
namespace Generator

/-- The fundamental Casimir `C_F = 4/3`, transcribing `su3FundamentalStatement`. -/
def cF : Float := 4.0 / 3.0

/-- The adjoint Casimir `C_A = 3`, transcribing `su3AdjointStatement`. -/
def cA : Float := 3.0

/-- The trace normalization `T_R = 1/2`, transcribing `su3TraceStatement`. -/
def tR : Float := 0.5

/-- Number of active flavours, held fixed.

A real generator runs this with thresholds at the quark masses; holding it at five is a
simplification of the same kind as the toy `F₂`, and is wrong below the bottom threshold. -/
def nFlavour : Float := 5.0

/-- The measured strong coupling at the `Z` mass, the anchor everything else is fixed from.
PDG value. -/
def alphaSMZ : Float := 0.118

/-- The `Z` mass in GeV, used only as the scale at which `alphaSMZ` is quoted. -/
def mZ : Float := 91.1876

/-- One-loop `β₀`, in the normalization where `α_s(t) = 1 / (β₀ ln(t/Λ²))`. -/
def beta0 : Float := (33.0 - 2.0 * nFlavour) / (12.0 * 3.141592653589793)

/-- The QCD scale `Λ` in GeV, **derived** from the anchor rather than tabulated:
inverting `α_s(m_Z²) = 1/(β₀ ln(m_Z²/Λ²))` gives `Λ = m_Z exp(-1/(2 β₀ α_s(m_Z²)))`.

Deriving it is the point.  A literal here would be a second place for the calibration to
live, and a claim about `α_s(m_Z²)` in this docstring could then drift away from what the
code computes — which is exactly what happened in the first version of this file, where a
tabulated `Λ = 0.21` sat under a comment claiming it gave `0.118`.  It does not: at one
loop with five flavours, `Λ = 0.21` gives `α_s(m_Z²) ≈ 0.135`.

The two numbers are both "right" and answer different questions. `Λ^(5) ≈ 0.21 GeV` is the
conventional MS-bar value, but it reproduces `α_s(m_Z²) = 0.118` only with *higher-order*
running; forced through the one-loop formula it overshoots by 14%.  Matching the measured
coupling at one loop instead needs `Λ ≈ 0.088 GeV`, which is what this expression evaluates
to.  Since the shower uses `α_s` at scales of order 1–100 GeV² rather than at `m_Z`, and the
one-loop form is wrong there anyway, anchoring to the measured coupling is the less
arbitrary of the two — but it does mean this `Λ` should not be compared with a tabulated
one. -/
def lambdaQCD : Float := mZ * (-1.0 / (2.0 * beta0 * alphaSMZ)).exp

/-- The one-loop running coupling at scale `t = μ²` in GeV².

Returns `0` at or below the Landau pole rather than a negative or infinite value: the
sampler compares against it, and a negative coupling would silently invert an acceptance
test.  Callers should keep their cutoff well above `Λ²`; `showerCutoff` does. -/
def alphaS (t : Float) : Float :=
  let l := t / (lambdaQCD * lambdaQCD)
  if l <= 1.0 then 0.0 else 1.0 / (beta0 * l.log)

/-- `P_qq(z) = C_F (1 + z²)/(1 - z)`, the quark-to-quark kernel, unregularized.

The `z → 1` pole is the soft-gluon singularity.  It is not regularized here because the
shower never reaches it: the sampler cuts `z` away from both endpoints, which is a physical
cutoff standing in for the hadronization scale rather than a plus-distribution. -/
def pQQ (z : Float) : Float := cF * (1.0 + z * z) / (1.0 - z)

/-- `P_gq(z) = C_F (1 + (1-z)²)/z`, the quark-to-gluon kernel (gluon takes `z`). -/
def pGQ (z : Float) : Float := cF * (1.0 + (1.0 - z) * (1.0 - z)) / z

/-- `P_qg(z) = T_R (z² + (1-z)²)`, gluon splitting to a quark pair.  Finite on `[0,1]`. -/
def pQG (z : Float) : Float := tR * (z * z + (1.0 - z) * (1.0 - z))

/-- `P_gg(z) = 2 C_A [z/(1-z) + (1-z)/z + z(1-z)]`, gluon to two gluons. -/
def pGG (z : Float) : Float :=
  2.0 * cA * (z / (1.0 - z) + (1.0 - z) / z + z * (1.0 - z))

/-- The overestimate of `P_qq` used by the veto sampler: `2 C_F / (1 - z)`.

Dominates because `1 + z² ≤ 2` for `z ∈ [0,1]`, with the ratio `(1 + z²)/2` as the
acceptance probability. -/
def pQQOver (z : Float) : Float := 2.0 * cF / (1.0 - z)

/-- `∫ pQQOver` over `[z₀, 1 - z₀]`, in closed form: `2 C_F ln((1 - z₀)/z₀)`. -/
def pQQOverIntegral (z0 : Float) : Float := 2.0 * cF * ((1.0 - z0) / z0).log

/-- Sample `z` from `pQQOver` on `[z₀, 1 - z₀]` given a uniform `r ∈ [0,1)`.

Inverting `∫_{z₀}^{z} 2C_F/(1-z') dz'` against a uniform fraction of the total gives
`1 - z = (1 - z₀) (z₀/(1 - z₀))^r`, which is where the closed-form invertibility that makes
the overestimate worth using actually shows up. -/
def pQQOverSample (z0 r : Float) : Float :=
  1.0 - (1.0 - z0) * ((z0 / (1.0 - z0)).pow r)

/-- The acceptance probability for the `z` overestimate: `P_qq(z) / pQQOver(z) = (1 + z²)/2`.

Lies in `[1/2, 1]` on `[0,1]`, so the `z` overestimate alone is never worse than a factor
two in efficiency — the coupling overestimate is the expensive one. -/
def pQQAccept (z : Float) : Float := (1.0 + z * z) / 2.0

end Generator
end Physlib
