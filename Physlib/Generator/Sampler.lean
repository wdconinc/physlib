/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Generator.CrossSection
public import Physlib.Numerics.Random

/-!
# Sampling `(x, Q²)` from the leading-order cross section

Acceptance–rejection in the variables `(ln x, ln Q²)`.

## Why logarithmic variables

The target `d²σ/(dx dQ²) ∝ F₂(x) · Y(y) / (x Q⁴)` is steeply peaked: it diverges as `x → 0`
and as `Q² → 0`.  Sampling `x` and `Q²` uniformly would put almost every trial where the
integrand is negligible and accept almost nothing.  Proposing *flat in `ln x` and flat in
`ln Q²`* means the proposal density carries a factor `1/(x Q²)`, and the acceptance weight is
the ratio

  `w(x, Q²) = target / proposal ∝ F₂(x) · Y(y) / Q²`,

which is bounded rather than divergent.  The `1/x` has cancelled exactly, and what remains
falls monotonically in `Q²`.

## The bound, and an honest note about it

With `y ∈ [0,1]` we have `Y(y) ≤ 1`, and `Q² ≥ Q²_min` over the sampled region, so

  `w ≤ F₂^max / Q²_min`.

`Y(y) ≤ 1` is exact.  **`F₂^max` is not obtained analytically.** The generator plan asks for
an *analytic* overestimate; for this toy `F₂` the maximum over the sampled `x` range is found
by a grid scan with a safety factor, which is a numerical bound, and that is a deviation worth
naming rather than glossing. It is mitigated, not cured, by a runtime check: every trial
compares its weight against the bound and `SampleStats.violations` counts the excesses. A
violated bound silently biases the sample, so a generator that cannot detect the violation is
worse than one that reports it.

## Termination

The rejection loop runs on explicit fuel rather than `partial`.  Exhausting it returns `none`,
which the caller must handle; it does not silently return an unaccepted point.
-/

@[expose] public section

namespace Physlib
namespace Generator

open Numerics Rand

/-- A sampled hard-scattering point. -/
structure HardPoint where
  /-- Bjorken `x`. -/
  x : Float
  /-- Hard scale `Q²` in GeV². -/
  q2 : Float
  /-- Inelasticity `y = Q²/(x s)`. -/
  y : Float
  /-- Number of trials this point cost, for efficiency accounting. -/
  trials : Nat
deriving Repr, Inhabited

/-- Counters accumulated over a run. -/
structure SampleStats where
  /-- Points accepted. -/
  accepted : Nat := 0
  /-- Total trials across all points. -/
  trials : Nat := 0
  /-- Trials whose weight exceeded the claimed overestimate.  Must be zero for the sample to
  be distributed as the target; any non-zero value invalidates the run. -/
  violations : Nat := 0
  /-- Points abandoned because the rejection loop ran out of fuel. -/
  exhausted : Nat := 0
deriving Repr, Inhabited

/-- The sampling region: `Q² ∈ [q2Min, x s]` and `x ∈ [q2Min/s, 1]`, the latter because
`Q² ≤ x s` forces `x ≥ Q²_min/s` for the region to be non-empty. -/
structure Region where
  /-- Squared centre-of-mass energy. -/
  s : Float
  /-- Lower cut on `Q²`, in GeV². -/
  q2Min : Float
deriving Repr, Inhabited

/-- Smallest `x` for which the `Q²` window is non-empty. -/
def Region.xMin (r : Region) : Float := r.q2Min / r.s

/-- The acceptance weight: the ratio of the target density to the proposal density, up to
constants common to every trial.

**The window width is part of the weight, and leaving it out is a real bug.**  The proposal
is flat in `ln Q²` over `[ln Q²_min, ln(x s)]`, and that interval's *width* depends on `x`.
Writing `L(x) = ln(x s) - ln(Q²_min)`, the proposal density in `(x, Q²)` is

  `p(x, Q²) = 1 / (Δ_{ln x} · L(x) · x · Q²)`,

so the ratio to the target `T ∝ F₂(x) Y(y) / (x Q⁴)` is

  `T/p ∝ F₂(x) · Y(y) · L(x) / Q²`.

The `1/x` cancels against the proposal's, which is the point of sampling logarithmically;
the `L(x)` does **not** cancel, because the window shrinks to nothing as `x → Q²_min/s`.

This factor was missing in the first version, and the resulting sample was wrong in a way no
support or conservation check could see: every event was individually legal and the `x`
spectrum was badly distorted. It was caught only by comparing the sampled marginals against
the numerically integrated cross section — 20000 events gave `χ²/dof = 2025` against the
true target, and `χ²/dof = 0.65` against `target / L(x)`, which identified the omission
exactly rather than merely flagging a mismatch. -/
def weight (r : Region) (x q2v y : Float) : Float :=
  let l := (r.s * x).log - r.q2Min.log
  f2Toy x q2v * yFactor y * l / q2v

/-- An overestimate of `weight` on the region: `F₂^max · L^max / Q²_min`.

Three factors, of which two are bounded exactly and one is not.  `Y(y) ≤ 1` on `y ∈ [0,1]`
and `L(x) ≤ ln(s/Q²_min)` at `x = 1` are exact; `F₂^max` is found by scanning `n` points
logarithmically in `x` and inflating by `safety`, which is numerical, not analytic — see the
module docstring.  `safety` defaults to 1.3. -/
def weightBound (r : Region) (n : Nat := 512) (safety : Float := 1.3) : Float :=
  let lnLo := r.xMin.log
  let lMax := r.s.log - r.q2Min.log
  let rec go : Nat → Float → Float
    | 0, acc => acc
    | k + 1, acc =>
      let u := (n - k).toFloat / n.toFloat
      let x := (lnLo * (1.0 - u)).exp
      let v := f2Toy x r.q2Min
      go k (if v > acc then v else acc)
  safety * go n 0.0 * lMax / r.q2Min

/-- One acceptance–rejection trial chain, on explicit fuel.

Returns the accepted point together with the number of trials used and the number of bound
violations seen, or `none` if the fuel ran out. -/
def sampleHardPoint {g : Type} [RandomGen g] [Monad m]
    (r : Region) (wMax : Float) : Nat → Nat → Nat →
    RandGT g m (Option HardPoint × Nat × Nat)
  | 0, used, viol => pure (none, used, viol)
  | fuel + 1, used, viol => do
    let u1 ← uniform01
    let u2 ← uniform01
    let u3 ← uniform01
    -- flat in ln x on [ln xMin, 0]
    let x := (r.xMin.log * (1.0 - u1)).exp
    let q2Hi := r.s * x
    if q2Hi <= r.q2Min then
      sampleHardPoint r wMax fuel (used + 1) viol
    else
      -- flat in ln Q² on [ln q2Min, ln (x s)]
      let lnLo := r.q2Min.log
      let lnHi := q2Hi.log
      let q2v := (lnLo + (lnHi - lnLo) * u2).exp
      let y := q2v / (x * r.s)
      let w := weight r x q2v y
      let viol' := if w > wMax then viol + 1 else viol
      if u3 * wMax <= w then
        pure (some { x := x, q2 := q2v, y := y, trials := used + 1 }, used + 1, viol')
      else
        sampleHardPoint r wMax fuel (used + 1) viol'

/-- Fold one trial chain's outcome into the running counters.

Takes a `Bool` rather than the sampled object: the counters record *whether* a point was
produced and at what cost, and are deliberately agnostic about what was built from it, so
the same accounting serves the raw `(x, Q²)` sampler and the event-level wrapper. -/
def SampleStats.record (st : SampleStats) (produced : Bool) (used viol : Nat) :
    SampleStats :=
  { accepted := st.accepted + (if produced then 1 else 0),
    trials := st.trials + used,
    violations := st.violations + viol,
    exhausted := st.exhausted + (if produced then 0 else 1) }

end Generator
end Physlib
