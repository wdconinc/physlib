/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Control.Random

/-!
# Uniform `Float` sampling

`Mathlib.Control.Random` supplies the monad (`RandGT`), the seeding entry point
(`runRandWith`), stream splitting (`split`), and `Random`/`BoundedRandom` instances for
`Fin n`, `Bool`, `Nat` and `Int`.  It has **no instance for `Float` and no uniform on
`[0,1)`**, which is the first thing a numerical layer needs.  This module supplies it.

## Why two draws, and why rejection

`StdGen`'s range is `stdRange = (1, 2147483562)`, so a single draw carries just under 31
bits — not enough for a `Float`'s 53-bit significand.  Worse, the span is not a power of two,
so simply reducing a draw modulo `2^k` is biased: `2147483562 = 2·2^30 - 86`, which makes the
low values of a `% 2^30` reduction very slightly more likely than the high ones.

Sampling a *binary* fraction correctly therefore needs whole bits, and the cheapest way to
get unbiased whole bits from a non-power-of-two range is rejection.  `randBits30` keeps a
draw only when it lands in `[0, 2^30)` — acceptance just over one half — and two accepted
blocks give 60 bits, of which the top 53 become the significand.  The result is uniform on
the `2^53` representable multiples of `2^-53` in `[0,1)`, and is never exactly `1.0`.

The rejection loop is bounded by explicit fuel rather than marked `partial`.  On exhaustion
it falls back to a modular reduction, which is biased — but the fallback is reached with
probability below `2^-64`, and it is better to document a bound than to loop forever.

## Why there is no `BoundedRandom` instance

`BoundedRandom m α` is declared `[Preorder α]` and its `randomR` returns
`{a // lo ≤ a ∧ a ≤ hi}` — a sample carrying a *proof* of its own bounds.  Neither half is
available for `Float`:

* **There is no `Preorder Float`, and there cannot lawfully be one.** `Preorder` requires
  `le_refl : ∀ a, a ≤ a`, and `Float`'s `≤` is the IEEE-754 comparison, which is `false` at
  `NaN`.  No such instance exists in core or mathlib, and adding one would be unsound.
* Even granting an order, discharging the bound proof would need `Float` arithmetic facts of
  exactly the kind this library deliberately does not claim.

So bounded sampling is supplied as a plain function, `uniformIn`, with **no proof attached**.
Callers that need the bound must check it.  Stating that here is the point: the absence of a
`BoundedRandom Float` instance is a deliberate correctness decision, not an omission.
-/

@[expose] public section

namespace Physlib
namespace Numerics

-- `next`, `range` and `split` live in `Rand`; the `Random` class itself is top-level.
open Rand

/-- Number of bits taken from each accepted draw. -/
def blockBits : Nat := 30

/-- `2 ^ blockBits`, the rejection bound for a single draw.

Derived from `blockBits` rather than written out, so the two cannot drift apart. -/
def blockBound : Nat := 2 ^ blockBits

/-- Number of bits in a `Float` significand, including the implicit leading bit. -/
def significandBits : Nat := 53

/-- `2 ^ significandBits`, the denominator of the returned fraction.

Derived from `significandBits` for the same reason as `blockBound`. -/
def significandBound : Nat := 2 ^ significandBits

/-- Draw a uniform `blockBits`-bit block by rejecting values at or above `blockBound`.

Fuel bounds the number of rejections.  On exhaustion a **final fresh draw** is reduced modulo
`blockBound`, which is slightly biased; the rejected value that exhausted the fuel is not
reused.  With the default fuel this branch is reached with probability below `2 ^ (-64)`,
since each rejection has probability below `1/2`. -/
def randBits30 {g : Type} [RandomGen g] [Monad m] : Nat → RandGT g m Nat
  | 0 => do
    let (lo, _) ← range
    let a ← next
    pure ((a - lo) % blockBound)
  | fuel + 1 => do
    let (lo, _) ← range
    let a ← next
    let v := a - lo
    if v < blockBound then pure v else randBits30 fuel

/-- A uniform `Float` in `[0,1)`.

Returns one of the `2 ^ 53` multiples of `2 ^ (-53)` in `[0,1)`, each with equal probability.
The value is never exactly `1.0`: the numerator is strictly below `2 ^ 53` by construction. -/
def uniform01 {g : Type} [RandomGen g] [Monad m] (fuel : Nat := 64) : RandGT g m Float := do
  let hi ← randBits30 fuel
  let lo ← randBits30 fuel
  -- 60 bits, of which the top 53 are kept
  let k := (hi * blockBound + lo) / 128
  pure (k.toFloat / significandBound.toFloat)

instance [Monad m] : Random m Float where
  random := uniform01

/-- A uniform `Float` in `[lo, hi)`, carrying **no proof** of its bounds — see the module
docstring for why `BoundedRandom` is not instantiated.

For finite `lo ≤ hi` with finite `hi - lo`, the result lies in `[lo, hi)` up to rounding of
the affine map.  No claim is made when either endpoint is infinite or `NaN`. -/
def uniformIn {g : Type} [RandomGen g] [Monad m] (lo hi : Float) (fuel : Nat := 64) :
    RandGT g m Float := do
  let u ← uniform01 fuel
  pure (lo + (hi - lo) * u)

/-- Derive an independent substream, so that changing the number of draws taken by one stage
cannot perturb any other stage.

This is `Mathlib.Control.Random`'s `split` under a name that says what it is for.  A
generator should derive one substream per stage — hard process, shower, hadronization,
decays — from the run seed, rather than drawing from a single shared stream. -/
def substream {g : Type} [RandomGen g] [Monad m] : RandGT g m g := split

end Numerics
end Physlib
