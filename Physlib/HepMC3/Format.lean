/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

/-!
# Exact fixed-precision decimal rendering of `Float`

HepMC3's `WriterAscii` prints every floating point quantity with C's `printf` conversion
`%.Ne`: a single digit before the point, exactly `N` digits after it, and a signed exponent
of at least two digits.  Reproducing the *format* is easy; reproducing the *digits* is not,
because `printf` renders the exact value of the binary double, which is in general a decimal
of up to 767 significant digits, and then rounds once.

This module therefore does no floating point arithmetic at all.  It takes the IEEE-754 bit
pattern apart into `x = (-1)^neg * m * 2^e` with `m e : ℕ, ℤ`, and performs the decimal
conversion in exact `ℕ` arithmetic, which is arbitrary precision in Lean.  The single
rounding step is round-half-to-even, matching the default IEEE rounding mode that `glibc`'s
`printf` uses.  The output is consequently digit-for-digit what a C writer emits, rather
than merely a decimal that happens to parse back to the same double.

The alternative — reformatting the shortest round-tripping decimal that `Float.toString`
produces — would also round-trip correctly through any reader, but would differ from a
reference file in the low-order digits (`5.1099999999999995e-04` against
`5.1100000000000000e-04`).  Byte comparison against reference output is the cheapest way to
test a writer, so it is worth keeping.

## Main definitions

* `Physlib.HepMC3.floatParts` — exact IEEE-754 decomposition.
* `Physlib.HepMC3.formatScientific` — the `%.Ne` renderer.
-/

@[expose] public section

namespace Physlib
namespace HepMC3

/-- The exact IEEE-754 decomposition of a finite `Float` as `(-1)^neg * m * 2^e`. -/
structure FloatParts where
  /-- Sign bit: `true` for negative values, including negative zero. -/
  neg : Bool
  /-- Significand, as a non-negative integer (the implicit leading bit is included for
  normal numbers). -/
  m : Nat
  /-- Binary exponent, such that the value is `m * 2^e` up to sign. -/
  e : Int
deriving Repr, Inhabited

/-- Take a `Float` apart into its exact IEEE-754 double-precision fields.

The result is meaningful only for finite inputs; `formatScientific` screens out `nan` and
the infinities before calling this. -/
def floatParts (x : Float) : FloatParts :=
  let b := x.toBits.toNat
  let neg := (b >>> 63) == 1
  let be := (b >>> 52) &&& 0x7ff
  let fr := b &&& 0xfffffffffffff
  if be == 0 then
    -- Subnormal (and zero): no implicit leading bit.
    { neg := neg, m := fr, e := -1074 }
  else
    { neg := neg, m := fr + 0x10000000000000, e := (be : Int) - 1075 }

/-- Decide `m * 2^e ≥ 10^E` exactly, by clearing both denominators into `ℕ`.

`Int.toNat` clamps negatives to `0`, which is exactly the "move this factor to the other
side" behaviour wanted here. -/
def geTenPow (m : Nat) (e : Int) (E : Int) : Bool :=
  m * 2 ^ e.toNat * 10 ^ (-E).toNat ≥ 10 ^ E.toNat * 2 ^ (-e).toNat

/-- `num / den` rounded to nearest, ties to even — the default IEEE rounding mode, and so
the one `printf` applies. -/
def divRoundHalfEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den then q + 1
  else if 2 * r < den then q
  else if q % 2 == 0 then q else q + 1

/-- Walk `E` downward until `10^E ≤ m·2^e`, returning `none` if the fuel runs out first.

A top-level definition rather than a `let rec` inside `decExp`: Lean lifts a `let rec` to
`decExp.down`, and the repository's documentation linter requires a docstring on it, which
there is no syntax to attach to a `let rec`.

**Why `Option` rather than `private`.** Review of #45 rightly objected that a lifted helper
carrying a fuel precondition is an exported footgun: given too little fuel it used to
return an `E` that quietly fails the postcondition in this very sentence.  `private` is not
available as the remedy — Lean's module system forbids an exposed `def` body from
referencing a private name, and `decExp` is exposed all the way out through
`formatScientific`, which `Physlib.HepMC3.Ascii` calls.  So the precondition is encoded in
the return type instead: exhausting the fuel is `none`, which no caller can mistake for an
answer. -/
def decExpDown (m : Nat) (e : Int) (E : Int) : Nat → Option Int
  | 0 => none
  | n + 1 => if geTenPow m e E then some E else decExpDown m e (E - 1) n

/-- Walk `E` upward while `10^(E+1) ≤ m·2^e`, returning `none` if the fuel runs out first.
Lifted, and `Option`-valued, for the same reasons as `decExpDown`. -/
def decExpUp (m : Nat) (e : Int) (E : Int) : Nat → Option Int
  | 0 => none
  | n + 1 => if geTenPow m e (E + 1) then decExpUp m e (E + 1) n else some E

/-- The greatest `E` with `10^E ≤ m * 2^e`, for `m ≠ 0`.

Seeded from `log₂(m·2^e) · log₁₀2` and then corrected exactly.  The correction loops are
fuel-bounded rather than `partial`: a double has `|E| ≤ 324`, so the seed is never more
than a few steps out and the supplied fuel is ample. -/
def decExp (m : Nat) (e : Int) : Int :=
  let seed : Int := ((Nat.log2 m : Int) + e) * 30103 / 100000
  -- 2200 against a worst case of `|E| ≤ 324` for a double, so neither `none` branch is
  -- reachable from here; the fallback to the unrefined seed only discharges the
  -- `Option` and is never taken.
  ((decExpDown m e seed 2200).bind fun E => decExpUp m e E 2200).getD seed

/-- The significand digits and decimal exponent of `m * 2^e` at `prec` digits after the
point: returns `(digits, E)` with `digits` the `prec + 1` significant digits and the value
equal to `0.digits * 10^(E+1)`.

The rounding is a single exact division, so no double rounding occurs.  Carry out of the
leading digit (`9.99… → 10.0…`) lengthens the digit string, which is detected and folded
back into the exponent. -/
def sciDigits (m : Nat) (e : Int) (prec : Nat) : String × Int :=
  let E := decExp m e
  let k : Int := (prec : Int) - E
  let num := m * 2 ^ e.toNat * 10 ^ k.toNat
  let den := 2 ^ (-e).toNat * 10 ^ (-k).toNat
  let s := toString (divRoundHalfEven num den)
  if s.length > prec + 1 then (String.ofList (s.toList.take (prec + 1)), E + 1)
  else (s, E)

/-- Render `x` the way C's `printf("%.<prec>e", x)` does: one digit, a point, exactly
`prec` digits, then `e` and a signed exponent padded to at least two digits.

Non-finite inputs render as `nan`, `inf` and `-inf`, again matching `printf`.  Negative zero
keeps its sign, as it does there. -/
def formatScientific (prec : Nat) (x : Float) : String :=
  if x.isNaN then "nan"
  else if !x.isFinite then (if x < 0 then "-" else "") ++ "inf"
  else
    let p := floatParts x
    let sign := if p.neg then "-" else ""
    if p.m == 0 then
      sign ++ "0." ++ String.ofList (List.replicate prec '0') ++ "e+00"
    else
      let (ds, E) := sciDigits p.m p.e prec
      let l := ds.toList
      let frac := String.ofList (l.drop 1)
      let frac := frac ++ String.ofList (List.replicate (prec - frac.length) '0')
      let ea := E.natAbs
      let estr := if ea < 10 then "0" ++ toString ea else toString ea
      sign ++ String.ofList [l.headD '0'] ++ "." ++ frac
        ++ "e" ++ (if E < 0 then "-" else "+") ++ estr

end HepMC3
end Physlib
