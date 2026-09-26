/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.HepMC3.Basic

/-!
# Executable four-momenta

A `Float` four-momentum with the Minkowski product, signature `(+,-,-,-)`.

This is deliberately **not** `HepMC3.FourVector`, although the two carry the same four numbers.
`FourVector` is a field of the output record: its job is to be serialized, and it has no
algebra.  `FourMom` is the arithmetic type the physics is computed in.  Keeping them distinct
is the layering the generator plan asks for — output format changes must not propagate into
kinematics, and vice versa — and `toFourVector` is the single crossing point.

Everything here is `Float`, so nothing in this file is proved.  The `ℝ`-level statements these
transcribe live in `Physlib.QFT.Scattering.DIS.Kinematics`, and the correspondence is
documented, not verified: §6 of the generator plan rules out a proved `Float`↔`ℝ` bridge.
-/

@[expose] public section

namespace Physlib
namespace Numerics

/-- A four-momentum `(pₓ, p_y, p_z; E)` in `Float`, with the Minkowski product below. -/
structure FourMom where
  /-- `x` component of the three-momentum. -/
  px : Float := 0.0
  /-- `y` component of the three-momentum. -/
  py : Float := 0.0
  /-- `z` component of the three-momentum. -/
  pz : Float := 0.0
  /-- Energy. -/
  e : Float := 0.0
deriving Repr, Inhabited

namespace FourMom

/-- Componentwise sum. -/
def add (a b : FourMom) : FourMom :=
  { px := a.px + b.px, py := a.py + b.py, pz := a.pz + b.pz, e := a.e + b.e }

/-- Componentwise difference. -/
def sub (a b : FourMom) : FourMom :=
  { px := a.px - b.px, py := a.py - b.py, pz := a.pz - b.pz, e := a.e - b.e }

/-- Componentwise negation. -/
def neg (a : FourMom) : FourMom :=
  { px := -a.px, py := -a.py, pz := -a.pz, e := -a.e }

/-- Scalar multiple. -/
def smul (c : Float) (a : FourMom) : FourMom :=
  { px := c * a.px, py := c * a.py, pz := c * a.pz, e := c * a.e }

instance : Add FourMom := ⟨add⟩
instance : Sub FourMom := ⟨sub⟩
instance : Neg FourMom := ⟨neg⟩

/-- The Minkowski product with signature `(+,-,-,-)`, so that a physical particle has
`dot p p = m² ≥ 0`. -/
def dot (a b : FourMom) : Float :=
  a.e * b.e - a.px * b.px - a.py * b.py - a.pz * b.pz

/-- Invariant mass squared, `p·p`.  Can come out slightly negative for a massless particle
through rounding; that is a property of `Float`, not of the definition. -/
def m2 (a : FourMom) : Float := dot a a

/-- Squared transverse momentum. -/
def pt2 (a : FourMom) : Float := a.px * a.px + a.py * a.py

/-- Transverse momentum. -/
def pt (a : FourMom) : Float := a.pt2.sqrt

/-- Euclidean length of the three-momentum, `|p⃗|`.

For a massless particle this equals the energy, which is what the shower's splitting
kinematics and the Durham jet measure both rely on. -/
def p3 (a : FourMom) : Float :=
  (a.px * a.px + a.py * a.py + a.pz * a.pz).sqrt

/-- A massless four-momentum built from its three components, with `E = |p|`. -/
def ofMassless (px py pz : Float) : FourMom :=
  { px := px, py := py, pz := pz, e := (px * px + py * py + pz * pz).sqrt }

/-- A four-momentum of mass `m` from its three components, with `E = √(p² + m²)`. -/
def ofMass (m px py pz : Float) : FourMom :=
  { px := px, py := py, pz := pz, e := (px * px + py * py + pz * pz + m * m).sqrt }

/-- The crossing point into the output layer. -/
def toFourVector (a : FourMom) : HepMC3.FourVector :=
  { x := a.px, y := a.py, z := a.pz, t := a.e }

end FourMom
end Numerics
end Physlib
