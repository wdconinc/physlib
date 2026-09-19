/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Data.Complex.Basic
/-!

# Dimensional Regularization Core

This module introduces the minimal analytic objects needed to represent
dimensional-regularized quantities near $\varepsilon = 0$.

The focus is intentionally narrow: a Laurent-style expansion with at most a
simple pole, together with a scheme tag for MS-like renormalization.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace PerturbationTheory
namespace DimensionalRegularization

/-- Minimal renormalization-scheme tags used by the perturbative interface. -/
inductive RenormalizationScheme where
  /-- Minimal subtraction. -/
  | MS
  /-- Modified minimal subtraction. -/
  | MSBar

/-- Space-time dimension as a function of the dimensional regulator $\varepsilon$. -/
def regularizedDimension (ε : ℝ) : ℝ :=
  4 - ε

/-- A Laurent-style expansion at $\varepsilon = 0$ with at most a simple pole.

It is represented by a pole coefficient, a finite part, and a regular remainder.
The remainder is left abstract for now; later modules can impose analytic
conditions such as continuity or a vanishing limit at zero.
-/
structure LaurentExpansionAtZero : Type where
  /-- Coefficient of the simple pole term $1/\varepsilon$. -/
  poleCoeff : ℝ
  /-- Finite part at order $\varepsilon^0$. -/
  finitePart : ℂ
  /-- Higher-order regular remainder. -/
  regularPart : ℝ → ℂ

/-- Evaluate a Laurent-style expansion away from $\varepsilon = 0$. -/
def LaurentExpansionAtZero.eval (x : LaurentExpansionAtZero) (ε : ℝ) : ℂ :=
  ((x.poleCoeff / ε : ℝ) : ℂ) + x.finitePart + x.regularPart ε

/-- The principal part of the Laurent expansion. -/
def LaurentExpansionAtZero.principalPart (x : LaurentExpansionAtZero) (ε : ℝ) : ℂ :=
  ((x.poleCoeff / ε : ℝ) : ℂ)

/-- Predicate asserting that the expansion is regular at $\varepsilon = 0$. -/
def LaurentExpansionAtZero.IsRegular (x : LaurentExpansionAtZero) : Prop :=
  x.poleCoeff = 0

/-- Extract the simple-pole coefficient of a Laurent expansion. -/
def poleCoeff (x : LaurentExpansionAtZero) : ℝ :=
  x.poleCoeff

/-- A regular expansion has vanishing extracted pole coefficient. -/
lemma poleCoeff_eq_zero_of_regular (x : LaurentExpansionAtZero) (h : x.IsRegular) :
    poleCoeff x = 0 :=
  h

/-- Canonical regular expansion attached to a finite complex value. -/
def regularOfComplex (z : ℂ) : LaurentExpansionAtZero where
  poleCoeff := 0
  finitePart := z
  regularPart := fun _ => 0

/-- The extracted pole coefficient of a regular quantity vanishes. -/
@[simp] lemma poleCoeff_regularOfComplex (z : ℂ) :
    poleCoeff (regularOfComplex z) = 0 :=
  rfl

end DimensionalRegularization
end PerturbationTheory
end QFT
end Physlib
