/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Module
/-!

# The geometry of a planar interface

## i. Overview

In this module we set up the minimal geometric vocabulary needed to state Snell's law and
the law of reflection: the angle a propagation direction makes with the normal to a planar
interface, and the projection of a vector onto the interface (its "tangential part").

None of this is specific to electromagnetism — it is pure `Space d`/`Direction d` geometry —
but it exists to support `Electromagnetism.Interface.SnellsLaw`, so it lives alongside it.

## ii. Key results

- `angleFromNormal` : the angle (in `[0, π]`) between a direction and the interface normal.
- `tangentialPart` : the orthogonal projection of a vector onto the interface hyperplane.
- `norm_tangentialPart_smul_unit` : the tangential part of a wavevector `κ • s.unit` has norm
  `|κ| * sin (angleFromNormal n s)` — the key geometric identity used to derive Snell's law.

## iii. Table of contents

- A. The angle from the interface normal
- B. The tangential part of a vector

## iv. References

* None.
-/

@[expose] public section

namespace Electromagnetism
namespace Interface

open Space InnerProductSpace

/-!

## A. The angle from the interface normal

-/

/-- The angle, in `[0, π]`, between a direction `s` and the interface normal `n`. -/
noncomputable def angleFromNormal {d : ℕ} (n s : Direction d) : ℝ :=
  Real.arccos ⟪s.unit, n.unit⟫_ℝ

lemma abs_inner_direction_le_one {d : ℕ} (s t : Direction d) :
    |⟪s.unit, t.unit⟫_ℝ| ≤ 1 := by
  have h := abs_real_inner_le_norm s.unit t.unit
  rwa [s.norm, t.norm, mul_one] at h

lemma cos_angleFromNormal {d : ℕ} (n s : Direction d) :
    Real.cos (angleFromNormal n s) = ⟪s.unit, n.unit⟫_ℝ := by
  rw [angleFromNormal, Real.cos_arccos (abs_le.mp (abs_inner_direction_le_one s n)).1
    (abs_le.mp (abs_inner_direction_le_one s n)).2]

lemma sin_angleFromNormal {d : ℕ} (n s : Direction d) :
    Real.sin (angleFromNormal n s) = Real.sqrt (1 - ⟪s.unit, n.unit⟫_ℝ ^ 2) := by
  rw [angleFromNormal, Real.sin_arccos]

/-!

## B. The tangential part of a vector

-/

/-- The orthogonal projection of a vector onto the interface hyperplane
  `{x | ⟪x, n.unit⟫_ℝ = 0}`. -/
noncomputable def tangentialPart {d : ℕ} (n : Direction d) (k : Space d) : Space d :=
  k - ⟪k, n.unit⟫_ℝ • n.unit

lemma tangentialPart_smul {d : ℕ} (n : Direction d) (κ : ℝ) (k : Space d) :
    tangentialPart n (κ • k) = κ • tangentialPart n k := by
  simp only [tangentialPart, real_inner_smul_left, smul_sub, smul_smul, mul_comm]

lemma norm_sq_tangentialPart_unit {d : ℕ} (n s : Direction d) :
    ‖s.unit - ⟪s.unit, n.unit⟫_ℝ • n.unit‖ ^ 2 = 1 - ⟪s.unit, n.unit⟫_ℝ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, n.norm, mul_one,
    Real.norm_eq_abs, sq_abs, s.norm]
  ring

lemma norm_tangentialPart_unit {d : ℕ} (n s : Direction d) :
    ‖tangentialPart n s.unit‖ = Real.sin (angleFromNormal n s) := by
  simp only [tangentialPart]
  rw [sin_angleFromNormal, ← norm_sq_tangentialPart_unit, Real.sqrt_sq (norm_nonneg _)]

/-- The tangential part of a wavevector `κ • s.unit` has norm
  `|κ| * sin (angleFromNormal n s)`. This is the key geometric identity behind both the law
  of reflection and Snell's law: matching tangential wavevectors across an interface becomes,
  after taking norms, an equation purely in wavenumbers and angles. -/
lemma norm_tangentialPart_smul_unit {d : ℕ} (n s : Direction d) (κ : ℝ) :
    ‖tangentialPart n (κ • s.unit)‖ = |κ| * Real.sin (angleFromNormal n s) := by
  rw [tangentialPart_smul, norm_smul, Real.norm_eq_abs, norm_tangentialPart_unit]

end Interface
end Electromagnetism
