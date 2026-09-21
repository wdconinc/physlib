/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.Contracting
/-!

# Reciprocity: spacelike and timelike anomalous dimensions

## i. Overview

Twist-two operators in a gauge theory organise into a Regge trajectory: a curve in the
`(spin, dimension)` plane, analytic in the spin variable. In the free theory the twist-two
trajectory is the straight line `Δ = J + τ` of slope one — the "45-degree line" — where `τ`
is the free twist. Interactions displace the trajectory off that line, and there are two
equally valid ways to record the displacement of a point of the interacting trajectory from
the free line:

- *vertically*, at fixed spin, by the increase in dimension. This is the **spacelike**
  anomalous dimension `γ_S`, the one that governs deep-inelastic (spacelike) DGLAP evolution
  of parton distributions;
- *horizontally*, at fixed dimension, by the decrease in spin. This is the **timelike**
  anomalous dimension `γ_T`, the one that governs fragmentation and the collinear limit of
  energy correlators.

Because the free trajectory has slope exactly one, the two displacements are not independent.
Eliminating the point of the trajectory between them gives the *reciprocity relation*

`γ_T N = γ_S (N - γ_T N)`,

which is the content of `ReggeTrajectory.reciprocity` below. This is the geometric reading of
reciprocity given in Lee, Moult and Zhang, *Revisiting Single Inclusive Jet Production:
Timelike Factorization and Reciprocity*, `arXiv:2409.19045`, eq. (19); the relation itself goes
back to Gribov and Lipatov and to Drell, Levy and Yan, and its all-order form is due to
Dokshitzer, Marchesini and Salam.

## ii. What is and is not assumed

The single physical input is `ReggeTrajectory`: **one** analytic trajectory, of which the
spacelike and the timelike anomalous dimension are two different coordinate readings. That is
exactly the modern statement of reciprocity, and it is the only physics hypothesis here. No
perturbative expansion, no explicit splitting function, and no factorization theorem is
assumed.

The one analytic hypothesis is `ReggeTrajectory.lip_lt_one`: the spacelike anomalous dimension
is Lipschitz in the spin with constant `lip < 1`. Geometrically this says the interacting
trajectory has slope in `(0, 2)` and so never turns back in spin, which is what makes the
horizontal displacement — and hence `γ_T` — well defined at all. Physically it is weak
coupling: `∂γ_S/∂N = O(α_s)`. It is not vacuous: `affineTrajectory` is an explicit family
satisfying every field, with `γ_S ≠ γ_T`.

Nothing here formalizes energy correlators themselves. The connection is one of motivation
only: the collinear limit of the projected energy correlator scales with the *timelike*
anomalous dimension, and reciprocity is what converts that into a statement about the
spacelike one.

## iii. Key results

- `ReggeTrajectory` bundles the free twist, the spacelike anomalous dimension, and the
  Lipschitz hypothesis.
- `ReggeTrajectory.IsTimelikeAnomalousDim` is the *geometric* definition of `γ_T`: the point
  of the interacting trajectory at spin `N - γ` has the free dimension of spin `N`.
- `ReggeTrajectory.isTimelikeAnomalousDim_iff` shows that geometric statement is equivalent to
  the implicit equation `γ = γ_S (N - γ)`.
- `ReggeTrajectory.timelikeAnomalousDim_existsUnique` is well-posedness: for each `N` exactly
  one `γ` satisfies it, by the Banach fixed point theorem.
- `ReggeTrajectory.reciprocity` is the reciprocity relation `γ_T N = γ_S (N - γ_T N)`.
- `ReggeTrajectory.norm_timelike_sub_spacelike_le` is the quantitative Gribov-Lipatov
  statement: `‖γ_T N - γ_S N‖ ≤ lip * ‖γ_T N‖`, so the two anomalous dimensions differ only at
  second order in the trajectory's departure from the free line.
- `ReggeTrajectory.dimension_injective` is the no-turning-back statement that makes `γ_T` well
  defined.
- `affineTrajectory` and `affineTrajectory_spacelike_sub_timelike` exhibit the whole structure
  on a solvable trajectory and display the reciprocity-violating difference explicitly.

## iv. Conventions

Spin and dimension are complex throughout: the trajectory is the analytic continuation in spin,
and the Mellin index of `Physlib.QFT.Factorization.Evolution` is likewise complex. `N` names a
spin argument, `J` a spin at which the trajectory is being evaluated. Both anomalous dimensions
are taken with the sign convention in which `Δ = J + τ + γ_S J`, i.e. a positive `γ_S` raises
the dimension.

## v. Table of contents

- A. Regge trajectories
- B. The timelike anomalous dimension
- C. Reciprocity
- D. Gribov-Lipatov: how far spacelike and timelike differ
- E. A solvable trajectory

-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Physlib
namespace QFT
namespace Factorization
namespace Evolution

/-! ## A. Regge trajectories -/

/-- The dimension of the free twist-`τ` trajectory at spin `J`. The slope is one; this is the
"45-degree line" whose slope is the whole reason spacelike and timelike anomalous dimensions
are related. -/
def freeDimension (twist J : ℂ) : ℂ := J + twist

/-- An interacting twist-two Regge trajectory, recorded by its vertical displacement from the
free line.

The displacement `spacelikeAnomalousDim` is the spacelike anomalous dimension: the amount by
which interactions raise the dimension of the operator of spin `J` above its free value.
`lip_lt_one` says the trajectory never turns back in spin, so that a point of it is equally
well specified by its dimension; that is what makes the timelike anomalous dimension exist. -/
structure ReggeTrajectory where
  /-- The twist of the free trajectory, i.e. the intercept of the free 45-degree line. -/
  twist : ℂ
  /-- The spacelike anomalous dimension: the vertical displacement of the interacting
  trajectory above the free line, as a function of the spin. -/
  spacelikeAnomalousDim : ℂ → ℂ
  /-- A Lipschitz constant for the spacelike anomalous dimension as a function of the spin. -/
  lip : ℝ≥0
  /-- The spacelike anomalous dimension is `lip`-Lipschitz in the spin. -/
  lipschitz : LipschitzWith lip spacelikeAnomalousDim
  /-- The trajectory is nowhere steeper than the free line by a factor of two, and nowhere
  turns back: its slope lies in `(0, 2)`. Perturbatively this is `∂γ_S/∂N = O(α_s) ≪ 1`. -/
  lip_lt_one : lip < 1

namespace ReggeTrajectory

variable (T : ReggeTrajectory)

/-- The dimension of the interacting trajectory at spin `J`. -/
def dimension (J : ℂ) : ℂ := freeDimension T.twist J + T.spacelikeAnomalousDim J

lemma dimension_apply (J : ℂ) : T.dimension J = J + T.twist + T.spacelikeAnomalousDim J := rfl

lemma coe_lip_lt_one : (T.lip : ℝ) < 1 := by exact_mod_cast T.lip_lt_one

lemma one_sub_coe_lip_pos : 0 < 1 - (T.lip : ℝ) := by
  have := T.coe_lip_lt_one
  linarith

/-- The interacting trajectory never turns back in spin: two spins a distance `d` apart have
dimensions at least `(1 - lip) * d` apart. This is the quantitative form of the hypothesis
`lip_lt_one`, and it is why a point of the trajectory may be specified by its dimension
instead of by its spin. -/
lemma norm_dimension_sub_dimension_ge (J₁ J₂ : ℂ) :
    (1 - (T.lip : ℝ)) * ‖J₁ - J₂‖ ≤ ‖T.dimension J₁ - T.dimension J₂‖ := by
  have hlip : ‖T.spacelikeAnomalousDim J₁ - T.spacelikeAnomalousDim J₂‖
      ≤ (T.lip : ℝ) * ‖J₁ - J₂‖ := by
    simpa [dist_eq_norm] using T.lipschitz.dist_le_mul J₁ J₂
  have hsplit : J₁ - J₂ = (T.dimension J₁ - T.dimension J₂)
      - (T.spacelikeAnomalousDim J₁ - T.spacelikeAnomalousDim J₂) := by
    simp only [dimension_apply]
    ring
  have htri : ‖J₁ - J₂‖ ≤ ‖T.dimension J₁ - T.dimension J₂‖
      + ‖T.spacelikeAnomalousDim J₁ - T.spacelikeAnomalousDim J₂‖ := by
    rw [hsplit]
    exact norm_sub_le _ _
  nlinarith [norm_nonneg (J₁ - J₂), norm_nonneg (T.dimension J₁ - T.dimension J₂)]

/-- A point of the interacting trajectory is determined by its dimension. -/
lemma dimension_injective : Function.Injective T.dimension := by
  intro J₁ J₂ h
  have hb := T.norm_dimension_sub_dimension_ge J₁ J₂
  rw [h, sub_self, norm_zero] at hb
  have hpos := T.one_sub_coe_lip_pos
  have hle : ‖J₁ - J₂‖ ≤ 0 := by nlinarith [norm_nonneg (J₁ - J₂)]
  have hd : dist J₁ J₂ = 0 := by
    rw [dist_eq_norm]
    exact le_antisymm hle (norm_nonneg _)
  exact dist_eq_zero.mp hd

/-! ## B. The timelike anomalous dimension -/

/-- `γ` is the timelike anomalous dimension of the trajectory `T` at spin `N` when the point of
the interacting trajectory whose spin is `N - γ` sits at the dimension the *free* trajectory has
at spin `N`. In words: `γ` is the horizontal displacement, at fixed dimension, between the free
and the interacting trajectory. -/
def IsTimelikeAnomalousDim (N γ : ℂ) : Prop :=
  T.dimension (N - γ) = freeDimension T.twist N

/-- The geometric definition of the timelike anomalous dimension is the implicit equation
`γ = γ_S (N - γ)`. Both the 45-degree slope of the free line and the cancellation of the twist
are used here; nothing else. -/
lemma isTimelikeAnomalousDim_iff (N γ : ℂ) :
    T.IsTimelikeAnomalousDim N γ ↔ γ = T.spacelikeAnomalousDim (N - γ) := by
  simp only [IsTimelikeAnomalousDim, dimension_apply, freeDimension]
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h

/-- The self-map of the spin plane whose fixed point is the timelike anomalous dimension. -/
def timelikeMap (N : ℂ) : ℂ → ℂ := fun γ => T.spacelikeAnomalousDim (N - γ)

lemma lipschitzWith_timelikeMap (N : ℂ) : LipschitzWith T.lip (T.timelikeMap N) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := T.lipschitz.dist_le_mul (N - x) (N - y)
  have hd : dist (N - x) (N - y) = dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    have he : N - x - (N - y) = -(x - y) := by ring
    rw [he, norm_neg]
  rwa [hd] at h

lemma contractingWith_timelikeMap (N : ℂ) : ContractingWith T.lip (T.timelikeMap N) :=
  ⟨T.lip_lt_one, T.lipschitzWith_timelikeMap N⟩

/-- The timelike anomalous dimension of the trajectory `T` at spin `N`, obtained as the Banach
fixed point of `timelikeMap`. -/
def timelikeAnomalousDim (N : ℂ) : ℂ :=
  ContractingWith.fixedPoint (T.timelikeMap N) (T.contractingWith_timelikeMap N)

lemma isTimelikeAnomalousDim_timelikeAnomalousDim (N : ℂ) :
    T.IsTimelikeAnomalousDim N (T.timelikeAnomalousDim N) := by
  rw [T.isTimelikeAnomalousDim_iff]
  have h : T.timelikeMap N (T.timelikeAnomalousDim N) = T.timelikeAnomalousDim N :=
    (T.contractingWith_timelikeMap N).fixedPoint_isFixedPt
  exact h.symm

lemma isTimelikeAnomalousDim_unique {N γ₁ γ₂ : ℂ} (h₁ : T.IsTimelikeAnomalousDim N γ₁)
    (h₂ : T.IsTimelikeAnomalousDim N γ₂) : γ₁ = γ₂ := by
  rw [T.isTimelikeAnomalousDim_iff] at h₁ h₂
  have k₁ : T.timelikeMap N γ₁ = γ₁ := h₁.symm
  have k₂ : T.timelikeMap N γ₂ = γ₂ := h₂.symm
  exact (T.contractingWith_timelikeMap N).fixedPoint_unique' k₁ k₂

/-- Well-posedness of the timelike anomalous dimension: at every spin there is exactly one
horizontal displacement between the free and the interacting trajectory. -/
lemma timelikeAnomalousDim_existsUnique (N : ℂ) :
    ∃! γ : ℂ, T.IsTimelikeAnomalousDim N γ :=
  ⟨T.timelikeAnomalousDim N, T.isTimelikeAnomalousDim_timelikeAnomalousDim N,
    fun _ hγ => T.isTimelikeAnomalousDim_unique hγ
      (T.isTimelikeAnomalousDim_timelikeAnomalousDim N)⟩

lemma eq_timelikeAnomalousDim_of_isTimelikeAnomalousDim {N γ : ℂ}
    (h : T.IsTimelikeAnomalousDim N γ) : γ = T.timelikeAnomalousDim N :=
  T.isTimelikeAnomalousDim_unique h (T.isTimelikeAnomalousDim_timelikeAnomalousDim N)

/-- The timelike anomalous dimension inherits Lipschitz regularity from the trajectory, with
the constant enhanced by the fixed-point denominator `1 - lip`. -/
lemma norm_timelikeAnomalousDim_sub_le (N M : ℂ) :
    ‖T.timelikeAnomalousDim N - T.timelikeAnomalousDim M‖
      ≤ (T.lip : ℝ) * ‖N - M‖ / (1 - (T.lip : ℝ)) := by
  have hC : ∀ z : ℂ, dist (T.timelikeMap N z) (T.timelikeMap M z) ≤ (T.lip : ℝ) * ‖N - M‖ := by
    intro z
    have h := T.lipschitz.dist_le_mul (N - z) (M - z)
    have hd : dist (N - z) (M - z) = ‖N - M‖ := by
      rw [dist_eq_norm]
      congr 1
      ring
    rw [hd] at h
    exact h
  have h := ContractingWith.fixedPoint_lipschitz_in_map (T.contractingWith_timelikeMap N)
    (T.contractingWith_timelikeMap M) hC
  rw [dist_eq_norm] at h
  exact h

/-! ## C. Reciprocity -/

/-- **The reciprocity relation.** The timelike anomalous dimension at spin `N` equals the
spacelike anomalous dimension evaluated at the shifted spin `N - γ_T N`.

This is eq. (19) of `arXiv:2409.19045`, in the sign convention of this file. Its content is
that the two anomalous dimensions are two coordinate readings of one and the same point of one
and the same Regge trajectory; the algebra that turns that statement into the displayed
identity is elementary, and the physics is entirely in the hypothesis. -/
theorem reciprocity (N : ℂ) :
    T.timelikeAnomalousDim N = T.spacelikeAnomalousDim (N - T.timelikeAnomalousDim N) :=
  (T.isTimelikeAnomalousDim_iff N _).mp (T.isTimelikeAnomalousDim_timelikeAnomalousDim N)

/-- The reciprocity relation read in the other direction: the spacelike anomalous dimension at
spin `J` is the timelike anomalous dimension at the shifted spin `J + γ_S J`. Unlike
`reciprocity` this direction needs no fixed-point argument, because the shift is explicit. -/
theorem reciprocity_spacelike (J : ℂ) :
    T.timelikeAnomalousDim (J + T.spacelikeAnomalousDim J) = T.spacelikeAnomalousDim J := by
  refine (T.eq_timelikeAnomalousDim_of_isTimelikeAnomalousDim ?_).symm
  rw [T.isTimelikeAnomalousDim_iff]
  congr 1
  ring

/-! ## D. Gribov-Lipatov: how far spacelike and timelike differ -/

/-- **Quantitative Gribov-Lipatov.** The timelike and spacelike anomalous dimensions at the
same spin differ by at most `lip` times the anomalous dimension itself.

Perturbatively both `lip` and `γ_T` are `O(α_s)`, so the difference is `O(α_s²)`: the naive
Gribov-Lipatov identification `γ_T = γ_S` is correct at one loop and is violated, in a
controlled way, beyond it. -/
lemma norm_timelike_sub_spacelike_le (N : ℂ) :
    ‖T.timelikeAnomalousDim N - T.spacelikeAnomalousDim N‖
      ≤ (T.lip : ℝ) * ‖T.timelikeAnomalousDim N‖ := by
  have hrec := T.reciprocity N
  have h := T.lipschitz.dist_le_mul (N - T.timelikeAnomalousDim N) N
  have he : N - T.timelikeAnomalousDim N - N = -T.timelikeAnomalousDim N := by ring
  rw [dist_eq_norm, dist_eq_norm, he, norm_neg, ← hrec] at h
  exact h

/-- The same bound expressed through the spacelike anomalous dimension, which is the quantity
normally known from a fixed-order DGLAP calculation. -/
lemma norm_timelikeAnomalousDim_le (N : ℂ) :
    (1 - (T.lip : ℝ)) * ‖T.timelikeAnomalousDim N‖ ≤ ‖T.spacelikeAnomalousDim N‖ := by
  have h := T.norm_timelike_sub_spacelike_le N
  have htri : ‖T.timelikeAnomalousDim N‖ - ‖T.spacelikeAnomalousDim N‖
      ≤ ‖T.timelikeAnomalousDim N - T.spacelikeAnomalousDim N‖ := norm_sub_norm_le _ _
  nlinarith

/-- If the trajectory is exactly parallel to the free line — a spin-independent anomalous
dimension — then spacelike and timelike anomalous dimensions coincide. This is the degenerate
case in which Gribov-Lipatov is exact. -/
lemma timelikeAnomalousDim_eq_spacelikeAnomalousDim_of_lip_eq_zero (h : T.lip = 0) (N : ℂ) :
    T.timelikeAnomalousDim N = T.spacelikeAnomalousDim N := by
  have hb := T.norm_timelike_sub_spacelike_le N
  rw [h] at hb
  simp only [NNReal.coe_zero, zero_mul] at hb
  have hd : dist (T.timelikeAnomalousDim N) (T.spacelikeAnomalousDim N) = 0 := by
    rw [dist_eq_norm]
    exact le_antisymm hb (norm_nonneg _)
  exact dist_eq_zero.mp hd

/-! ## E. A solvable trajectory -/

/-- The affine trajectory `γ_S J = a * J + b`, the linearisation of a Regge trajectory about a
reference spin. It satisfies every hypothesis of `ReggeTrajectory` whenever `‖a‖ < 1`, which
shows the hypotheses are consistent, and it is solvable in closed form. -/
def affineTrajectory (twist a b : ℂ) (ha : ‖a‖₊ < 1) : ReggeTrajectory where
  twist := twist
  spacelikeAnomalousDim := fun J => a * J + b
  lip := ‖a‖₊
  lipschitz := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have he : a * x + b - (a * y + b) = a * (x - y) := by ring
    have hEq : dist (a * x + b) (a * y + b) = (‖a‖₊ : ℝ) * dist x y := by
      rw [dist_eq_norm, dist_eq_norm, he, norm_mul, coe_nnnorm]
    exact hEq.le
  lip_lt_one := ha

lemma affineTrajectory_one_add_ne_zero {a : ℂ} (ha : ‖a‖₊ < 1) : (1 : ℂ) + a ≠ 0 := by
  intro h
  have hva : a = -1 := by linear_combination h
  rw [hva] at ha
  simp at ha

/-- The timelike anomalous dimension of the affine trajectory, in closed form. It differs from
the spacelike one, `a * N + b`, by the factor `1 / (1 + a)`. -/
lemma affineTrajectory_timelikeAnomalousDim (twist a b : ℂ) (ha : ‖a‖₊ < 1) (N : ℂ) :
    (affineTrajectory twist a b ha).timelikeAnomalousDim N = (a * N + b) / (1 + a) := by
  have hne := affineTrajectory_one_add_ne_zero ha
  refine ((affineTrajectory twist a b ha).eq_timelikeAnomalousDim_of_isTimelikeAnomalousDim
    ?_).symm
  rw [(affineTrajectory twist a b ha).isTimelikeAnomalousDim_iff]
  show (a * N + b) / (1 + a) = a * (N - (a * N + b) / (1 + a)) + b
  field_simp
  ring

/-- The reciprocity-violating difference on the affine trajectory, explicitly. It carries one
extra power of the slope `a` relative to the anomalous dimension itself, which is the
statement that Gribov-Lipatov violation is second order. -/
lemma affineTrajectory_spacelike_sub_timelike (twist a b : ℂ) (ha : ‖a‖₊ < 1) (N : ℂ) :
    (affineTrajectory twist a b ha).spacelikeAnomalousDim N
      - (affineTrajectory twist a b ha).timelikeAnomalousDim N = a * (a * N + b) / (1 + a) := by
  have hne := affineTrajectory_one_add_ne_zero ha
  rw [affineTrajectory_timelikeAnomalousDim]
  show a * N + b - (a * N + b) / (1 + a) = a * (a * N + b) / (1 + a)
  field_simp
  ring

end ReggeTrajectory

end Evolution
end Factorization
end QFT
end Physlib
