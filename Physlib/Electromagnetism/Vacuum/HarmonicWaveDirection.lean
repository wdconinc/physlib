/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Vacuum.IsPlaneWave
/-!

# Harmonic wave in an arbitrary direction

## i. Overview

`Vacuum.HarmonicWave.harmonicWaveX` constructs a monochromatic plane-wave solution of
Maxwell's equations in free space, but restricts propagation to the first coordinate axis.
Deriving Snell's law (`Electromagnetism.Interface.SnellsLaw`) needs the incident, reflected
and transmitted waves at an interface, whose propagation directions are generally not
axis-aligned, so this module generalizes the construction to an arbitrary
`s : Direction d`, using the direction-generic `planeWave` machinery from
`ClassicalMechanics.WaveEquation.Basic` rather than the per-axis-component encoding of
`harmonicWaveX`.

The wave is transverse: the electric-field amplitude `E₀` is required to satisfy
`∑ i, s.unit i * E₀ i = 0` (the component-sum form of `⟪E₀, s.unit⟫ = 0`; `E₀` and `s.unit`
have different Lean types — `EuclideanSpace ℝ (Fin d)` for field amplitudes versus `Space d`
for positions/directions — so the sum is spelled out rather than written with inner-product
notation across the two).

## ii. Key results

- `harmonicWave` : the electromagnetic potential of a monochromatic transverse plane wave
  travelling in direction `s` with wavenumber `κ` and amplitude `E₀`.
- `harmonicWave_electricField` : the closed-form electric field.
- `harmonicWave_magneticFieldMatrix` : the closed-form magnetic field matrix.
- `harmonicWave_isPlaneWave` : the wave matches the general `IsPlaneWave` predicate.
- `harmonicWave_div_electricField_eq_zero` : Gauss's law for the wave (transversality).

## iii. Table of contents

- A. The scalar amplitude of the vector potential and its derivative
- B. The electromagnetic potential for a harmonic wave in direction `s`
- C. The electric field
- D. The magnetic field matrix
- E. The harmonic wave is a plane wave
- F. Gauss's law for the harmonic wave

## iv. References

* None.
-/

@[expose] public section
namespace Electromagnetism
namespace ElectromagneticPotential

open Space Time InnerProductSpace ClassicalMechanics

variable {d : ℕ}

/-!

## A. The scalar amplitude of the vector potential and its derivative

-/

/-- The scalar amplitude function of the vector potential of a monochromatic wave of
  wavenumber `κ`, phase `φ`, travelling at speed `𝓕.c`. -/
noncomputable def harmonicWaveAmp (𝓕 : FreeSpace) (κ φ : ℝ) (u : ℝ) : ℝ :=
  -1 / (κ * 𝓕.c.val) * Real.sin (-κ * u + φ)

lemma harmonicWaveAmp_smul_differentiable (𝓕 : FreeSpace) (κ φ : ℝ)
    (E₀ : EuclideanSpace ℝ (Fin d)) :
    Differentiable ℝ (fun u => harmonicWaveAmp 𝓕 κ φ u • E₀) := by
  unfold harmonicWaveAmp
  fun_prop

lemma harmonicWaveAmp_fderiv (𝓕 : FreeSpace) (κ φ u : ℝ) (hκ : κ ≠ 0) :
    fderiv ℝ (harmonicWaveAmp 𝓕 κ φ) u 1 = 1 / 𝓕.c.val * Real.cos (-κ * u + φ) := by
  unfold harmonicWaveAmp
  rw [fderiv_const_mul (by fun_prop)]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_sin (by fun_prop)]
  simp only [fderiv_add_const, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul (by fun_prop)]
  simp only [FunLike.coe_smul, Pi.smul_apply, fderiv_id', ContinuousLinearMap.coe_id',
    id_eq, smul_eq_mul, mul_one]
  field_simp
  ring

/-- The vector-valued derivative of the vector-potential amplitude `harmonicWaveAmp 𝓕 κ φ`
  scaled by `E₀`, i.e. the (up to a factor of `𝓕.c`) electric-field amplitude. -/
lemma harmonicWaveAmp_smul_fderiv (𝓕 : FreeSpace) (κ φ u : ℝ) (hκ : κ ≠ 0)
    (E₀ : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun u => harmonicWaveAmp 𝓕 κ φ u • E₀) u 1 =
    (1 / 𝓕.c.val * Real.cos (-κ * u + φ)) • E₀ := by
  rw [fderiv_smul_const (by unfold harmonicWaveAmp; fun_prop),
    ContinuousLinearMap.smulRight_apply, harmonicWaveAmp_fderiv 𝓕 κ φ u hκ]

/-- The scalar amplitude function of the electric field. -/
noncomputable def harmonicWaveEAmp (κ φ : ℝ) (u : ℝ) : ℝ :=
  Real.cos (-κ * u + φ)

lemma harmonicWaveEAmp_smul_differentiable (κ φ : ℝ) (E₀ : EuclideanSpace ℝ (Fin d)) :
    Differentiable ℝ (fun u => harmonicWaveEAmp κ φ u • E₀) := by
  unfold harmonicWaveEAmp
  fun_prop

lemma harmonicWaveEAmp_fderiv (κ φ u : ℝ) :
    fderiv ℝ (harmonicWaveEAmp κ φ) u 1 = κ * Real.sin (-κ * u + φ) := by
  unfold harmonicWaveEAmp
  rw [fderiv_cos (by fun_prop)]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_add_const, fderiv_const_mul (by fun_prop)]
  simp only [FunLike.coe_smul, Pi.smul_apply, fderiv_id', ContinuousLinearMap.coe_id',
    id_eq, smul_eq_mul, mul_one]
  ring

lemma harmonicWaveEAmp_smul_fderiv (κ φ u : ℝ) (E₀ : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun u => harmonicWaveEAmp κ φ u • E₀) u 1 =
    (κ * Real.sin (-κ * u + φ)) • E₀ := by
  rw [fderiv_smul_const (by unfold harmonicWaveEAmp; fun_prop),
    ContinuousLinearMap.smulRight_apply, harmonicWaveEAmp_fderiv κ φ u]

/-!

## B. The electromagnetic potential for a harmonic wave in direction `s`

-/

/-- The electromagnetic potential for a monochromatic, transversely-polarized plane wave of
  wavenumber `κ` and amplitude `E₀`, travelling in direction `s.unit` at speed `𝓕.c`. -/
noncomputable def harmonicWave (𝓕 : FreeSpace) (κ : ℝ) (s : Direction d)
    (E₀ : EuclideanSpace ℝ (Fin d)) (φ : ℝ) : ElectromagneticPotential d :=
  ofVectorPotential 𝓕.c (planeWave (fun u => harmonicWaveAmp 𝓕 κ φ u • E₀) 𝓕.c.val s)

lemma harmonicWave_differentiable (𝓕 : FreeSpace) (κ : ℝ) (s : Direction d)
    (E₀ : EuclideanSpace ℝ (Fin d)) (φ : ℝ) :
    Differentiable ℝ (harmonicWave 𝓕 κ s E₀ φ) := by
  unfold harmonicWave
  apply differentiable_ofVectorPotential
  unfold planeWave
  change Differentiable ℝ ((fun u => harmonicWaveAmp 𝓕 κ φ u • E₀) ∘
    fun (p : Time × Space d) => (inner ℝ p.2 s.unit - 𝓕.c.val * p.1 : ℝ))
  apply Differentiable.comp
  · exact harmonicWaveAmp_smul_differentiable 𝓕 κ φ E₀
  · apply Differentiable.sub
    · exact Differentiable.inner ℝ (by fun_prop) (by fun_prop)
    · fun_prop

lemma harmonicWave_contDiff (n : WithTop ℕ∞) (𝓕 : FreeSpace) (κ : ℝ) (s : Direction d)
    (E₀ : EuclideanSpace ℝ (Fin d)) (φ : ℝ) :
    ContDiff ℝ n (harmonicWave 𝓕 κ s E₀ φ) := by
  unfold harmonicWave
  apply contDiff_ofVectorPotential
  unfold planeWave
  change ContDiff ℝ n ((fun u => harmonicWaveAmp 𝓕 κ φ u • E₀) ∘
    fun (p : Time × Space d) => (inner ℝ p.2 s.unit - 𝓕.c.val * p.1 : ℝ))
  apply ContDiff.comp
  · show ContDiff ℝ n (fun u => harmonicWaveAmp 𝓕 κ φ u • E₀)
    unfold harmonicWaveAmp
    fun_prop
  · apply ContDiff.sub
    · exact ContDiff.inner (by fun_prop) (by fun_prop)
    · fun_prop

@[simp]
lemma harmonicWave_scalarPotential_eq_zero (𝓕 : FreeSpace) (κ : ℝ) (s : Direction d)
    (E₀ : EuclideanSpace ℝ (Fin d)) (φ : ℝ) :
    (harmonicWave 𝓕 κ s E₀ φ).scalarPotential 𝓕.c = 0 := by
  ext t x
  simp [harmonicWave, scalarPotential, ofVectorPotential, timeSlice]

@[simp]
lemma harmonicWave_vectorPotential (𝓕 : FreeSpace) (κ : ℝ) (s : Direction d)
    (E₀ : EuclideanSpace ℝ (Fin d)) (φ : ℝ) :
    (harmonicWave 𝓕 κ s E₀ φ).vectorPotential 𝓕.c =
    planeWave (fun u => harmonicWaveAmp 𝓕 κ φ u • E₀) 𝓕.c.val s :=
  ofVectorPotential_vectorPotential 𝓕.c _

/-!

## C. The electric field

-/

/-- The electric field of the harmonic wave, a transverse plane wave of amplitude `E₀`. -/
lemma harmonicWave_electricField (𝓕 : FreeSpace) (κ : ℝ) (hκ : κ ≠ 0) (s : Direction d)
    (E₀ : EuclideanSpace ℝ (Fin d)) (φ : ℝ) :
    (harmonicWave 𝓕 κ s E₀ φ).electricField 𝓕.c =
    planeWave (fun u => harmonicWaveEAmp κ φ u • E₀) 𝓕.c.val s := by
  ext t x
  rw [electricField_eq]
  simp only [harmonicWave_scalarPotential_eq_zero, Pi.zero_apply, Space.grad_zero, zero_sub]
  rw [harmonicWave_vectorPotential,
    planeWave_time_deriv (harmonicWaveAmp_smul_differentiable 𝓕 κ φ E₀)]
  simp only [Pi.neg_apply, neg_smul, neg_neg, planeWave_eq]
  rw [harmonicWaveAmp_smul_fderiv 𝓕 κ φ _ hκ E₀, smul_smul]
  congr 1
  unfold harmonicWaveEAmp
  field_simp

/-!

## D. The magnetic field matrix

-/

/-- The magnetic field matrix of the harmonic wave, expressed via the electric field
  (a general fact for any transverse plane-wave ansatz, independent of Maxwell's equations). -/
lemma harmonicWave_magneticFieldMatrix (𝓕 : FreeSpace) (κ : ℝ) (hκ : κ ≠ 0) (s : Direction d)
    (E₀ : EuclideanSpace ℝ (Fin d)) (φ : ℝ) (t : Time) (x : Space d) (i j : Fin d) :
    (harmonicWave 𝓕 κ s E₀ φ).magneticFieldMatrix 𝓕.c t x (i, j) =
    1 / 𝓕.c.val * (s.unit j * (harmonicWave 𝓕 κ s E₀ φ).electricField 𝓕.c t x i -
      s.unit i * (harmonicWave 𝓕 κ s E₀ φ).electricField 𝓕.c t x j) := by
  rw [magneticFieldMatrix_eq_vectorPotential _ (harmonicWave_differentiable 𝓕 κ s E₀ φ),
    harmonicWave_vectorPotential,
    planeWave_apply_space_deriv (harmonicWaveAmp_smul_differentiable 𝓕 κ φ E₀) j i,
    planeWave_apply_space_deriv (harmonicWaveAmp_smul_differentiable 𝓕 κ φ E₀) i j]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, planeWave_eq]
  rw [harmonicWaveAmp_smul_fderiv 𝓕 κ φ _ hκ E₀, harmonicWave_electricField 𝓕 κ hκ s E₀ φ]
  simp only [planeWave_eq, PiLp.smul_apply, smul_eq_mul]
  unfold harmonicWaveEAmp
  ring

/-!

## E. The harmonic wave is a plane wave

-/

lemma harmonicWave_isPlaneWave (𝓕 : FreeSpace) (κ : ℝ) (hκ : κ ≠ 0) (s : Direction d)
    (E₀ : EuclideanSpace ℝ (Fin d)) (φ : ℝ) :
    IsPlaneWave 𝓕 (harmonicWave 𝓕 κ s E₀ φ) s := by
  constructor
  · exact ⟨_, harmonicWave_electricField 𝓕 κ hκ s E₀ φ⟩
  · refine ⟨fun u ij => 1 / 𝓕.c.val *
      (s.unit ij.2 * harmonicWaveEAmp κ φ u * E₀ ij.1 -
        s.unit ij.1 * harmonicWaveEAmp κ φ u * E₀ ij.2), fun t x => ?_⟩
    ext ⟨i, j⟩
    rw [harmonicWave_magneticFieldMatrix 𝓕 κ hκ s E₀ φ t x i j,
      harmonicWave_electricField 𝓕 κ hκ s E₀ φ]
    simp [planeWave_eq]
    ring

/-!

## F. Gauss's law for the harmonic wave

-/

/-- Gauss's law (divergence-free electric field) for the harmonic wave, a consequence of
  transversality of the amplitude `E₀` to the propagation direction `s`. -/
lemma harmonicWave_div_electricField_eq_zero (𝓕 : FreeSpace) (κ : ℝ) (hκ : κ ≠ 0)
    (s : Direction d) (E₀ : EuclideanSpace ℝ (Fin d)) (hE₀ : ∑ i, s.unit i * E₀ i = 0) (φ : ℝ)
    (t : Time) (x : Space d) :
    Space.div (fun x => (harmonicWave 𝓕 κ s E₀ φ).electricField 𝓕.c t x) x = 0 := by
  rw [harmonicWave_electricField 𝓕 κ hκ s E₀ φ]
  unfold Space.div
  have key : ∀ i, ∂[i] (fun x =>
      planeWave (fun u => harmonicWaveEAmp κ φ u • E₀) 𝓕.c.val s t x i) x =
      κ * Real.sin (-κ * (⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) + φ) * (s.unit i * E₀ i) := by
    intro i
    rw [planeWave_apply_space_deriv (harmonicWaveEAmp_smul_differentiable κ φ E₀) i i]
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, planeWave_eq,
      harmonicWaveEAmp_smul_fderiv]
    ring
  simp only [key, ← Finset.mul_sum, hE₀, mul_zero]

end ElectromagneticPotential
end Electromagnetism
