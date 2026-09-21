/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Kinematics.Basic
public import Physlib.Meta.Linters.Sorry
/-!

# DIS Tensors

This module introduces tensor objects for inclusive DIS:

- A leptonic tensor model built from incoming and outgoing lepton momenta.
- Reflections of a bilinear form, used as concrete elements of the stabilizer of the
  kinematics inside the `g`-isometry group.
- An abstract hadronic tensor with explicit Lorentz-covariance, symmetry and
  current-conservation assumptions.
- The *transverse* basis `{-g + q ⊗ q / q², p_T ⊗ p_T}` and the decomposition interface in
  terms of structure functions `F1` and `F2` written against it.
- A uniqueness theorem for decomposition coefficients under probe-vector assumptions.
- Pointwise contraction lemmas used by later cross-section derivations.

## Conventions

Tensors are real bilinear forms `Bilin V := LinearMap.BilinForm ℝ V` on an abstract real
vector space `V`; `g` plays the role of the metric and carries no built-in signature. The
kinematic invariants follow `DIS.Kinematics`: `K.Q2 g = - g K.q K.q`, i.e. the metric
convention is `+---`, spacelike momentum transfer has `g K.q K.q < 0` and `Q² > 0`. All
transverse constructions divide by `g K.q K.q`, so they carry `g K.q K.q ≠ 0` as an explicit
hypothesis rather than assuming `Q² > 0`; the photoproduction limit `Q² = 0` is a legitimate
boundary case elsewhere in the repository.

The structure-function basis is the one of Callan-Gross (Phys. Rev. Lett. 22 (1969) 156) and
Collins, *Foundations of Perturbative QCD* (2011):

  `W^{μν} = F₁ (-g^{μν} + q^μ q^ν / q²) + (F₂ / (p·q)) p_T^μ p_T^ν`,
  `p_T^μ = p^μ - (p·q / q²) q^μ`.

Both basis tensors are individually transverse to `q` — that is the point of writing them
this way and it is what makes `F1` and `F2` well defined (`transverseMetric_conserved_left`,
`transverseMetric_conserved_right`, `pTransverse_orthogonal_q`). **The second coefficient
here is the literature's `F₂ / (p·q)`, not `F₂`**: the `1/(p·q)` normalization is not folded
into the basis, so that no statement in this module needs `g K.p K.q ≠ 0`.

## Status

`IsF1F2Decomposition` is still a definition rather than a consequence of covariance: the
exhaustion statement `exists_isF1F2Decomposition` is stated over concrete hypotheses but is
not proved here (one `sorry`). What *is* proved is that the transverse basis satisfies all of
`Assumptions` (`fromF1F2Assumptions`), that covariance in the sense of
`IsLorentzCovariant` has teeth (`covariant_spectator_offDiagonal_zero`), and that the
coefficients are unique (`decomposition_unique`).

The `Hadronic.Witness` section audits `IsLorentzCovariant` itself, since
`Assumptions.covariant` is the field that the critique of placeholder assumption bundles
named. Verdict: the predicate is **not vacuous** — `not_isLorentzCovariant_wWit` exhibits a
tensor that fails it — but it is **not a predicate of `W` alone**: on the one-dimensional
kinematics of `isLorentzCovariant_line` it holds for every bilinear form, because the
kinematic stabilizer is trivial there. Its strength is the size of that stabilizer, a
property of `(V, g, p, q)`. The same section supplies `uniquenessWit`, the first
instantiation of `UniquenessAssumptions`, which had never been shown inhabited.

The parity-violating `F₃ ε^{μναβ} p_α q_β / (2 p·q)` term is *not* included: on an abstract
`V` with only a bilinear form there is no orientation or volume form, and physlib's
`Relativity.Tensors.RealTensor.Metrics.LeviCivita` supplies `leviCivita4Int` only as a
component symbol on `Fin 4` indices of `realLorentzTensor`. Adding `F₃` honestly requires
first specializing this module to `Lorentz.Vector 3`.

-/

@[expose] public section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Tensors

variable (V : Type) [AddCommGroup V] [Module ℝ V]

abbrev Bilin := LinearMap.BilinForm ℝ V

namespace Bilin

variable {V}

/-- Rank-one bilinear form `(v,w) ↦ g(a,v) g(b,w)` derived from a background bilinear form `g`. -/
def rankOne (g : Bilin V) (a b : V) : Bilin V where
  toFun := fun v =>
    { toFun := fun w => g a v * g b w
      map_add' := by
        intro w₁ w₂
        simp [mul_add, map_add]
      map_smul' := by
        intro c w
        change g a v * g b (c • w) = c * (g a v * g b w)
        rw [map_smul]
        ring }
  map_add' := by
    intro v₁ v₂
    ext w
    simp [add_mul, map_add]
  map_smul' := by
    intro c v
    ext w
    change g a (c • v) * g b w = c * (g a v * g b w)
    rw [map_smul]
    ring

@[simp] lemma rankOne_apply (g : Bilin V) (a b v w : V) :
    rankOne g a b v w = g a v * g b w := rfl

/-- A rank-one form built from a single vector is symmetric. -/
lemma rankOne_isSymm (g : Bilin V) (a : V) : (rankOne g a a).IsSymm := by
  refine { eq := ?_ }
  intro v w
  simp [rankOne_apply, mul_comm]

/-- Expansion of a bilinear form on a pair of vectors each shifted along `u`. -/
lemma apply_sub_smul_pair (g : Bilin V) (u x y : V) (a b : ℝ) :
    g (x - a • u) (y - b • u)
      = g x y - b * g x u - a * g u y + a * b * g u u := by
  have h1 : g (x - a • u) = g x - a • g u := by
    rw [map_sub, map_smul]
  have h3 : ∀ z : V, g z (y - b • u) = g z y - b * g z u := by
    intro z
    rw [map_sub, map_smul, smul_eq_mul]
  rw [h1, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h3 x, h3 u]
  ring

/-- A linear endomorphism preserving the background form `g`. For `g` a Lorentz metric these
are exactly the (linear) Lorentz transformations. -/
def IsIsometry (g : Bilin V) (f : V →ₗ[ℝ] V) : Prop :=
  ∀ v w : V, g (f v) (f w) = g v w

/-- The identity map is a `g`-isometry. -/
lemma isIsometry_id (g : Bilin V) : IsIsometry g (LinearMap.id) := by
  intro v w
  simp

/-- Reflection of `V` in the `g`-orthogonal hyperplane to `u`, `v ↦ v - 2 (g u v / g u u) u`.
The definition is unconditional; it is a `g`-isometry when `g` is symmetric and
`g u u ≠ 0` (`reflect_isometry`), and degenerates to the identity when `g u u = 0`, since
`(0 : ℝ)⁻¹ = 0`. -/
noncomputable def reflect (g : Bilin V) (u : V) : V →ₗ[ℝ] V where
  toFun := fun v => v - (2 * (g u u)⁻¹ * g u v) • u
  map_add' := by
    intro v₁ v₂
    have h : 2 * (g u u)⁻¹ * g u (v₁ + v₂)
        = 2 * (g u u)⁻¹ * g u v₁ + 2 * (g u u)⁻¹ * g u v₂ := by
      rw [map_add]
      ring
    simp only [h, add_smul]
    abel
  map_smul' := by
    intro c v
    have h : 2 * (g u u)⁻¹ * g u (c • v) = c * (2 * (g u u)⁻¹ * g u v) := by
      rw [map_smul, smul_eq_mul]
      ring
    simp only [RingHom.id_apply, h, smul_sub, smul_smul]

@[simp] lemma reflect_apply (g : Bilin V) (u v : V) :
    reflect g u v = v - (2 * (g u u)⁻¹ * g u v) • u := rfl

/-- The reflection in `u` reverses `u`. -/
lemma reflect_apply_self (g : Bilin V) (u : V) (hu : g u u ≠ 0) :
    reflect g u u = -u := by
  have h : 2 * (g u u)⁻¹ * g u u = 2 := by
    rw [mul_assoc, inv_mul_cancel₀ hu, mul_one]
  rw [reflect_apply, h, two_smul]
  abel

/-- The reflection in `u` fixes every vector `g`-orthogonal to `u`. -/
lemma reflect_apply_of_orthogonal (g : Bilin V) (u v : V) (h : g u v = 0) :
    reflect g u v = v := by
  rw [reflect_apply, h, mul_zero, zero_smul, sub_zero]

/-- A reflection in a non-null direction is a `g`-isometry when `g` is symmetric. -/
lemma reflect_isometry (g : Bilin V) (hSymm : g.IsSymm) (u : V) (hu : g u u ≠ 0) :
    IsIsometry g (reflect g u) := by
  intro v w
  have hc : (g u u)⁻¹ * g u u = 1 := inv_mul_cancel₀ hu
  rw [reflect_apply, reflect_apply, apply_sub_smul_pair, hSymm.eq v u]
  linear_combination (4 * (g u u)⁻¹ * g u v * g u w) * hc

end Bilin

namespace Leptonic

variable {V}

open Kinematics

/-- A symmetric model leptonic tensor used in the inclusive DIS derivation. -/
def lMuNu (g : Bilin V) (K : Kinematics.DisKinematics V) : Bilin V :=
  Bilin.rankOne g K.k K.kPrime + Bilin.rankOne g K.kPrime K.k - (g K.k K.kPrime) • g

@[simp] lemma lMuNu_apply (g : Bilin V) (K : Kinematics.DisKinematics V) (v w : V) :
    lMuNu g K v w = g K.k v * g K.kPrime w + g K.kPrime v * g K.k w
      - g K.k K.kPrime * g v w := by
  simp [lMuNu, sub_eq_add_neg, add_assoc]

lemma lMuNu_isSymm (g : Bilin V) (K : Kinematics.DisKinematics V) (hSymm : g.IsSymm) :
    (lMuNu g K).IsSymm := by
  refine { eq := ?_ }
  intro v w
  have hg : ∀ x y : V, g x y = g y x := hSymm.eq
  simp [lMuNu_apply, hg, mul_comm, add_comm]

end Leptonic

namespace Hadronic

variable {V}

open Kinematics

/-!

## The `Q²` sign convention

`Kinematics.DisKinematics.Q2` is defined as `- g K.q K.q`. Every lemma below is stated in
terms of `g K.q K.q` directly, with `q_sq_eq_neg_Q2` available to translate.

-/

/-- The repository's hard-scale convention: `g q q = - Q²`. -/
lemma q_sq_eq_neg_Q2 (g : Bilin V) (K : DisKinematics V) :
    g K.q K.q = - K.Q2 g := by
  unfold Kinematics.DisKinematics.Q2
  ring

/-- `Q² ≠ 0` is the same hypothesis as `g q q ≠ 0`. -/
lemma q_sq_ne_zero_iff (g : Bilin V) (K : DisKinematics V) :
    g K.q K.q ≠ 0 ↔ K.Q2 g ≠ 0 := by
  rw [q_sq_eq_neg_Q2, neg_ne_zero]

/-!

## The transverse basis

-/

/-- The transverse metric projector `-g^{μν} + q^μ q^ν / q²`, written in the `+---`
convention of `Kinematics` (so the `q ⊗ q` coefficient is `(g q q)⁻¹ = -(Q²)⁻¹`). It is
transverse to `q` in both slots whenever `g q q ≠ 0`. -/
noncomputable def transverseMetric (g : Bilin V) (K : DisKinematics V) : Bilin V :=
  (-1 : ℝ) • g + (g K.q K.q)⁻¹ • Bilin.rankOne g K.q K.q

/-- Pointwise value of the transverse metric projector. -/
lemma transverseMetric_apply (g : Bilin V) (K : DisKinematics V) (v w : V) :
    transverseMetric g K v w = -g v w + (g K.q K.q)⁻¹ * (g K.q v * g K.q w) := by
  simp only [transverseMetric, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    Bilin.rankOne_apply]
  ring

/-- The transverse metric projector written with `Q² = - q²`, for comparison with the
literature form `-g^{μν} + q^μ q^ν / q²`. -/
lemma transverseMetric_apply_Q2 (g : Bilin V) (K : DisKinematics V) (v w : V) :
    transverseMetric g K v w = -g v w - (K.Q2 g)⁻¹ * (g K.q v * g K.q w) := by
  rw [transverseMetric_apply, q_sq_eq_neg_Q2, inv_neg]
  ring

/-- The transverse metric projector is transverse in the first slot. -/
lemma transverseMetric_conserved_left (g : Bilin V) (K : DisKinematics V)
    (hQ2 : g K.q K.q ≠ 0) (v : V) :
    transverseMetric g K K.q v = 0 := by
  rw [transverseMetric_apply, inv_mul_cancel_left₀ hQ2]
  ring

/-- The transverse metric projector is transverse in the second slot. This needs symmetry of
`g`: `transverseMetric` is symmetric only because `g` is. -/
lemma transverseMetric_conserved_right (g : Bilin V) (K : DisKinematics V)
    (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0) (v : V) :
    transverseMetric g K v K.q = 0 := by
  rw [transverseMetric_apply, hSymm.eq v K.q, mul_comm (g K.q v) (g K.q K.q),
    inv_mul_cancel_left₀ hQ2]
  ring

/-- The transverse metric projector is symmetric when `g` is. -/
lemma transverseMetric_isSymm (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm) :
    (transverseMetric g K).IsSymm := by
  refine { eq := ?_ }
  intro v w
  have hg : ∀ x y : V, g x y = g y x := hSymm.eq
  simp [transverseMetric_apply, hg, mul_comm]

/-- The transverse part of the hadron momentum, `p^μ - (p·q / q²) q^μ`. -/
noncomputable def pTransverse (g : Bilin V) (K : DisKinematics V) : V :=
  K.p - (g K.p K.q / g K.q K.q) • K.q

/-- Pointwise pairing of the transverse hadron momentum against a vector. -/
lemma pTransverse_pairing (g : Bilin V) (K : DisKinematics V) (v : V) :
    g (pTransverse g K) v = g K.p v - (g K.p K.q / g K.q K.q) * g K.q v := by
  simp only [pTransverse, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]

/-- The transverse hadron momentum is `g`-orthogonal to `q`. -/
lemma pTransverse_orthogonal_q (g : Bilin V) (K : DisKinematics V) (hQ2 : g K.q K.q ≠ 0) :
    g (pTransverse g K) K.q = 0 := by
  have h : g K.p K.q / g K.q K.q * g K.q K.q = g K.p K.q := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hQ2, mul_one]
  rw [pTransverse_pairing, h, sub_self]

/-!

## Lorentz covariance

Covariance of the hadronic tensor is the statement that `W` is built only out of `g`, `p` and
`q`: it is invariant under every `g`-isometry that fixes `p` and `q`. This replaces the
`lorentzCovariant : Prop` placeholder that previously stood in `Assumptions` and carried no
information (any such field is satisfiable by `True`).

-/

/-- A `g`-isometry fixing both hadron and probe momenta, i.e. an element of the stabilizer of
the kinematics inside the isometry group of `g`. -/
structure IsKinematicStabilizer (g : Bilin V) (K : DisKinematics V) (f : V →ₗ[ℝ] V) :
    Prop where
  /-- `f` preserves the background form. -/
  isometry : Bilin.IsIsometry g f
  /-- `f` fixes the hadron momentum. -/
  fixes_p : f K.p = K.p
  /-- `f` fixes the momentum transfer. -/
  fixes_q : f K.q = K.q

/-- Lorentz covariance of a hadronic tensor, stated concretely: `W` is invariant under every
`g`-isometry fixing `p` and `q`. -/
def IsLorentzCovariant (g : Bilin V) (K : DisKinematics V) (W : Bilin V) : Prop :=
  ∀ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f → ∀ v w : V, W (f v) (f w) = W v w

/-- Pairing against a vector fixed by a stabilizer element is invariant. -/
lemma pairing_invariant_of_fixed (g : Bilin V) (K : DisKinematics V) {f : V →ₗ[ℝ] V}
    (hf : IsKinematicStabilizer g K f) {a : V} (ha : f a = a) (v : V) :
    g a (f v) = g a v := by
  calc g a (f v) = g (f a) (f v) := by rw [ha]
    _ = g a v := hf.isometry a v

/-- A stabilizer element fixes the transverse hadron momentum. -/
lemma stabilizer_fixes_pTransverse (g : Bilin V) (K : DisKinematics V) {f : V →ₗ[ℝ] V}
    (hf : IsKinematicStabilizer g K f) :
    f (pTransverse g K) = pTransverse g K := by
  simp only [pTransverse, map_sub, map_smul, hf.fixes_p, hf.fixes_q]

/-- The transverse metric projector is Lorentz covariant. -/
lemma transverseMetric_isLorentzCovariant (g : Bilin V) (K : DisKinematics V) :
    IsLorentzCovariant g K (transverseMetric g K) := by
  intro f hf v w
  rw [transverseMetric_apply, transverseMetric_apply, hf.isometry v w,
    pairing_invariant_of_fixed g K hf hf.fixes_q v,
    pairing_invariant_of_fixed g K hf hf.fixes_q w]

/-- The transverse hadron rank-one tensor is Lorentz covariant. -/
lemma rankOne_pTransverse_isLorentzCovariant (g : Bilin V) (K : DisKinematics V) :
    IsLorentzCovariant g K (Bilin.rankOne g (pTransverse g K) (pTransverse g K)) := by
  intro f hf v w
  rw [Bilin.rankOne_apply, Bilin.rankOne_apply,
    pairing_invariant_of_fixed g K hf (stabilizer_fixes_pTransverse g K hf) v,
    pairing_invariant_of_fixed g K hf (stabilizer_fixes_pTransverse g K hf) w]

/-- Reflection in a spectator direction — a direction `g`-orthogonal to both `p` and `q` —
is an element of the kinematic stabilizer. This is the concrete supply of covariance
constraints used by `covariant_spectator_offDiagonal_zero`. -/
lemma reflect_isKinematicStabilizer (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm)
    (u : V) (hu : g u u ≠ 0) (hup : g u K.p = 0) (huq : g u K.q = 0) :
    IsKinematicStabilizer g K (Bilin.reflect g u) where
  isometry := Bilin.reflect_isometry g hSymm u hu
  fixes_p := Bilin.reflect_apply_of_orthogonal g u K.p hup
  fixes_q := Bilin.reflect_apply_of_orthogonal g u K.q huq

/-- **Covariance has content.** A Lorentz-covariant tensor has no mixed component between a
non-null spectator direction `u` and any vector `g`-orthogonal to `u`: the reflection in `u`
is a stabilizer element that reverses `u` and fixes `v`, so covariance forces
`W u v = - W u v`. This is the step that removes the `p^μ u^ν` and off-diagonal spectator
structures from a general symmetric conserved tensor. -/
theorem covariant_spectator_offDiagonal_zero (g : Bilin V) (K : DisKinematics V) (W : Bilin V)
    (hSymm : g.IsSymm) (hW : IsLorentzCovariant g K W) (u v : V) (hu : g u u ≠ 0)
    (hup : g u K.p = 0) (huq : g u K.q = 0) (huv : g u v = 0) :
    W u v = 0 := by
  have hf := reflect_isKinematicStabilizer g K hSymm u hu hup huq
  have h := hW (Bilin.reflect g u) hf u v
  rw [Bilin.reflect_apply_self g u hu, Bilin.reflect_apply_of_orthogonal g u v huv] at h
  have hneg : W (-u) v = -W u v := by simp
  rw [hneg] at h
  linarith

/-!

## The hadronic tensor and its `F1`/`F2` decomposition

-/

/-- Assumptions on an abstract hadronic tensor: Lorentz covariance in the concrete sense of
`IsLorentzCovariant`, current conservation in both slots, and symmetry (the parity-even,
electromagnetic case). -/
structure Assumptions (g : Bilin V) (K : DisKinematics V) (W : Bilin V) : Type where
  /-- Invariance under every `g`-isometry fixing `p` and `q`. -/
  covariant : IsLorentzCovariant g K W
  /-- Current conservation in the first tensor slot. -/
  conserved_left : ∀ v : V, W K.q v = 0
  /-- Current conservation in the second tensor slot. -/
  conserved_right : ∀ v : V, W v K.q = 0
  /-- Symmetry of the hadronic tensor. -/
  symm : W.IsSymm

/-- Pointwise `F1`/`F2` decomposition relation in the transverse basis. `F2` here carries the
literature's `1/(p·q)` normalization: it is `F₂/(p·q)`. -/
def IsF1F2Decomposition
    (g : Bilin V) (K : DisKinematics V) (W : Bilin V) (F1 F2 : ℝ) : Prop :=
  ∀ v w : V, W v w = F1 * transverseMetric g K v w
    + F2 * (g (pTransverse g K) v * g (pTransverse g K) w)

/-- One concrete representative built from `F1` and `F2` coefficients in the transverse
basis. `F2` carries the literature's `1/(p·q)` normalization. -/
noncomputable def fromF1F2
    (g : Bilin V) (K : DisKinematics V) (F1 F2 : ℝ) : Bilin V :=
  F1 • transverseMetric g K + F2 • Bilin.rankOne g (pTransverse g K) (pTransverse g K)

/-- Pointwise value of the transverse-basis representative. -/
lemma fromF1F2_apply (g : Bilin V) (K : DisKinematics V) (F1 F2 : ℝ) (v w : V) :
    fromF1F2 g K F1 F2 v w = F1 * transverseMetric g K v w
      + F2 * (g (pTransverse g K) v * g (pTransverse g K) w) := by
  simp only [fromF1F2, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    Bilin.rankOne_apply]

/-- The transverse-basis representative decomposes with the coefficients it was built from. -/
lemma fromF1F2_isDecomposition
    (g : Bilin V) (K : DisKinematics V) (F1 F2 : ℝ) :
    IsF1F2Decomposition g K (fromF1F2 g K F1 F2) F1 F2 := by
  intro v w
  rw [fromF1F2_apply]

/-- The transverse-basis representative is conserved in the first slot. -/
lemma fromF1F2_conserved_left (g : Bilin V) (K : DisKinematics V) (hQ2 : g K.q K.q ≠ 0)
    (F1 F2 : ℝ) (v : V) :
    fromF1F2 g K F1 F2 K.q v = 0 := by
  rw [fromF1F2_apply, transverseMetric_conserved_left g K hQ2 v,
    pTransverse_orthogonal_q g K hQ2]
  ring

/-- The transverse-basis representative is conserved in the second slot. -/
lemma fromF1F2_conserved_right (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm)
    (hQ2 : g K.q K.q ≠ 0) (F1 F2 : ℝ) (v : V) :
    fromF1F2 g K F1 F2 v K.q = 0 := by
  rw [fromF1F2_apply, transverseMetric_conserved_right g K hSymm hQ2 v,
    pTransverse_orthogonal_q g K hQ2]
  ring

/-- The transverse-basis representative is symmetric when `g` is. -/
lemma fromF1F2_isSymm (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm) (F1 F2 : ℝ) :
    (fromF1F2 g K F1 F2).IsSymm := by
  refine { eq := ?_ }
  intro v w
  have hg : ∀ x y : V, g x y = g y x := hSymm.eq
  simp [fromF1F2_apply, transverseMetric_apply, hg, mul_comm]

/-- The transverse-basis representative is Lorentz covariant. -/
lemma fromF1F2_isLorentzCovariant (g : Bilin V) (K : DisKinematics V) (F1 F2 : ℝ) :
    IsLorentzCovariant g K (fromF1F2 g K F1 F2) := by
  intro f hf v w
  rw [fromF1F2_apply, fromF1F2_apply, transverseMetric_isLorentzCovariant g K f hf v w,
    pairing_invariant_of_fixed g K hf (stabilizer_fixes_pTransverse g K hf) v,
    pairing_invariant_of_fixed g K hf (stabilizer_fixes_pTransverse g K hf) w]

/-- **`Assumptions` is instantiable in the transverse basis, for every pair of structure
functions.** This is the statement that fails in the non-transverse basis
`F1 • g + F2 • rankOne g p p`, where `conserved_left` forces `F1 = 0` and `F2 * g p q = 0`.
The only hypotheses are symmetry of `g` and `Q² ≠ 0`. -/
def fromF1F2Assumptions (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm)
    (hQ2 : g K.q K.q ≠ 0) (F1 F2 : ℝ) :
    Assumptions g K (fromF1F2 g K F1 F2) where
  covariant := fromF1F2_isLorentzCovariant g K F1 F2
  conserved_left := fromF1F2_conserved_left g K hQ2 F1 F2
  conserved_right := fromF1F2_conserved_right g K hSymm hQ2 F1 F2
  symm := fromF1F2_isSymm g K hSymm F1 F2

/-- Assumptions that separate `F1` and `F2` coefficients via probe vectors, stated against
the transverse basis: one pair of vectors sees the projector but not `p_T ⊗ p_T`, and one
pair does the reverse. -/
structure UniquenessAssumptions (g : Bilin V) (K : DisKinematics V) : Type where
  /-- First slot of the probe pair isolating `F1`. -/
  vF1 : V
  /-- Second slot of the probe pair isolating `F1`. -/
  wF1 : V
  /-- The `F1` probe pair sees the transverse projector. -/
  transverse_nonzero : transverseMetric g K vF1 wF1 ≠ 0
  /-- The `F1` probe pair does not see `p_T ⊗ p_T`. -/
  pT_outer_zero : g (pTransverse g K) vF1 * g (pTransverse g K) wF1 = 0
  /-- First slot of the probe pair isolating `F2`. -/
  vF2 : V
  /-- Second slot of the probe pair isolating `F2`. -/
  wF2 : V
  /-- The `F2` probe pair does not see the transverse projector. -/
  transverse_zero : transverseMetric g K vF2 wF2 = 0
  /-- The `F2` probe pair sees `p_T ⊗ p_T`. -/
  pT_outer_nonzero : g (pTransverse g K) vF2 * g (pTransverse g K) wF2 ≠ 0

/-- With probe vectors separating the two basis structures, a decomposition with
`(F1, F2) ≠ (0, 0)` is a non-zero tensor. Together with `fromF1F2Assumptions` this is the
non-triviality statement that the old, non-transverse basis could not support. -/
lemma fromF1F2_ne_zero (g : Bilin V) (K : DisKinematics V) (F1 F2 : ℝ)
    (hU : UniquenessAssumptions g K) (h : F1 ≠ 0 ∨ F2 ≠ 0) :
    fromF1F2 g K F1 F2 ≠ 0 := by
  intro hzero
  rcases h with hF1 | hF2
  · have h0 : fromF1F2 g K F1 F2 hU.vF1 hU.wF1 = 0 := by rw [hzero]; simp
    rw [fromF1F2_apply, hU.pT_outer_zero, mul_zero, add_zero] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hF1 h
    · exact hU.transverse_nonzero h
  · have h0 : fromF1F2 g K F1 F2 hU.vF2 hU.wF2 = 0 := by rw [hzero]; simp
    rw [fromF1F2_apply, hU.transverse_zero, mul_zero, zero_add] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hF2 h
    · exact hU.pT_outer_nonzero h

/-- **Uniqueness of the structure functions.** Given one probe pair that sees the transverse
projector but not `p_T ⊗ p_T`, and one pair that does the reverse, the coefficients of a
decomposition are pinned. Ported unchanged from the non-transverse basis: the argument only
uses non-degeneracy of the two structures, so only the witness fields are renamed. -/
lemma decomposition_unique
    (g : Bilin V) (K : DisKinematics V) (W : Bilin V)
    (F1 F2 F1' F2' : ℝ)
    (hW : IsF1F2Decomposition g K W F1 F2)
    (hW' : IsF1F2Decomposition g K W F1' F2')
    (hU : UniquenessAssumptions g K) :
    F1 = F1' ∧ F2 = F2' := by
  have hEqF1 :
      F1 * transverseMetric g K hU.vF1 hU.wF1
          + F2 * (g (pTransverse g K) hU.vF1 * g (pTransverse g K) hU.wF1)
        = F1' * transverseMetric g K hU.vF1 hU.wF1
          + F2' * (g (pTransverse g K) hU.vF1 * g (pTransverse g K) hU.wF1) := by
    calc
      F1 * transverseMetric g K hU.vF1 hU.wF1
          + F2 * (g (pTransverse g K) hU.vF1 * g (pTransverse g K) hU.wF1)
          = W hU.vF1 hU.wF1 := by simp [hW hU.vF1 hU.wF1]
      _ = F1' * transverseMetric g K hU.vF1 hU.wF1
          + F2' * (g (pTransverse g K) hU.vF1 * g (pTransverse g K) hU.wF1) := by
          simp [hW' hU.vF1 hU.wF1]
  have hEqF1' : F1 * transverseMetric g K hU.vF1 hU.wF1
      = F1' * transverseMetric g K hU.vF1 hU.wF1 := by
    simpa [hU.pT_outer_zero] using hEqF1
  have hMulF1 : (F1 - F1') * transverseMetric g K hU.vF1 hU.wF1 = 0 := by
    linarith [hEqF1']
  have hF1 : F1 = F1' := by
    have hSub : F1 - F1' = 0 :=
      (mul_eq_zero.mp hMulF1).resolve_right hU.transverse_nonzero
    exact sub_eq_zero.mp hSub

  have hEqF2 :
      F1 * transverseMetric g K hU.vF2 hU.wF2
          + F2 * (g (pTransverse g K) hU.vF2 * g (pTransverse g K) hU.wF2)
        = F1' * transverseMetric g K hU.vF2 hU.wF2
          + F2' * (g (pTransverse g K) hU.vF2 * g (pTransverse g K) hU.wF2) := by
    calc
      F1 * transverseMetric g K hU.vF2 hU.wF2
          + F2 * (g (pTransverse g K) hU.vF2 * g (pTransverse g K) hU.wF2)
          = W hU.vF2 hU.wF2 := by simp [hW hU.vF2 hU.wF2]
      _ = F1' * transverseMetric g K hU.vF2 hU.wF2
          + F2' * (g (pTransverse g K) hU.vF2 * g (pTransverse g K) hU.wF2) := by
          simp [hW' hU.vF2 hU.wF2]
  have hEqF2' :
      F2 * (g (pTransverse g K) hU.vF2 * g (pTransverse g K) hU.wF2)
        = F2' * (g (pTransverse g K) hU.vF2 * g (pTransverse g K) hU.wF2) := by
    simpa [hU.transverse_zero, hF1] using hEqF2
  have hMulF2 :
      (F2 - F2') * (g (pTransverse g K) hU.vF2 * g (pTransverse g K) hU.wF2) = 0 := by
    linarith [hEqF2']
  have hF2 : F2 = F2' := by
    have hSub : F2 - F2' = 0 :=
      (mul_eq_zero.mp hMulF2).resolve_right hU.pT_outer_nonzero
    exact sub_eq_zero.mp hSub

  exact ⟨hF1, hF2⟩

/-!

## Exhaustion: covariance and conservation leave exactly two structures

The statement below is the honest version of K1: it asserts that `IsF1F2Decomposition` is a
*consequence* of `Assumptions`, not a definition users must posit. It is not proved here.

Note that exhaustion is false for an arbitrary abstract `V` and `g`: if the stabilizer of the
kinematics is trivial then `IsLorentzCovariant` is vacuous and any conserved symmetric `W`
qualifies. The three linear-algebra inputs that make the argument go through are collected in
`SpectatorAssumptions`; they hold for `V = Lorentz.Vector 3` with `g` the Minkowski form, `p`
timelike and `q` spacelike, and none of them is the conclusion.

-/

/-- Linear-algebra inputs about the spectator subspace `{p, q}^⊥` needed to turn covariance
plus conservation into the two-structure decomposition. These are facts about `g`, `p`, `q`
and the isometry group — not about the hadronic tensor. -/
structure SpectatorAssumptions (g : Bilin V) (K : DisKinematics V) : Type where
  /-- Every vector splits into a transverse-hadron part, a longitudinal `q` part, and a
  spectator part orthogonal to both. -/
  span : ∀ v : V, ∃ (a b : ℝ) (u : V), g K.q u = 0 ∧ g (pTransverse g K) u = 0 ∧
    v = a • pTransverse g K + b • K.q + u
  /-- The spectator subspace is negative definite — spacelike, in the `+---` convention of
  `Kinematics`. In particular every non-zero spectator direction is non-null, so
  `Bilin.reflect` supplies a stabilizer element for it. -/
  definite : ∀ u : V, g K.q u = 0 → g (pTransverse g K) u = 0 → u ≠ 0 → g u u < 0
  /-- Witt-type transitivity: the kinematic stabilizer acts transitively on spectator
  vectors of equal norm. -/
  transitive : ∀ u u' : V, g K.q u = 0 → g (pTransverse g K) u = 0 →
    g K.q u' = 0 → g (pTransverse g K) u' = 0 → g u u = g u' u' →
    ∃ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f ∧ f u = u'

/-- **Open target (K1).** Lorentz covariance, current conservation and symmetry leave exactly
the two transverse structures, so the `F1`/`F2` decomposition is a theorem rather than an
interface.

The intended proof: `conserved_left`/`conserved_right` kill the `q` component, so `W` is
determined by its restriction to `span {p_T} ⊕ {p,q}^⊥`;
`covariant_spectator_offDiagonal_zero` (with `definite` supplying non-null spectator
directions) kills the mixed `p_T`-spectator and off-diagonal spectator components;
`transitive` plus homogeneity of degree two forces `W u u = F1 * (- g u u)` with a single
constant `F1` on the spectator subspace, which is `F1 * transverseMetric` there since
`g K.q u = 0`; the remaining `p_T ⊗ p_T` component defines `F2`; `span` assembles the
pointwise identity. -/
-- TODO(task/k1-hadronic-tensor): the four steps above are each short but need a polarization
-- identity and a scaling argument that we could not write down with confidence without a
-- toolchain; the `transitive` and `definite` hypotheses may also need strengthening (for
-- instance to a statement about reflections generating the spectator isometry group) once
-- the proof is attempted. Nothing downstream depends on this lemma: `fromF1F2Assumptions`
-- and `decomposition_unique` are the load-bearing results.
@[sorryful]
theorem exists_isF1F2Decomposition (g : Bilin V) (K : DisKinematics V) (W : Bilin V)
    (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0) (hS : SpectatorAssumptions g K)
    (hA : Assumptions g K W) :
    ∃ F1 F2 : ℝ, IsF1F2Decomposition g K W F1 F2 := by
  sorry

/-!

## Audit of `IsLorentzCovariant`: what the predicate does and does not assert

`Hadronic.Assumptions.covariant` is the field that the critique of placeholder assumption
bundles named. The section above asserts in prose that it "has teeth" and that it degenerates
when the kinematic stabilizer is trivial. Neither claim was backed by a witness, so neither
was checked. This section settles both by construction, and the verdict is:

**`IsLorentzCovariant` is a genuine predicate, not a vacuous one — but it is not a predicate
of `W` alone. Its strength is exactly the size of the kinematic stabilizer, which is a
property of `(V, g, p, q)` and not of `W`.** Concretely:

* `not_isLorentzCovariant_wWit` exhibits `(V, g, K, W)` where the predicate **fails**. So it
  is not satisfiable by every `W` and is therefore not vacuous. This is the test a vacuous
  field cannot pass: `foo : Prop` paired with `hFoo : foo` admits `foo := True`, and no
  witness of failure exists for it. One does here.
* `isLorentzCovariant_line` exhibits kinematics on which the predicate holds for **every**
  bilinear form, because the stabilizer there is the identity alone
  (`stabilizer_line_eq_id`). So the predicate is *conditionally* uninformative, exactly as
  the `exists_isF1F2Decomposition` docstring claims in prose — now as a theorem.

Both witnesses use the same `+---`-signature construction restricted to one time and two
space directions, `ℝ × ℝ × ℝ` with `g (v₀,v₁,v₂) (w₀,w₁,w₂) = v₀w₀ - v₁w₁ - v₂w₂`, which is
the smallest space carrying a timelike `p`, a spacelike `q` orthogonal to it, and one
spectator direction — the minimum needed for `covariant_spectator_offDiagonal_zero` to bite.

The same construction settles a second open question at no extra cost: `uniquenessWit`
instantiates `UniquenessAssumptions`, which nothing in the repository previously did. Until
now `decomposition_unique` and `fromF1F2_ne_zero` were conditioned on a hypothesis not known
to be satisfiable; had it been empty, both would have been vacuously true statements about
nothing.

-/

namespace Witness

/-- The `+--` Minkowski form on `ℝ × ℝ × ℝ`, one time and two space directions:
`g v w = v₀w₀ - v₁w₁ - v₂w₂`. This is the `Kinematics` sign convention, restricted to the
smallest dimension that admits a spectator direction. -/
def gWit : Bilin (ℝ × ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun v w => v.1 * w.1 - v.2.1 * w.2.1 - v.2.2 * w.2.2)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

@[simp] lemma gWit_apply (v w : ℝ × ℝ × ℝ) :
    gWit v w = v.1 * w.1 - v.2.1 * w.2.1 - v.2.2 * w.2.2 := rfl

/-- `gWit` is symmetric, as a metric must be. -/
lemma gWit_isSymm : gWit.IsSymm := by
  refine { eq := ?_ }
  intro v w
  simp only [gWit_apply]
  ring

/-- Witness kinematics: timelike hadron momentum `p = (1,0,0)` and spacelike momentum
transfer `q = (0,1,0)`, orthogonal to `p`, which leaves `(0,0,1)` as a spectator direction
orthogonal to both. Here `g q q = -1`, so `Q² = 1 > 0`, the physical DIS sign. -/
def kWit : DisKinematics (ℝ × ℝ × ℝ) where
  p := (1, 0, 0)
  pPrime := 0
  k := (0, 1, 0)
  kPrime := 0
  q := (0, 1, 0)
  hq := by simp

@[simp] lemma kWit_p : kWit.p = ((1, 0, 0) : ℝ × ℝ × ℝ) := rfl

@[simp] lemma kWit_q : kWit.q = ((0, 1, 0) : ℝ × ℝ × ℝ) := rfl

/-- The off-diagonal spectator-hadron structure `W v w = v₂ w₀`, i.e. `u^μ p^ν` for `u` the
spectator direction. This is precisely one of the structures that Lorentz covariance is
supposed to forbid in the hadronic tensor, so it is the natural candidate for a failure
witness. -/
def wWit : Bilin (ℝ × ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun v w => v.2.2 * w.1)
    (fun _ _ _ => by simp only [Prod.snd_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_snd, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Prod.fst_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, smul_eq_mul]; ring)

@[simp] lemma wWit_apply (v w : ℝ × ℝ × ℝ) : wWit v w = v.2.2 * w.1 := rfl

/-- **`IsLorentzCovariant` is not vacuous: here is a tensor that fails it.** The spectator
direction `u = (0,0,1)` is non-null and orthogonal to both `p` and `q`, so reflection in it
is a kinematic stabilizer element; covariance would then force the mixed component
`W u p` to vanish, but `wWit u p = 1`.

This is the decisive test for a placeholder field. A field of the form `foo : Prop` together
with `hFoo : foo` admits `foo := True`, so no instantiation can ever fail it and no witness
like this one exists. That `IsLorentzCovariant` has one settles the question the assumption
bundle critique raised about `Assumptions.covariant`: the field asserts something. -/
theorem not_isLorentzCovariant_wWit : ¬ IsLorentzCovariant gWit kWit wWit := by
  intro hW
  have h : wWit ((0, 0, 1) : ℝ × ℝ × ℝ) ((1, 0, 0) : ℝ × ℝ × ℝ) = 0 :=
    covariant_spectator_offDiagonal_zero gWit kWit wWit gWit_isSymm hW (0, 0, 1) (1, 0, 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h

/-- Corollary: `Hadronic.Assumptions` is not satisfied by every symmetric conserved tensor,
because its `covariant` field alone already rules `wWit` out. -/
lemma not_assumptions_wWit : ¬ Assumptions gWit kWit wWit := by
  intro hA
  exact not_isLorentzCovariant_wWit hA.covariant

/-- **`UniquenessAssumptions` is satisfiable.** The `F1` probe is the spectator pair
`(u, u)`, which sees the transverse projector (`g u u = -1`) but is orthogonal to `p_T`; the
`F2` probe is the null pair `(n, n)` with `n = (1,0,1)`, for which the projector value
`-n₀² + n₂² ` vanishes while `g p_T n = 1`.

Without a witness of this kind, `decomposition_unique` and `fromF1F2_ne_zero` were
conditioned on a structure not known to be inhabited. -/
def uniquenessWit : UniquenessAssumptions gWit kWit where
  vF1 := (0, 0, 1)
  wF1 := (0, 0, 1)
  transverse_nonzero := by rw [transverseMetric_apply]; norm_num
  pT_outer_zero := by simp only [pTransverse_pairing]; norm_num
  vF2 := (1, 0, 1)
  wF2 := (1, 0, 1)
  transverse_zero := by rw [transverseMetric_apply]; norm_num
  pT_outer_nonzero := by simp only [pTransverse_pairing]; norm_num

/-!

### The other side: covariance is only as strong as the stabilizer

-/

/-- If the identity is the only element of the kinematic stabilizer, then every bilinear form
is Lorentz covariant, so the predicate carries no information about `W`. This is the precise
form of the caveat recorded in prose on `exists_isF1F2Decomposition`. -/
lemma isLorentzCovariant_of_stabilizer_eq_id (g : Bilin V) (K : DisKinematics V)
    (hTriv : ∀ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f → f = LinearMap.id)
    (W : Bilin V) :
    IsLorentzCovariant g K W := by
  intro f hf v w
  rw [hTriv f hf]
  simp

/-- The multiplication form on the line. -/
def gLine : Bilin ℝ :=
  LinearMap.mk₂ ℝ (fun v w => v * w)
    (fun _ _ _ => by ring)
    (fun _ _ _ => by simp only [smul_eq_mul]; ring)
    (fun _ _ _ => by ring)
    (fun _ _ _ => by simp only [smul_eq_mul]; ring)

@[simp] lemma gLine_apply (v w : ℝ) : gLine v w = v * w := rfl

/-- Degenerate one-dimensional kinematics, `p = q = 1`. There is no spectator direction. -/
def kLine : DisKinematics ℝ where
  p := 1
  pPrime := 0
  k := 1
  kPrime := 0
  q := 1
  hq := by norm_num

/-- On the line, a kinematic stabilizer element is the identity: it fixes `p = 1`, and `1`
spans. Note that the isometry field is not even needed. -/
lemma stabilizer_line_eq_id (f : ℝ →ₗ[ℝ] ℝ) (hf : IsKinematicStabilizer gLine kLine f) :
    f = LinearMap.id := by
  have h1 : f 1 = 1 := hf.fixes_q
  ext x
  show f x = x
  calc f x = f (x • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
    _ = x • f 1 := map_smul f x 1
    _ = x := by rw [h1, smul_eq_mul, mul_one]

/-- **`IsLorentzCovariant` is uninformative on these kinematics: every bilinear form
satisfies it.** Together with `not_isLorentzCovariant_wWit` this pins the verdict — the
predicate is neither vacuous nor a constraint on `W` alone. It is a constraint on `W`
*relative to a stabilizer group*, and it is empty exactly when that group is trivial. Any
downstream use of `Assumptions.covariant` therefore carries an unstated dependence on the
ambient geometry, which is what `SpectatorAssumptions` exists to supply. -/
lemma isLorentzCovariant_line (W : Bilin ℝ) : IsLorentzCovariant gLine kLine W :=
  isLorentzCovariant_of_stabilizer_eq_id gLine kLine stabilizer_line_eq_id W

end Witness

end Hadronic

namespace Contraction

variable {V}

open Kinematics
open Hadronic

/-- Pointwise scalar contraction proxy used to state contraction identities. -/
def contractAt (L W : Bilin V) (v w : V) : ℝ := L v w * W v w

/-- The leptonic-hadronic contraction of a decomposed hadronic tensor, in the transverse
basis. -/
lemma contractAt_withF1F2
    (g : Bilin V) (K : Kinematics.DisKinematics V) (L W : Bilin V)
    (F1 F2 : ℝ) (hW : IsF1F2Decomposition g K W F1 F2)
    (v w : V) :
    contractAt L W v w
      = L v w * (F1 * transverseMetric g K v w
        + F2 * (g (pTransverse g K) v * g (pTransverse g K) w)) := by
  simp [contractAt, hW v w]

end Contraction

end Tensors
end DIS
end Scattering
end QFT
end Physlib
