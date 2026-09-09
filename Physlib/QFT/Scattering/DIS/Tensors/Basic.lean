/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Kinematics.Basic
/-!

# DIS Tensors

This module introduces tensor objects for inclusive DIS:

- A leptonic tensor model built from incoming and outgoing lepton momenta.
- An abstract hadronic tensor with explicit symmetry and current-conservation assumptions.
- A decomposition interface in terms of structure functions `F1` and `F2`.
- A uniqueness theorem for decomposition coefficients under probe-vector assumptions.
- Pointwise contraction lemmas used by later cross-section derivations.

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

/-- Assumptions on an abstract hadronic tensor. -/
structure Assumptions (g : Bilin V) (K : Kinematics.DisKinematics V) (W : Bilin V) : Type where
  /-- Placeholder proposition for Lorentz-covariant tensor structure assumptions. -/
  lorentzCovariant : Prop
  /-- Witness that the Lorentz-covariance proposition holds. -/
  hLorentzCovariant : lorentzCovariant
  /-- Current conservation in the first tensor slot. -/
  conserved_left : ∀ v : V, W K.q v = 0
  /-- Current conservation in the second tensor slot. -/
  conserved_right : ∀ v : V, W v K.q = 0
  /-- Symmetry of the hadronic tensor. -/
  symm : W.IsSymm

/-- Pointwise `F1`/`F2` decomposition relation for hadronic tensors. -/
def IsF1F2Decomposition
    (g : Bilin V) (K : Kinematics.DisKinematics V) (W : Bilin V) (F1 F2 : ℝ) : Prop :=
  ∀ v w : V, W v w = F1 * g v w + F2 * (g K.p v * g K.p w)

/-- One concrete representative built from `F1` and `F2` coefficients. -/
def fromF1F2
    (g : Bilin V) (K : Kinematics.DisKinematics V) (F1 F2 : ℝ) : Bilin V :=
  F1 • g + F2 • Bilin.rankOne g K.p K.p

lemma fromF1F2_isDecomposition
    (g : Bilin V) (K : Kinematics.DisKinematics V) (F1 F2 : ℝ) :
    IsF1F2Decomposition g K (fromF1F2 g K F1 F2) F1 F2 := by
  intro v w
  simp [fromF1F2, Bilin.rankOne_apply]

/-- Assumptions that separate `F1` and `F2` coefficients via probe vectors. -/
structure UniquenessAssumptions (g : Bilin V) (K : Kinematics.DisKinematics V) : Type where
  vF1 : V
  wF1 : V
  g_nonzero : g vF1 wF1 ≠ 0
  p_outer_zero : g K.p vF1 * g K.p wF1 = 0
  vF2 : V
  wF2 : V
  g_zero : g vF2 wF2 = 0
  p_outer_nonzero : g K.p vF2 * g K.p wF2 ≠ 0

lemma decomposition_unique
    (g : Bilin V) (K : Kinematics.DisKinematics V) (W : Bilin V)
    (F1 F2 F1' F2' : ℝ)
    (hW : IsF1F2Decomposition g K W F1 F2)
    (hW' : IsF1F2Decomposition g K W F1' F2')
    (hU : UniquenessAssumptions g K) :
    F1 = F1' ∧ F2 = F2' := by
  have hEqF1 :
      F1 * g hU.vF1 hU.wF1 + F2 * (g K.p hU.vF1 * g K.p hU.wF1)
        = F1' * g hU.vF1 hU.wF1 + F2' * (g K.p hU.vF1 * g K.p hU.wF1) := by
    calc
      F1 * g hU.vF1 hU.wF1 + F2 * (g K.p hU.vF1 * g K.p hU.wF1)
          = W hU.vF1 hU.wF1 := by simp [hW hU.vF1 hU.wF1]
      _ = F1' * g hU.vF1 hU.wF1 + F2' * (g K.p hU.vF1 * g K.p hU.wF1) := by
          simp [hW' hU.vF1 hU.wF1]
  have hEqF1' : F1 * g hU.vF1 hU.wF1 = F1' * g hU.vF1 hU.wF1 := by
    simpa [hU.p_outer_zero] using hEqF1
  have hMulF1 : (F1 - F1') * g hU.vF1 hU.wF1 = 0 := by
    linarith [hEqF1']
  have hF1 : F1 = F1' := by
    have hSub : F1 - F1' = 0 := (mul_eq_zero.mp hMulF1).resolve_right hU.g_nonzero
    exact sub_eq_zero.mp hSub

  have hEqF2 :
      F1 * g hU.vF2 hU.wF2 + F2 * (g K.p hU.vF2 * g K.p hU.wF2)
        = F1' * g hU.vF2 hU.wF2 + F2' * (g K.p hU.vF2 * g K.p hU.wF2) := by
    calc
      F1 * g hU.vF2 hU.wF2 + F2 * (g K.p hU.vF2 * g K.p hU.wF2)
          = W hU.vF2 hU.wF2 := by simp [hW hU.vF2 hU.wF2]
      _ = F1' * g hU.vF2 hU.wF2 + F2' * (g K.p hU.vF2 * g K.p hU.wF2) := by
          simp [hW' hU.vF2 hU.wF2]
  have hEqF2' :
      F2 * (g K.p hU.vF2 * g K.p hU.wF2) = F2' * (g K.p hU.vF2 * g K.p hU.wF2) := by
    simpa [hU.g_zero, hF1] using hEqF2
  have hMulF2 : (F2 - F2') * (g K.p hU.vF2 * g K.p hU.wF2) = 0 := by
    linarith [hEqF2']
  have hF2 : F2 = F2' := by
    have hSub : F2 - F2' = 0 := (mul_eq_zero.mp hMulF2).resolve_right hU.p_outer_nonzero
    exact sub_eq_zero.mp hSub

  exact ⟨hF1, hF2⟩

end Hadronic

namespace Contraction

variable {V}

open Kinematics
open Hadronic

/-- Pointwise scalar contraction proxy used to state contraction identities. -/
def contractAt (L W : Bilin V) (v w : V) : ℝ := L v w * W v w

lemma contractAt_withF1F2
    (g : Bilin V) (K : Kinematics.DisKinematics V) (L W : Bilin V)
    (F1 F2 : ℝ) (hW : IsF1F2Decomposition g K W F1 F2)
    (v w : V) :
    contractAt L W v w
      = L v w * (F1 * g v w + F2 * (g K.p v * g K.p w)) := by
  simp [contractAt, hW v w]

end Contraction

end Tensors
end DIS
end Scattering
end QFT
end Physlib
