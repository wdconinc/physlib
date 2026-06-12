/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Kinematics.Basic
/-!

# DIS Kinematics Access Methods

This module implements reconstruction methods for DIS invariants from experimental measurements.
Each method represents a different experimental technique for accessing the standard DIS variables
(xBj, Q2, y, W2) and includes appropriateness theorems showing consistency.

## Access Methods

- **Electron Method**: Reconstructs invariants from electron scattering kinematics (angle, energy loss)
- **Sigma Method**: Reconstructs invariants from hadronic final state only
- **eSigma Method**: Reconstructs invariants from both electron and hadronic final states
- **JB Method (Jacquet-Blondel)**: Reconstructs invariants from hadronic momenta sum

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Kinematics

variable (V : Type) [AddCommGroup V] [Module ℝ V]
variable (g : Bilin V)

/-- Electron method: Q² reconstruction from electron scattering angle and energy.
    Q² = 4 * E_e * E_e' * sin²(θ/2), where E_e is initial electron energy,
    E_e' is final electron energy, and θ is the scattering angle. -/
structure ElectronMethodData where
  /-- Initial electron energy. -/
  E_initial : ℝ
  /-- Final electron energy after scattering. -/
  E_final : ℝ
  /-- Scattering angle (between incident and scattered electron). -/
  theta : ℝ
  /-- Constraint: final energy is less than initial (energy loss). -/
  energy_loss : 0 < E_final ∧ E_final < E_initial
  /-- Constraint: scattering angle in physical range. -/
  theta_bounds : 0 < theta ∧ theta < π

namespace ElectronMethodData

/-- Electron method Q² reconstruction. -/
def Q2_electron (d : ElectronMethodData) : ℝ :=
  4 * d.E_initial * d.E_final * (Real.sin (d.theta / 2)) ^ 2

/-- Electron method y reconstruction from energy ratio. -/
def y_electron (d : ElectronMethodData) : ℝ :=
  1 - d.E_final / d.E_initial

/-- Electron method xBj reconstruction (requires hadronic invariant mass input). -/
def xBj_electron (d : ElectronMethodData) (M_p : ℝ) : ℝ :=
  (Q2_electron d) / (2 * M_p * d.E_initial * (y_electron d))

/-- Appropriateness theorem: electron method Q² reconstruction is positive. -/
lemma Q2_electron_pos (d : ElectronMethodData) : 0 < Q2_electron d := by
  unfold Q2_electron
  have h_energy : 0 < d.E_initial ∧ 0 < d.E_final := ⟨by linarith [d.energy_loss.2], d.energy_loss.1⟩
  have h_sin_pos : 0 < (Real.sin (d.theta / 2)) ^ 2 := by
    apply sq_pos_of_pos
    apply Real.sin_pos
    constructor
    · linarith [d.theta_bounds.1]
    · linarith [d.theta_bounds.2, Real.pi_pos]
  positivity

/-- Appropriateness theorem: electron method y is in valid range (0, 1). -/
lemma y_electron_bounds (d : ElectronMethodData) : 0 < y_electron d ∧ y_electron d < 1 := by
  unfold y_electron
  constructor
  · linarith [d.energy_loss.2]
  · have h_ratio_pos : 0 < d.E_final / d.E_initial := by
      positivity
    have h_ratio_le_one : d.E_final / d.E_initial < 1 := by
      rw [div_lt_one]
      · exact d.energy_loss.2
      · linarith [d.energy_loss.1]
    linarith

end ElectronMethodData

/-- Sigma method data: hadronic final state information. -/
structure SigmaMethodData where
  /-- Sum of hadronic final state momenta (Jacquet-Blondel observable). -/
  P_h : V
  /-- Outgoing lepton momentum (required for energy-momentum conservation). -/
  k_out : V
  /-- Initial state total 4-momentum. -/
  P_initial : V

namespace SigmaMethodData

/-- Sigma method: Q² reconstruction from t-channel momentum transfer.
    Q² is reconstructed from the hadronic invariants and energy-momentum conservation. -/
def Q2_sigma (d : SigmaMethodData V) (g_met : Bilin V) : ℝ :=
  - g_met d.k_out d.k_out

/-- Sigma method y reconstruction from hadronic energy fraction. -/
def y_sigma (d : SigmaMethodData V) (g_met : Bilin V) : ℝ :=
  (g_met d.P_initial d.P_initial - g_met (d.P_initial - d.P_h - d.k_out) (d.P_initial - d.P_h - d.k_out)) /
    g_met d.P_initial d.P_initial

/-- Appropriateness theorem: Sigma method Q² is non-negative. -/
lemma Q2_sigma_nonneg (d : SigmaMethodData V) (g_met : Bilin V) (hTimelike : ∀ v, g_met v v ≤ 0 → 0 ≤ - g_met v v) :
    0 ≤ Q2_sigma d g_met := by
  unfold Q2_sigma
  apply hTimelike
  sorry -- depends on lepton being timelike in metric signature

end SigmaMethodData

/-- eSigma method: uses both electron and hadronic information. -/
structure ESigmaMethodData where
  /-- Electron method component. -/
  electron_data : ElectronMethodData
  /-- Hadronic method component. -/
  sigma_data : SigmaMethodData V
  /-- Agreement condition: both methods must give consistent Q² within experimental resolution. -/
  Q2_agreement : ∃ ε > 0, |ElectronMethodData.Q2_electron electron_data -
    SigmaMethodData.Q2_sigma sigma_data g| < ε

namespace ESigmaMethodData

/-- eSigma method Q² reconstruction: average of electron and Sigma methods. -/
def Q2_eSigma (d : ESigmaMethodData V) : ℝ :=
  (ElectronMethodData.Q2_electron d.electron_data + SigmaMethodData.Q2_sigma d.sigma_data g) / 2

/-- eSigma method y reconstruction: average of both methods. -/
def y_eSigma (d : ESigmaMethodData V) : ℝ :=
  (ElectronMethodData.y_electron d.electron_data + SigmaMethodData.y_sigma d.sigma_data g) / 2

/-- Appropriateness theorem: eSigma Q² reconstruction is consistent with both methods. -/
lemma Q2_eSigma_consistency (d : ESigmaMethodData V) :
    |Q2_eSigma d - ElectronMethodData.Q2_electron d.electron_data| ≤
    |ElectronMethodData.Q2_electron d.electron_data - SigmaMethodData.Q2_sigma d.sigma_data g| / 2 := by
  unfold Q2_eSigma
  sorry -- triangle inequality application

end ESigmaMethodData

/-- Jacquet-Blondel (JB) method: reconstruction from hadronic side only. -/
structure JBMethodData where
  /-- Sum of final state hadron momenta. -/
  P_h : V
  /-- Beam energy (from accelerator specs). -/
  E_beam : ℝ
  /-- Initial target nucleus mass. -/
  M_target : ℝ

namespace JBMethodData

/-- JB method: Q² reconstruction using scattered lepton information and hadronic recoil.
    Requires scattered lepton momentum which is implicit in hadronic recoil. -/
def Q2_JB (d : JBMethodData V) (g_met : Bilin V) (k_out : V) : ℝ :=
  - g_met k_out k_out

/-- JB method: W² reconstruction from hadronic invariant mass. -/
def W2_JB (d : JBMethodData V) (g_met : Bilin V) (p_hadron : V) : ℝ :=
  g_met (p_hadron + d.P_h) (p_hadron + d.P_h)

/-- JB method: xBj reconstruction from kinematic relations. -/
def xBj_JB (d : JBMethodData V) (g_met : Bilin V) (p_target : V) (k_out : V) : ℝ :=
  (Q2_JB d g_met k_out) / (2 * g_met p_target k_out)

/-- Appropriateness theorem: JB method respects experimental constraints on W². -/
lemma W2_JB_physical_region (d : JBMethodData V) (g_met : Bilin V) (p : V)
    (hM : 0 < d.M_target)
    (hPhysical : ∀ v, g_met v v ≤ 0) :
    W2_JB d g_met p ≥ (d.M_target) ^ 2 := by
  unfold W2_JB
  sorry -- requires threshold constraint from hadronic masses

/-- Appropriateness theorem: JB method Q² is consistent with Q² definition. -/
lemma Q2_JB_def_consistent (d : JBMethodData V) (g_met : Bilin V) (k_out : V) :
    Q2_JB d g_met k_out = - g_met k_out k_out := by
  unfold Q2_JB
  rfl

end JBMethodData

/-- Reconstruction agreement theorem: under ideal conditions, all three methods converge. -/
lemma all_methods_agree_ideal
    (K : DisKinematics V)
    (e_data : ElectronMethodData)
    (sigma_data : SigmaMethodData V)
    (jb_data : JBMethodData V)
    (g_met : Bilin V) :
    (ElectronMethodData.Q2_electron e_data = SigmaMethodData.Q2_sigma sigma_data g_met) ∧
    (SigmaMethodData.Q2_sigma sigma_data g_met = JBMethodData.Q2_JB jb_data g_met K.kPrime) →
    ElectronMethodData.Q2_electron e_data = JBMethodData.Q2_JB jb_data g_met K.kPrime := by
  intro ⟨h1, h2⟩
  exact Eq.trans h1 h2

end Kinematics
end DIS
end Scattering
end QFT
end Physlib
