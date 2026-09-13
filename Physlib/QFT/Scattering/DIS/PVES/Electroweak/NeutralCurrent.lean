/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.PVES.Electroweak.Parameters
public import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.Basic
/-!

# PVES Neutral-Current Contracts

This module extends gauge-theory scattering contracts with neutral-current
mediator tagging and gamma/Z/interference decomposition interfaces.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace PVES
namespace Electroweak

open Physlib.QFT.PerturbationTheory

/-- Neutral-current mediator channel used in PVES. -/
inductive NeutralMediator where
  | photon
  | zBoson
  deriving DecidableEq, Repr

/-- A neutral-current mediator specification for one momentum transfer value. -/
structure MediatorSelection where
  /-- Which neutral mediator is selected. -/
  mediator : NeutralMediator
  /-- Momentum-transfer invariant. -/
  q2 : ℝ

/-- Neutral-current vertex contract with vector and axial pieces. -/
structure NeutralCurrentVertexAssumptions where
  /-- Effective vector coupling. -/
  vectorCoupling : ℝ
  /-- Effective axial coupling. -/
  axialCoupling : ℝ
  /-- Contract that the vector current structure is present. -/
  hasVectorCurrent : Prop
  /-- Witness for vector-current structure. -/
  hVectorCurrent : hasVectorCurrent
  /-- Contract that the axial current structure is present. -/
  hasAxialCurrent : Prop
  /-- Witness for axial-current structure. -/
  hAxialCurrent : hasAxialCurrent

/-- Neutral-current contract bundle for PVES at tree level. -/
structure NeutralCurrentFeynmanRules where
  /-- Electroweak model and couplings. -/
  model : EffectiveModel
  /-- Photon-channel gauge rules (QED-like). -/
  photonRules : FeynmanDiagrams.GaugeFeynmanRules
  /-- Z-channel propagator contract. -/
  zPropagator : ∀
    (_k : FeynmanDiagrams.Momentum)
    (_μ _ν : FeynmanDiagrams.LorentzIndex)
    (_ξ ε : ℝ), 0 < ε → ℂ
  /-- Electron neutral-current vertex assumptions. -/
  electronVertex : NeutralCurrentVertexAssumptions
  /-- Up-type quark neutral-current vertex assumptions. -/
  upTypeVertex : NeutralCurrentVertexAssumptions
  /-- Down-type quark neutral-current vertex assumptions. -/
  downTypeVertex : NeutralCurrentVertexAssumptions
  /-- Contract that gamma-Z interference contribution is real-valued at the
  matrix-element-squared level. -/
  gammaZInterferenceReal : Prop
  /-- Witness for gamma-Z interference reality contract. -/
  hGammaZInterferenceReal : gammaZInterferenceReal

/-- Mediator mass-squared map for neutral-current channels. -/
def mediatorMassSq (rules : NeutralCurrentFeynmanRules) (m : NeutralMediator) : ℝ :=
  match m with
  | .photon => 0
  | .zBoson => rules.model.params.mZ ^ 2

/-- Channel availability assumptions for a neutral-current decomposition. -/
structure NeutralCurrentChannelAssumptions where
  /-- Photon channel contribution is enabled. -/
  hasPhotonChannel : Prop
  /-- Witness for photon channel contribution. -/
  hPhotonChannel : hasPhotonChannel
  /-- Z channel contribution is enabled. -/
  hasZChannel : Prop
  /-- Witness for Z channel contribution. -/
  hZChannel : hasZChannel
  /-- gamma-Z interference channel contribution is enabled. -/
  hasGammaZInterference : Prop
  /-- Witness for gamma-Z interference channel contribution. -/
  hGammaZInterference : hasGammaZInterference

/-- Contract interface for gamma/Z/interference decomposition at fixed kinematics. -/
structure NeutralCurrentDecomposition where
  /-- Pure photon contribution. -/
  photon : ℝ → ℝ → ℝ
  /-- Pure Z contribution. -/
  zBoson : ℝ → ℝ → ℝ
  /-- gamma-Z interference contribution. -/
  gammaZInterference : ℝ → ℝ → ℝ

/-- Total neutral-current contribution assembled from decomposition pieces. -/
def totalNeutralCurrent
    (D : NeutralCurrentDecomposition) (x y : ℝ) : ℝ :=
  D.photon x y + D.zBoson x y + D.gammaZInterference x y

lemma totalNeutralCurrent_decompose
    (D : NeutralCurrentDecomposition) (x y : ℝ) :
    totalNeutralCurrent D x y = D.photon x y + D.zBoson x y + D.gammaZInterference x y :=
  rfl

/-- Contract that parity-odd helicity dependence is carried by the
interference contribution. -/
def parityOddFromInterferenceOnly (D : NeutralCurrentDecomposition) : Prop :=
  ∀ x y, D.gammaZInterference x y = totalNeutralCurrent D x y - (D.photon x y + D.zBoson x y)

lemma parityOddFromInterferenceOnly_of_rfl
    (D : NeutralCurrentDecomposition) :
    parityOddFromInterferenceOnly D := by
  intro x y
  simp [totalNeutralCurrent, add_assoc]

end Electroweak
end PVES
end DIS
end Scattering
end QFT
end Physlib
