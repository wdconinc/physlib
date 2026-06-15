/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.PVES.Interference.Basic
public import Physlib.QFT.Scattering.DIS.Kinematics.Basic
/-!

# PVES Electron-Proton Asymmetry Interfaces

This module introduces electron-proton (ep) beam-helicity asymmetry interfaces
with hadronic weak-current assumptions and DIS-kinematics compatibility
contracts.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace PVES
namespace Processes
namespace EP

open Electroweak
open Interference
open Kinematics

variable (V : Type) [AddCommGroup V] [Module ℝ V]

/-- Contract that `(x, y)` is the DIS point extracted from process kinematics. -/
def IsDISObservablePoint
    (g : Kinematics.Bilin V)
    (K : Kinematics.DisKinematics V)
    (x y : ℝ) : Prop :=
  x = K.xBj g ∧ y = K.yInel g

/-- Hadronic weak-current assumptions used in ep PVES interfaces. -/
structure HadronicWeakCurrentAssumptions
    (g : Kinematics.Bilin V)
  (K : Kinematics.DisKinematics V) : Type where
  /-- Neutral weak current is conserved in the hadronic response model. -/
  weakCurrentConserved : Prop
  /-- Witness of weak-current conservation. -/
  hWeakCurrentConserved : weakCurrentConserved
  /-- Hadronic form-factor/structure-function response is available. -/
  hasResponseModel : Prop
  /-- Witness that a response model is available. -/
  hHasResponseModel : hasResponseModel
  /-- Response model is compatible with parity-violating neutral-current terms. -/
  parityViolatingCompatible : Prop
  /-- Witness of PV-compatible hadronic response. -/
  hParityViolatingCompatible : parityViolatingCompatible

/-- Helicity-resolved ep cross-section proxy model at DIS variables `(x, y)`. -/
structure CrossSectionModel
    (g : Kinematics.Bilin V)
    (K : Kinematics.DisKinematics V) where
  /-- Positive-helicity (right-handed) beam proxy. -/
  sigmaPlus : ℝ → ℝ → ℝ
  /-- Negative-helicity (left-handed) beam proxy. -/
  sigmaMinus : ℝ → ℝ → ℝ
  /-- Domain contract selecting kinematic points where the model is valid. -/
  pointCompatible : ℝ → ℝ → Prop
  /-- Compatibility witness with DIS kinematics. -/
  hPointCompatible : ∀ x y, pointCompatible x y → IsDISObservablePoint V g K x y

/-- ep beam-helicity asymmetry with denominator regularizer. -/
def beamHelicityAsymmetry
    {g : Kinematics.Bilin V}
    {K : Kinematics.DisKinematics V}
    (M : CrossSectionModel V g K)
    (x y : ℝ)
    (epsilonReg : ℝ) : ℝ :=
  (M.sigmaPlus x y - M.sigmaMinus x y) /
    (|M.sigmaPlus x y + M.sigmaMinus x y| + epsilonReg)

/-- Isolation assumptions for ep helicity channels induced by a neutral-current
piecewise decomposition. -/
def IsolationAssumptions
    {g : Kinematics.Bilin V}
    {K : Kinematics.DisKinematics V}
    (D : NeutralCurrentDecomposition)
    (M : CrossSectionModel V g K) : Prop :=
  HelicityInterferenceIsolationAssumptions D M.sigmaPlus M.sigmaMinus

/-- ep asymmetry bridge theorem parallel to the ee case, with hadronic and
kinematic compatibility assumptions explicit in the statement. -/
lemma beamHelicityAsymmetry_eq_interferenceRatio_of_isolation
    {g : Kinematics.Bilin V}
    {K : Kinematics.DisKinematics V}
    (D : NeutralCurrentDecomposition)
    (M : CrossSectionModel V g K)
    (x y epsilonReg : ℝ)
    (hHad : HadronicWeakCurrentAssumptions V g K)
    (hPoint : M.pointCompatible x y)
    (hIso : IsolationAssumptions V D M) :
    beamHelicityAsymmetry V M x y epsilonReg
      = (2 * D.gammaZInterference x y) /
          (|2 * (D.photon x y + D.zBoson x y)| + epsilonReg) := by
  have _hDIS : IsDISObservablePoint V g K x y := M.hPointCompatible x y hPoint
  have _hWeak := hHad.hWeakCurrentConserved
  have _hResp := hHad.hHasResponseModel
  have _hPV := hHad.hParityViolatingCompatible
  have hPlus := hIso.plus_eq x y
  have hMinus := hIso.minus_eq x y
  have hNum : M.sigmaPlus x y - M.sigmaMinus x y = 2 * D.gammaZInterference x y := by
    linarith
  have hDenCore :
      M.sigmaPlus x y + M.sigmaMinus x y = 2 * (D.photon x y + D.zBoson x y) := by
    linarith
  calc
    beamHelicityAsymmetry V M x y epsilonReg
        = (M.sigmaPlus x y - M.sigmaMinus x y)
            / (|M.sigmaPlus x y + M.sigmaMinus x y| + epsilonReg) := by
              rfl
    _ = (2 * D.gammaZInterference x y) /
          (|2 * (D.photon x y + D.zBoson x y)| + epsilonReg) := by
            simp [hNum, hDenCore]

/-- Canonical ep cross-section model induced by Task 4 decomposition and a
fixed DIS kinematic point. -/
def canonicalModelOfDecomposition
    (g : Kinematics.Bilin V)
    (K : Kinematics.DisKinematics V)
    (D : NeutralCurrentDecomposition) :
    CrossSectionModel V g K where
  sigmaPlus := helicityResolvedTotal (canonicalHelicityModel D) true
  sigmaMinus := helicityResolvedTotal (canonicalHelicityModel D) false
  pointCompatible := fun x y => IsDISObservablePoint V g K x y
  hPointCompatible := by
    intro x y hxy
    exact hxy

lemma canonicalModel_isolationAssumptions
    {g : Kinematics.Bilin V}
    {K : Kinematics.DisKinematics V}
    (D : NeutralCurrentDecomposition) :
    IsolationAssumptions V D (canonicalModelOfDecomposition V g K D) := by
  simpa [IsolationAssumptions, canonicalModelOfDecomposition] using
    (canonicalIsolationAssumptions D)

lemma canonical_beamHelicityAsymmetry_eq_interferenceRatio
    (g : Kinematics.Bilin V)
    (K : Kinematics.DisKinematics V)
    (D : NeutralCurrentDecomposition)
    (x y epsilonReg : ℝ)
    (hHad : HadronicWeakCurrentAssumptions V g K)
    (hPoint : IsDISObservablePoint V g K x y) :
    beamHelicityAsymmetry V (canonicalModelOfDecomposition V g K D) x y epsilonReg
      = (2 * D.gammaZInterference x y) /
          (|2 * (D.photon x y + D.zBoson x y)| + epsilonReg) := by
  exact beamHelicityAsymmetry_eq_interferenceRatio_of_isolation
    V
    D
    (canonicalModelOfDecomposition V g K D)
    x y epsilonReg
    hHad
    hPoint
    (canonicalModel_isolationAssumptions V D)

end EP
end Processes
end PVES
end DIS
end Scattering
end QFT
end Physlib
