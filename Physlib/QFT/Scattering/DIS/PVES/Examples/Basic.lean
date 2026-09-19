/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.PVES.Processes.EE
public import Physlib.QFT.Scattering.DIS.PVES.Processes.EP
/-!

# PVES Validation Examples

This module provides worked examples that instantiate the PVES interference and
beam-helicity asymmetry interfaces for ee and ep channels.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace PVES
namespace Examples

open Electroweak
open Processes
open Kinematics

/-- Toy neutral-current decomposition with constant channel pieces. -/
def toyDecomposition (photonVal zVal gammaZVal : ℝ) : NeutralCurrentDecomposition where
  photon := fun _x _y => photonVal
  zBoson := fun _x _y => zVal
  gammaZInterference := fun _x _y => gammaZVal

/-- ee sanity check: canonical bridge theorem is executable on a toy decomposition. -/
lemma ee_toy_bridge_example
    (photonVal zVal gammaZVal x y epsilonReg : ℝ) :
    EE.beamHelicityAsymmetry
        (EE.canonicalModelOfDecomposition (toyDecomposition photonVal zVal gammaZVal))
        x y epsilonReg
      = (2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg) := by
  simpa [toyDecomposition] using
    EE.canonical_beamHelicityAsymmetry_eq_interferenceRatio
      (toyDecomposition photonVal zVal gammaZVal) x y epsilonReg

variable (V : Type) [AddCommGroup V] [Module ℝ V]

/-- Toy hadronic assumptions record for ep interface tests. -/
def toyHadronicAssumptions
    (g : Kinematics.Bilin V)
    (K : Kinematics.DisKinematics V) :
    EP.HadronicWeakCurrentAssumptions V g K :=
  ⟨True, trivial, True, trivial, True, trivial⟩

/-- ep sanity check: canonical bridge theorem is executable at the DIS point
`(x, y) = (xBj, yInel)`. -/
lemma ep_toy_bridge_example
    (g : Kinematics.Bilin V)
    (K : Kinematics.DisKinematics V)
    (photonVal zVal gammaZVal epsilonReg : ℝ) :
    EP.beamHelicityAsymmetry
        V
        (EP.canonicalModelOfDecomposition V g K (toyDecomposition photonVal zVal gammaZVal))
        (K.xBj g)
        (K.yInel g)
        epsilonReg
      = (2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg) := by
  have hPoint :
      EP.IsDISObservablePoint V g K (K.xBj g) (K.yInel g) := by
    simp [EP.IsDISObservablePoint]
  simpa [toyDecomposition] using
    EP.canonical_beamHelicityAsymmetry_eq_interferenceRatio
      V g K (toyDecomposition photonVal zVal gammaZVal)
      (K.xBj g) (K.yInel g) epsilonReg
      (toyHadronicAssumptions V g K) hPoint

/-! ## Experiment-facing ep connection (EIC-style) -/

/-- Generic multiplicative experimental scaling (`beam polarization × dilution`). -/
def experimentalScale (beamPolarization dilution : ℝ) : ℝ :=
  beamPolarization * dilution

/-- EIC-style measured asymmetry interface using the ep PVES asymmetry at a DIS point. -/
def eicMeasuredAsymmetry
    (g : Kinematics.Bilin V)
    (K : Kinematics.DisKinematics V)
    (beamPolarization dilution : ℝ)
    (D : NeutralCurrentDecomposition)
    (epsilonReg : ℝ) : ℝ :=
  experimentalScale beamPolarization dilution *
    EP.beamHelicityAsymmetry
      V
      (EP.canonicalModelOfDecomposition V g K D)
      (K.xBj g)
      (K.yInel g)
      epsilonReg

/-- EIC-style bridge: measured asymmetry follows the ep interference ratio
up to beam-polarization and dilution scaling. -/
lemma eic_measuredAsymmetry_eq_interferenceRatio
    (g : Kinematics.Bilin V)
    (K : Kinematics.DisKinematics V)
    (beamPolarization dilution : ℝ)
    (photonVal zVal gammaZVal epsilonReg : ℝ) :
    eicMeasuredAsymmetry
        V
        g
        K
        beamPolarization
        dilution
        (toyDecomposition photonVal zVal gammaZVal)
        epsilonReg
      = (beamPolarization * dilution) *
          ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) := by
  simp [eicMeasuredAsymmetry, experimentalScale, ep_toy_bridge_example, mul_assoc]

/-! ## EIC lab-frame observable interface (`A_PV`) -/

/-- Lab-frame input bundle for EIC-style PV asymmetry parameterization. -/
structure EICLabFrameInputs where
  /-- Lepton beam polarization. -/
  beamPolarization : ℝ
  /-- Effective dilution/acceptance factor used in the measured asymmetry. -/
  dilution : ℝ
  /-- DIS hard scale entering the electroweak prefactor (typically `Q2`). -/
  hardScale : ℝ
  /-- Fermi constant used in the prefactor. -/
  fermiConstant : ℝ
  /-- Fine-structure constant used in the prefactor. -/
  alphaEM : ℝ
  /-- Effective weak-charge combination entering the asymmetry. -/
  weakChargeCombination : ℝ
  /-- Dimensionless lab-frame kinematic factor. -/
  labKinematicFactor : ℝ

/-- EIC-style electroweak prefactor in the lab-frame asymmetry model. -/
def eicLabPrefactor (I : EICLabFrameInputs) : ℝ :=
  (I.hardScale * I.fermiConstant) / (2 * Real.sqrt 2 * Real.pi * I.alphaEM)

/-- Lab-frame parity-violating asymmetry interface for EIC-style analyses. -/
def eicLabFrameAPV (I : EICLabFrameInputs) : ℝ :=
  experimentalScale I.beamPolarization I.dilution
    * eicLabPrefactor I * I.labKinematicFactor * I.weakChargeCombination

/-- If the lab-frame weak-charge times kinematic factor is identified with the
PVES interference ratio, then EIC lab-frame `A_PV` equals scaled prefactor times that ratio. -/
lemma eic_labFrameAPV_eq_scaledPrefactor_times_interferenceRatio
    (I : EICLabFrameInputs)
    (photonVal zVal gammaZVal epsilonReg : ℝ)
    (hMatch : I.labKinematicFactor * I.weakChargeCombination
      = (2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) :
    eicLabFrameAPV I
      = (experimentalScale I.beamPolarization I.dilution * eicLabPrefactor I)
          * ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) := by
  calc
    eicLabFrameAPV I
      = (experimentalScale I.beamPolarization I.dilution * eicLabPrefactor I)
          * (I.labKinematicFactor * I.weakChargeCombination) := by
            simp [eicLabFrameAPV, mul_assoc, mul_comm]
    _ = (experimentalScale I.beamPolarization I.dilution * eicLabPrefactor I)
          * ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) := by
            rw [hMatch]

/-- Bridge from the existing EIC measured-asymmetry model to the EIC lab-frame
expression under an explicit expression-matching hypothesis. -/
lemma eic_bridge_to_labFrame
    (g : Kinematics.Bilin V)
    (K : Kinematics.DisKinematics V)
    (I : EICLabFrameInputs)
    (photonVal zVal gammaZVal epsilonReg : ℝ)
    (hExpr :
      (I.beamPolarization * I.dilution) *
          ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg))
        = eicLabFrameAPV I) :
    eicMeasuredAsymmetry
        V
        g
        K
        I.beamPolarization
        I.dilution
        (toyDecomposition photonVal zVal gammaZVal)
        epsilonReg
      = eicLabFrameAPV I := by
  have hMeas :
      eicMeasuredAsymmetry
          V
          g
          K
          I.beamPolarization
          I.dilution
          (toyDecomposition photonVal zVal gammaZVal)
          epsilonReg
        = (I.beamPolarization * I.dilution) *
            ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) := by
    simpa using eic_measuredAsymmetry_eq_interferenceRatio
      (V := V)
      (g := g)
      (K := K)
      (beamPolarization := I.beamPolarization)
      (dilution := I.dilution)
      (photonVal := photonVal)
      (zVal := zVal)
      (gammaZVal := gammaZVal)
      (epsilonReg := epsilonReg)
  calc
    eicMeasuredAsymmetry
        V
        g
        K
        I.beamPolarization
        I.dilution
        (toyDecomposition photonVal zVal gammaZVal)
        epsilonReg
      = (I.beamPolarization * I.dilution) *
          ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) := hMeas
    _ = eicLabFrameAPV I := hExpr

end Examples
end PVES
end DIS
end Scattering
end QFT
end Physlib
