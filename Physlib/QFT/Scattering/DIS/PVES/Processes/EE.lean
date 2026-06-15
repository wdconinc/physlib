/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.PVES.Interference.Basic
/-!

# PVES Electron-Electron Asymmetry Interfaces

This module introduces electron-electron (ee) beam-helicity asymmetry interfaces
and bridge theorems reducing `A_LR` to an interference-over-total ratio under
PVES neutral-current decomposition assumptions.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace PVES
namespace Processes
namespace EE

open Electroweak
open Interference

/-- Helicity-resolved ee cross-section proxy model. -/
structure CrossSectionModel where
  /-- Positive-helicity (right-handed) beam proxy. -/
  sigmaPlus : ℝ → ℝ → ℝ
  /-- Negative-helicity (left-handed) beam proxy. -/
  sigmaMinus : ℝ → ℝ → ℝ

/-- Beam-helicity asymmetry interface with denominator regularizer. -/
def beamHelicityAsymmetry
    (M : CrossSectionModel)
    (x y : ℝ)
    (epsilonReg : ℝ) : ℝ :=
  (M.sigmaPlus x y - M.sigmaMinus x y) /
    (|M.sigmaPlus x y + M.sigmaMinus x y| + epsilonReg)

/-- Nonnegativity of the regularized denominator under `0 ≤ epsilonReg`. -/
lemma beamHelicityAsymmetry_den_nonneg
    (M : CrossSectionModel)
    (x y epsilonReg : ℝ)
    (hReg : 0 ≤ epsilonReg) :
    0 ≤ |M.sigmaPlus x y + M.sigmaMinus x y| + epsilonReg := by
  have hAbs : 0 ≤ |M.sigmaPlus x y + M.sigmaMinus x y| := abs_nonneg _
  linarith

/-- Isolation assumptions on an ee cross-section model induced by a neutral-current
piecewise decomposition. -/
def IsolationAssumptions
    (D : NeutralCurrentDecomposition)
    (M : CrossSectionModel) : Prop :=
  HelicityInterferenceIsolationAssumptions D M.sigmaPlus M.sigmaMinus

/-- Bridge theorem: under helicity-interference isolation, `A_LR` is the
interference-over-total ratio with explicit `2` normalization factors. -/
lemma beamHelicityAsymmetry_eq_interferenceRatio_of_isolation
    (D : NeutralCurrentDecomposition)
    (M : CrossSectionModel)
    (x y epsilonReg : ℝ)
    (hIso : IsolationAssumptions D M) :
    beamHelicityAsymmetry M x y epsilonReg
      = (2 * D.gammaZInterference x y) /
          (|2 * (D.photon x y + D.zBoson x y)| + epsilonReg) := by
  have hPlus := hIso.plus_eq x y
  have hMinus := hIso.minus_eq x y
  have hNum : M.sigmaPlus x y - M.sigmaMinus x y = 2 * D.gammaZInterference x y := by
    linarith
  have hDenCore :
      M.sigmaPlus x y + M.sigmaMinus x y = 2 * (D.photon x y + D.zBoson x y) := by
    linarith
  simp [beamHelicityAsymmetry, hNum, hDenCore]

/-- Canonical ee cross-section model induced by Task 4's helicity-resolved
neutral-current decomposition. -/
def canonicalModelOfDecomposition
    (D : NeutralCurrentDecomposition) : CrossSectionModel where
  sigmaPlus := helicityResolvedTotal (canonicalHelicityModel D) true
  sigmaMinus := helicityResolvedTotal (canonicalHelicityModel D) false

lemma canonicalModel_isolationAssumptions
    (D : NeutralCurrentDecomposition) :
    IsolationAssumptions D (canonicalModelOfDecomposition D) := by
  simpa [IsolationAssumptions, canonicalModelOfDecomposition] using
    (canonicalIsolationAssumptions D)

/-- Canonical `A_LR` bridge from neutral-current decomposition to ee asymmetry. -/
lemma canonical_beamHelicityAsymmetry_eq_interferenceRatio
    (D : NeutralCurrentDecomposition)
    (x y epsilonReg : ℝ) :
    beamHelicityAsymmetry (canonicalModelOfDecomposition D) x y epsilonReg
      = (2 * D.gammaZInterference x y) /
          (|2 * (D.photon x y + D.zBoson x y)| + epsilonReg) := by
  exact beamHelicityAsymmetry_eq_interferenceRatio_of_isolation
    D
    (canonicalModelOfDecomposition D)
    x y epsilonReg
    (canonicalModel_isolationAssumptions D)

end EE
end Processes
end PVES
end DIS
end Scattering
end QFT
end Physlib
