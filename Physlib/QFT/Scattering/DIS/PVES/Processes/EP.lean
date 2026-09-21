/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.PVES.Interference.Basic
public import Physlib.QFT.Scattering.DIS.Kinematics.Basic
public import Physlib.QFT.Scattering.DIS.Tensors.Basic
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

/-- Conservation of the hadronic neutral weak current, as a statement about an explicit
hadronic tensor `W`.

Two deliberate choices:

* `W` is an argument.  The previous version of this structure took only `g` and `K` and
  carried three `Prop`-plus-witness field pairs (`weakCurrentConserved`,
  `hasResponseModel`, `parityViolatingCompatible`).  That form is not a hypothesis at all:
  `Examples.toyHadronicAssumptions` instantiated it as `⟨True, trivial, True, trivial,
  True, trivial⟩`, which is available for every `g` and `K`.
* There is no symmetry field.  `Tensors.Hadronic.Assumptions` assumes `W.IsSymm`, which is
  the parity-even electromagnetic case; the neutral weak hadronic tensor carries the
  parity-odd `F₃` structure and is not symmetric, so assuming symmetry here would assume
  away the effect being measured.

The two fields that had no honest statement at this fidelity, `hasResponseModel` and
`parityViolatingCompatible`, are dropped rather than restated: nothing in this module has a
structure-function decomposition to which they could refer. -/
structure HadronicWeakCurrentAssumptions
    (g : Kinematics.Bilin V)
    (K : Kinematics.DisKinematics V)
    (W : Kinematics.Bilin V) : Prop where
  /-- Current conservation in the first tensor slot, `q_μ W^{μν} = 0`. -/
  conserved_left : ∀ v : V, W K.q v = 0
  /-- Current conservation in the second tensor slot, `W^{μν} q_ν = 0`. -/
  conserved_right : ∀ v : V, W v K.q = 0

/-- The parity-even electromagnetic assumptions of `Tensors.Hadronic` are strictly stronger:
they imply weak-current conservation, and additionally impose covariance and symmetry. -/
lemma HadronicWeakCurrentAssumptions.of_hadronicAssumptions
    {g : Kinematics.Bilin V} {K : Kinematics.DisKinematics V} {W : Kinematics.Bilin V}
    (h : Tensors.Hadronic.Assumptions g K W) :
    HadronicWeakCurrentAssumptions V g K W :=
  ⟨h.conserved_left, h.conserved_right⟩

/-- The assumptions have content: a tensor that is nonzero against `q` in the first slot
fails them. -/
lemma not_hadronicWeakCurrentAssumptions_of_ne_zero
    {g : Kinematics.Bilin V} {K : Kinematics.DisKinematics V} {W : Kinematics.Bilin V}
    {v : V} (hv : W K.q v ≠ 0) :
    ¬ HadronicWeakCurrentAssumptions V g K W :=
  fun h => hv (h.conserved_left v)

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

/-- ep asymmetry bridge theorem parallel to the ee case.

**Assumptions discharged.** The previous statement also carried
`hHad : HadronicWeakCurrentAssumptions V g K` and `hPoint : M.pointCompatible x y`.  Neither
was used: the proof bound them to `_`-prefixed hypotheses and then proceeded from `hIso`
alone.  Both are removed here, which strengthens the result -- helicity-interference
isolation is by itself sufficient, at every `(x, y)` including points the model does not
declare compatible.  That is a statement about the *reach* of the present formalization, not
a physics claim: the asymmetry chain in this module is algebra on
`NeutralCurrentDecomposition` and never touches the hadronic side. -/
lemma beamHelicityAsymmetry_eq_interferenceRatio_of_isolation
    {g : Kinematics.Bilin V}
    {K : Kinematics.DisKinematics V}
    (D : NeutralCurrentDecomposition)
    (M : CrossSectionModel V g K)
    (x y epsilonReg : ℝ)
    (hIso : IsolationAssumptions V D M) :
    beamHelicityAsymmetry V M x y epsilonReg
      = (2 * D.gammaZInterference x y) /
          (|2 * (D.photon x y + D.zBoson x y)| + epsilonReg) := by
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
    (x y epsilonReg : ℝ) :
    beamHelicityAsymmetry V (canonicalModelOfDecomposition V g K D) x y epsilonReg
      = (2 * D.gammaZInterference x y) /
          (|2 * (D.photon x y + D.zBoson x y)| + epsilonReg) :=
  beamHelicityAsymmetry_eq_interferenceRatio_of_isolation
    V
    D
    (canonicalModelOfDecomposition V g K D)
    x y epsilonReg
    (canonicalModel_isolationAssumptions V D)

end EP
end Processes
end PVES
end DIS
end Scattering
end QFT
end Physlib
