/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Inference.Basic
public import Physlib.QFT.Scattering.DIS.Exclusive.DVCS.Interference
public import Physlib.QFT.Scattering.DIS.Exclusive.DVMP.Channels
/-!

# Joint DVCS/DVMP Inference Contracts

This module defines joint extraction contracts and compatibility interfaces for
exclusive DVCS and DVMP observable families.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Inference
namespace ExclusiveJoint

/-- Exclusive-process tag used by the joint dataset interface. -/
inductive ProcessTag where
  | dvcs
  | dvmp
  deriving DecidableEq, Repr

/-- Abstract exclusive data point for DVCS/DVMP joint fits. -/
structure ExclusiveDataPoint where
  tag : ProcessTag
  xiSkew : ℝ
  tMom : ℝ
  Q2 : ℝ
  observed : ℝ

/-- Joint dataset container for exclusive channels. -/
structure JointDataset where
  entries : List ExclusiveDataPoint

/-- Prediction residual interface. -/
def residual (prediction observed : ℝ) : ℝ :=
  prediction - observed

/-- Joint compatibility assumptions for two prediction maps. -/
structure JointCompatibilityAssumptions
    (dvcsPred dvmpPred : ExclusiveDataPoint → ℝ) : Prop where
  boundedGap : ∀ d, |dvcsPred d - dvmpPred d| ≤ 1

lemma compatibility_gap_bound
    (dvcsPred dvmpPred : ExclusiveDataPoint → ℝ)
    (hComp : JointCompatibilityAssumptions dvcsPred dvmpPred)
    (d : ExclusiveDataPoint) :
    |dvcsPred d - dvmpPred d| ≤ 1 :=
  hComp.boundedGap d

/-- Shifted prediction interface for exclusive channels. -/
def shiftedPrediction (prediction nuisanceShift : ℝ) : ℝ :=
  prediction + nuisanceShift

/-- Stability theorem for nuisance-shifted exclusive predictions. -/
lemma shiftedPrediction_stability
    (prediction nuisanceShift eps : ℝ)
    (hBound : |nuisanceShift| ≤ eps) :
    |shiftedPrediction prediction nuisanceShift - prediction| ≤ eps := by
  simpa [shiftedPrediction] using hBound

/-- Joint chi-square interface for a dataset and one prediction map. -/
def jointChiSq
    (sigma : ℝ)
    (pred : ExclusiveDataPoint → ℝ)
    (D : JointDataset) : ℝ :=
  (D.entries.map (fun d => Inference.chiSq (pred d) d.observed sigma)).sum

lemma jointChiSq_nonneg
    (sigma : ℝ)
    (pred : ExclusiveDataPoint → ℝ)
    (D : JointDataset) :
    0 ≤ jointChiSq sigma pred D := by
  unfold jointChiSq
  refine List.sum_nonneg ?_
  intro x hx
  rcases List.mem_map.mp hx with ⟨d, _hd, rfl⟩
  exact Inference.chiSq_nonneg (pred d) d.observed sigma

end ExclusiveJoint
end Inference
end DIS
end Scattering
end QFT
end Physlib
