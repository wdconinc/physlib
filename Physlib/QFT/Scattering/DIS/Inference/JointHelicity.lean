/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Inference.Basic
public import Physlib.QFT.Scattering.DIS.Inference.Helicity
public import Physlib.QFT.Scattering.DIS.Inference.Gluon
/-!

# Joint DeltaSigma/DeltaG Extraction Contracts

This module defines Stage-26 interfaces that jointly encode DeltaSigma and
DeltaG extraction assumptions, identifiability formulas, and bounded-systematic
stability contracts.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Inference
namespace JointHelicity

/-- Data-source labels for joint helicity extraction inputs. -/
inductive SourceTag where
  | inclusiveMoment
  | inclusiveSlope
  | taggedChannel
  deriving DecidableEq, Repr

/-- Joint data point spanning Stage 23-25 observable families. -/
structure JointDataPoint where
  source : SourceTag
  xBj : ℝ
  Q2 : ℝ
  observed : ℝ

/-- Joint dataset container used by coupled DeltaSigma/DeltaG fits. -/
structure JointDataset where
  entries : List JointDataPoint

/-- Stage-26 assumption bundle joining DeltaSigma and DeltaG contracts. -/
structure JointExtractionAssumptions
    (G : Polarized.StructureFunctions)
    (slope : ℝ → ℝ → ℝ)
    (obs : Gluon.TaggedChannelDataPoint → ℝ)
    (deltaSigma : ℝ → ℝ)
    (deltaG : ℝ → ℝ → ℝ)
    (wilsonSinglet nonSingletShift : ℝ → ℝ)
    (slopeCoeff slopeResidual : ℝ → ℝ → ℝ)
    (channelWeight : Gluon.TaggedChannel → ℝ)
    (channelResidual : Gluon.TaggedChannelDataPoint → ℝ) : Prop where
  helicity :
    Helicity.DeltaSigmaSchemeAssumptions G deltaSigma wilsonSinglet nonSingletShift
  slopeModel :
    Gluon.DeltaGSlopeAssumptions slope deltaG slopeCoeff slopeResidual
  channelModel :
    Gluon.ChannelDeltaGAssumptions obs deltaG channelWeight channelResidual

/-- Joint identifiability theorem: recover DeltaSigma and DeltaG from one model bundle. -/
lemma joint_identifiability
    (G : Polarized.StructureFunctions)
    (slope : ℝ → ℝ → ℝ)
    (obs : Gluon.TaggedChannelDataPoint → ℝ)
    (deltaSigma : ℝ → ℝ)
    (deltaG : ℝ → ℝ → ℝ)
    (wilsonSinglet nonSingletShift : ℝ → ℝ)
    (slopeCoeff slopeResidual : ℝ → ℝ → ℝ)
    (channelWeight : Gluon.TaggedChannel → ℝ)
    (channelResidual : Gluon.TaggedChannelDataPoint → ℝ)
    (hJoint : JointExtractionAssumptions
      G slope obs deltaSigma deltaG
      wilsonSinglet nonSingletShift
      slopeCoeff slopeResidual
      channelWeight channelResidual)
    (Q2 x tau : ℝ)
    (hWilson : wilsonSinglet Q2 ≠ 0)
    (hCoeff : slopeCoeff x tau ≠ 0) :
    deltaSigma Q2
      = (Helicity.g1FirstMoment G Q2 - nonSingletShift Q2) / wilsonSinglet Q2
    ∧
    deltaG x (Real.exp tau)
      = (slope x tau - slopeResidual x tau) / slopeCoeff x tau := by
  constructor
  · exact Helicity.deltaSigma_eq_of_scheme
      G deltaSigma wilsonSinglet nonSingletShift hJoint.helicity Q2 hWilson
  · exact Gluon.deltaG_eq_of_slope_model
      slope deltaG slopeCoeff slopeResidual hJoint.slopeModel x tau hCoeff

/-- Channel and slope extractions are consistent when both reconstruct the same `deltaG`. -/
lemma tagged_vs_slope_consistency
    (G : Polarized.StructureFunctions)
    (slope : ℝ → ℝ → ℝ)
    (obs : Gluon.TaggedChannelDataPoint → ℝ)
    (deltaSigma : ℝ → ℝ)
    (deltaG : ℝ → ℝ → ℝ)
    (wilsonSinglet nonSingletShift : ℝ → ℝ)
    (slopeCoeff slopeResidual : ℝ → ℝ → ℝ)
    (channelWeight : Gluon.TaggedChannel → ℝ)
    (channelResidual : Gluon.TaggedChannelDataPoint → ℝ)
    (hJoint : JointExtractionAssumptions
      G slope obs deltaSigma deltaG
      wilsonSinglet nonSingletShift
      slopeCoeff slopeResidual
      channelWeight channelResidual)
    (d : Gluon.TaggedChannelDataPoint)
    (tau : ℝ)
    (hQ2 : d.Q2 = Real.exp tau)
    (hWeight : channelWeight d.channel ≠ 0)
    (hCoeff : slopeCoeff d.xBj tau ≠ 0) :
    (obs d - channelResidual d) / channelWeight d.channel
      = (slope d.xBj tau - slopeResidual d.xBj tau) / slopeCoeff d.xBj tau := by
  have hTagged :
      deltaG d.xBj d.Q2 =
        (obs d - channelResidual d) / channelWeight d.channel :=
    Gluon.deltaG_channel_access
      obs deltaG channelWeight channelResidual hJoint.channelModel d hWeight
  have hSlope :
      deltaG d.xBj (Real.exp tau) =
        (slope d.xBj tau - slopeResidual d.xBj tau) / slopeCoeff d.xBj tau :=
    Gluon.deltaG_eq_of_slope_model
      slope deltaG slopeCoeff slopeResidual hJoint.slopeModel d.xBj tau hCoeff
  have hTagged' :
      deltaG d.xBj (Real.exp tau) =
        (obs d - channelResidual d) / channelWeight d.channel := by
    simpa [hQ2] using hTagged
  calc
    (obs d - channelResidual d) / channelWeight d.channel
        = deltaG d.xBj (Real.exp tau) := hTagged'.symm
    _ = (slope d.xBj tau - slopeResidual d.xBj tau) / slopeCoeff d.xBj tau := hSlope

/-- Bounded-systematics stability schema across moment/slope/tagged observables. -/
lemma joint_shifted_prediction_stability
    (momentPred momentShift momentEps : ℝ)
    (slopePred slopeShift slopeEps : ℝ)
    (channelPred channelShift channelEps : ℝ)
    (hMoment : |momentShift| ≤ momentEps)
    (hSlope : |slopeShift| ≤ slopeEps)
    (hChannel : |channelShift| ≤ channelEps) :
    |Inference.shiftedPrediction momentPred momentShift - momentPred| ≤ momentEps
    ∧ |Inference.shiftedPrediction slopePred slopeShift - slopePred| ≤ slopeEps
    ∧ |Inference.shiftedPrediction channelPred channelShift - channelPred| ≤ channelEps := by
  constructor
  · exact Inference.shiftedPrediction_stability momentPred momentShift momentEps hMoment
  constructor
  · exact Inference.shiftedPrediction_stability slopePred slopeShift slopeEps hSlope
  · exact Inference.shiftedPrediction_stability channelPred channelShift channelEps hChannel

/-- Joint consistency of DeltaSigma extraction and identity scheme conversion for DeltaG. -/
lemma joint_identity_scheme_consistency
    {Flavor : Type}
    [Fintype Flavor]
    (G : Polarized.StructureFunctions)
    (deltaSigma : ℝ → ℝ)
    (wilsonSinglet nonSingletShift : ℝ → ℝ)
    (hHel : Helicity.DeltaSigmaSchemeAssumptions G deltaSigma wilsonSinglet nonSingletShift)
    (Q2 : ℝ)
    (S : Factorization.HigherOrder.Scheme)
    (C : Factorization.HigherOrder.HardKernelFamily Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (x : ℝ)
    (ord : Factorization.HigherOrder.PerturbativeOrder) :
    g1FirstMoment G Q2 = wilsonSinglet Q2 * deltaSigma Q2 + nonSingletShift Q2
    ∧ Factorization.HigherOrder.truncatedStructureFunction
        (Factorization.HigherOrder.convertKernel S S C ord) f x Q2
        = Factorization.HigherOrder.truncatedStructureFunction C f x Q2 := by
  constructor
  · exact hHel.extraction Q2
  · exact Gluon.deltaG_identity_scheme_stability S C f x Q2 ord

end JointHelicity
end Inference
end DIS
end Scattering
end QFT
end Physlib
