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

/-- Neutral-current vertex contract with vector and axial pieces.

"The vector current structure is present" is spelled out as the only statement the data of
this structure can support: the effective vector coupling does not vanish, and likewise for
the axial coupling.  Note that this is a real restriction and not a formality -- the
electron's tree-level vector coupling vanishes at `sin^2(theta_W) = 1/4`
(`Electroweak.electron_gV_eq_zero_iff`), which is close to the physical value.

The previous version carried `hasVectorCurrent : Prop` together with a witness
`hVectorCurrent : hasVectorCurrent`, and likewise for the axial piece.  Such a pair is not a
hypothesis: `hasVectorCurrent := True` satisfies it for every value of `vectorCoupling`. -/
structure NeutralCurrentVertexAssumptions where
  /-- Effective vector coupling. -/
  vectorCoupling : ℝ
  /-- Effective axial coupling. -/
  axialCoupling : ℝ
  /-- The vector current is present: its effective coupling does not vanish. -/
  vectorCoupling_ne_zero : vectorCoupling ≠ 0
  /-- The axial current is present: its effective coupling does not vanish. -/
  axialCoupling_ne_zero : axialCoupling ≠ 0

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

/-- Mediator mass-squared map for neutral-current channels. -/
def mediatorMassSq (rules : NeutralCurrentFeynmanRules) (m : NeutralMediator) : ℝ :=
  match m with
  | .photon => 0
  | .zBoson => rules.model.params.mZ ^ 2

/-- Contract interface for gamma/Z/interference decomposition at fixed kinematics.

Every component is `ℝ`-valued.  This is the reason the separate "gamma-Z interference is
real-valued" contract that `NeutralCurrentFeynmanRules` used to carry is unnecessary: at this
level of abstraction reality of the interference term is not an assumption but a consequence
of the target type. -/
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

/-- Channel availability for a neutral-current decomposition: a channel is *enabled* when
its contribution is not identically zero.

The previous version of this structure took no arguments and had three
`Prop`-plus-witness field pairs, so it said nothing about any decomposition at all. -/
structure NeutralCurrentChannelAssumptions (D : NeutralCurrentDecomposition) : Prop where
  /-- The photon channel contributes. -/
  photon_ne_zero : D.photon ≠ 0
  /-- The Z channel contributes. -/
  zBoson_ne_zero : D.zBoson ≠ 0
  /-- The gamma-Z interference channel contributes. -/
  gammaZInterference_ne_zero : D.gammaZInterference ≠ 0

/-- Algebraic identity: subtracting the parity-even `gamma + Z` pieces from the total leaves
the interference piece.  This holds for every decomposition by definition of
`totalNeutralCurrent` and carries no physical content.

It replaces a declaration previously called `parityOddFromInterferenceOnly`, whose name
claimed that parity-odd helicity dependence is carried by the interference contribution but
whose statement was this identity, hence true of every `D`. -/
lemma totalNeutralCurrent_sub_parityEven
    (D : NeutralCurrentDecomposition) (x y : ℝ) :
    totalNeutralCurrent D x y - (D.photon x y + D.zBoson x y)
      = D.gammaZInterference x y := by
  unfold totalNeutralCurrent
  ring

/-- The statement that the previous `parityOddFromInterferenceOnly` claimed to make: a
helicity-resolved observable family `sigma` has its parity-even part given by the
`gamma + Z` contributions and its parity-odd part given by the `gamma-Z` interference
contribution alone.  Unlike the identity above, this constrains `sigma` against `D`. -/
def ParityOddFromInterferenceOnly
    (D : NeutralCurrentDecomposition) (sigma : Bool → ℝ → ℝ → ℝ) : Prop :=
  ∀ x y, (sigma true x y + sigma false x y) / 2 = D.photon x y + D.zBoson x y
    ∧ (sigma true x y - sigma false x y) / 2 = D.gammaZInterference x y

/-- `ParityOddFromInterferenceOnly` is not vacuous: it fails for the identically zero
observable family against a decomposition with nonzero interference. -/
lemma not_forall_parityOddFromInterferenceOnly :
    ¬ ∀ (D : NeutralCurrentDecomposition) (sigma : Bool → ℝ → ℝ → ℝ),
        ParityOddFromInterferenceOnly D sigma := by
  intro h
  have hFail :=
    (h { photon := fun _ _ => 0, zBoson := fun _ _ => 0, gammaZInterference := fun _ _ => 1 }
      (fun _ _ _ => 0) 0 0).2
  norm_num at hFail

end Electroweak
end PVES
end DIS
end Scattering
end QFT
end Physlib
