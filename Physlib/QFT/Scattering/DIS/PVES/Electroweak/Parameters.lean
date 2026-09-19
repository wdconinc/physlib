/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
/-!

# PVES Electroweak Parameters

This module defines electroweak parameter and effective neutral-current coupling
interfaces used by parity-violating electron scattering (PVES) contracts.

-/

@[expose] public section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace PVES
namespace Electroweak

/-- Core electroweak parameter record used by PVES interfaces. -/
structure Parameters where
  /-- SU(2) weak-isospin coupling. -/
  gSU2 : ℝ
  /-- U(1) hypercharge coupling. -/
  gU1 : ℝ
  /-- Electromagnetic coupling. -/
  electricCharge : ℝ
  /-- Weak-mixing input usually denoted `sin^2(theta_W)`. -/
  sin2ThetaW : ℝ
  /-- Z-boson mass parameter. -/
  mZ : ℝ
  /-- W-boson mass parameter. -/
  mW : ℝ

/-- Effective vector/axial neutral-current couplings for one fermion species. -/
structure FermionNeutralCurrentCouplings where
  /-- Vector coupling. -/
  gV : ℝ
  /-- Axial coupling. -/
  gA : ℝ

/-- Effective neutral-current coupling bundle used in PVES channels. -/
structure NeutralCurrentCouplings where
  /-- Electron couplings `(gV^e, gA^e)`. -/
  electron : FermionNeutralCurrentCouplings
  /-- Up-type quark couplings `(gV^u, gA^u)`. -/
  upType : FermionNeutralCurrentCouplings
  /-- Down-type quark couplings `(gV^d, gA^d)`. -/
  downType : FermionNeutralCurrentCouplings

/-- Tree-level weak-mixing relation contract. -/
def weakMixingConsistency (P : Parameters) : Prop :=
  P.sin2ThetaW * (P.gSU2 ^ 2 + P.gU1 ^ 2) = P.gU1 ^ 2

/-- Electromagnetic coupling relation contract. -/
def electricChargeConsistency (P : Parameters) : Prop :=
  P.electricCharge ^ 2 * (P.gSU2 ^ 2 + P.gU1 ^ 2) = P.gSU2 ^ 2 * P.gU1 ^ 2

/-- Tree-level mass-ratio relation contract. -/
def weakMassRatioConsistency (P : Parameters) : Prop :=
  P.mW ^ 2 = P.mZ ^ 2 * (1 - P.sin2ThetaW)

/-- Assumption bundle collecting electroweak consistency contracts. -/
structure ConsistencyAssumptions (P : Parameters) : Prop where
  /-- Weak-mixing relation holds. -/
  weakMixing : weakMixingConsistency P
  /-- Electric-charge relation holds. -/
  electricCharge : electricChargeConsistency P
  /-- Tree-level mass ratio relation holds. -/
  weakMassRatio : weakMassRatioConsistency P

lemma weakMixingConsistency_of_assumptions
    (P : Parameters) (h : ConsistencyAssumptions P) :
    weakMixingConsistency P :=
  h.weakMixing

lemma electricChargeConsistency_of_assumptions
    (P : Parameters) (h : ConsistencyAssumptions P) :
    electricChargeConsistency P :=
  h.electricCharge

lemma weakMassRatioConsistency_of_assumptions
    (P : Parameters) (h : ConsistencyAssumptions P) :
    weakMassRatioConsistency P :=
  h.weakMassRatio

/-- Full effective electroweak model used by PVES interfaces. -/
structure EffectiveModel where
  /-- Electroweak parameters. -/
  params : Parameters
  /-- Effective neutral-current couplings for fermions. -/
  couplings : NeutralCurrentCouplings
  /-- Standard-model compatibility contract placeholder. -/
  smCompatible : Prop
  /-- Witness of standard-model compatibility. -/
  hSmCompatible : smCompatible

end Electroweak
end PVES
end DIS
end Scattering
end QFT
end Physlib
