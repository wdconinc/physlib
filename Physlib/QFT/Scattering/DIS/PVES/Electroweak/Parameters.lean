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

noncomputable section

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

/-!

## Consequences of the tree-level relations

The three contracts above are not independent of the quantities a PVES analysis reports.
The lemmas in this section derive the standard tree-level identities from them, so that a
downstream module can use the identity rather than assume it.

-/

/-- Weak-mixing cosine squared, `cos^2(theta_W) = 1 - sin^2(theta_W)`. -/
def cos2ThetaW (P : Parameters) : ℝ :=
  1 - P.sin2ThetaW

/-- Companion of `weakMixingConsistency`: `cos^2(theta_W) (g^2 + g'^2) = g^2`. -/
lemma cos2ThetaW_mul_couplingSq (P : Parameters) (h : weakMixingConsistency P) :
    cos2ThetaW P * (P.gSU2 ^ 2 + P.gU1 ^ 2) = P.gSU2 ^ 2 := by
  have hMix : P.sin2ThetaW * (P.gSU2 ^ 2 + P.gU1 ^ 2) = P.gU1 ^ 2 := h
  have hExpand : cos2ThetaW P * (P.gSU2 ^ 2 + P.gU1 ^ 2)
      = (P.gSU2 ^ 2 + P.gU1 ^ 2) - P.sin2ThetaW * (P.gSU2 ^ 2 + P.gU1 ^ 2) := by
    unfold cos2ThetaW
    ring
  rw [hExpand, hMix]
  ring

/-- Tree-level relation `e^2 = g^2 sin^2(theta_W)`, derived from the weak-mixing and
electric-charge contracts.  Both hypotheses are used, and the nondegeneracy
`g^2 + g'^2 ≠ 0` cannot be dropped: at `g = g' = 0` the two contracts hold for every value
of `electricCharge`. -/
lemma electricCharge_sq_eq_gSU2_sq_mul_sin2ThetaW (P : Parameters)
    (hMix : weakMixingConsistency P) (hEM : electricChargeConsistency P)
    (hNe : P.gSU2 ^ 2 + P.gU1 ^ 2 ≠ 0) :
    P.electricCharge ^ 2 = P.gSU2 ^ 2 * P.sin2ThetaW := by
  have hA : P.sin2ThetaW * (P.gSU2 ^ 2 + P.gU1 ^ 2) = P.gU1 ^ 2 := hMix
  have hB : P.electricCharge ^ 2 * (P.gSU2 ^ 2 + P.gU1 ^ 2) = P.gSU2 ^ 2 * P.gU1 ^ 2 := hEM
  have key : (P.electricCharge ^ 2 - P.gSU2 ^ 2 * P.sin2ThetaW) * (P.gSU2 ^ 2 + P.gU1 ^ 2)
      = 0 := by
    have hExpand : (P.electricCharge ^ 2 - P.gSU2 ^ 2 * P.sin2ThetaW)
          * (P.gSU2 ^ 2 + P.gU1 ^ 2)
        = P.electricCharge ^ 2 * (P.gSU2 ^ 2 + P.gU1 ^ 2)
            - P.gSU2 ^ 2 * (P.sin2ThetaW * (P.gSU2 ^ 2 + P.gU1 ^ 2)) := by
      ring
    rw [hExpand, hA, hB]
    ring
  rcases mul_eq_zero.mp key with hZero | hNeZero
  · linarith
  · exact absurd hNeZero hNe

/-- The on-shell `rho` parameter, `rho = m_W^2 / (m_Z^2 cos^2(theta_W))`. -/
def rhoParameter (P : Parameters) : ℝ :=
  P.mW ^ 2 / (P.mZ ^ 2 * cos2ThetaW P)

/-- The mass-ratio contract of `ConsistencyAssumptions` is exactly the tree-level statement
`rho = 1`.  Recording this makes visible that `Parameters` describes a tree-level, on-shell
parameter set: it cannot represent `rho ≠ 1` and therefore cannot carry the electroweak
radiative corrections that current PVES analyses apply. -/
lemma rhoParameter_eq_one_of_weakMassRatio (P : Parameters)
    (h : weakMassRatioConsistency P) (hNe : P.mZ ^ 2 * cos2ThetaW P ≠ 0) :
    rhoParameter P = 1 := by
  have hEq : P.mW ^ 2 = P.mZ ^ 2 * cos2ThetaW P := h
  rw [rhoParameter, hEq, div_self hNe]

/-- Converse of `rhoParameter_eq_one_of_weakMassRatio`. -/
lemma weakMassRatioConsistency_of_rhoParameter_eq_one (P : Parameters)
    (hNe : P.mZ ^ 2 * cos2ThetaW P ≠ 0) (h : rhoParameter P = 1) :
    weakMassRatioConsistency P :=
  (div_eq_one_iff_eq hNe).mp h

/-- On-shell reading of the weak-mixing angle, `sin^2(theta_W) = 1 - m_W^2 / m_Z^2`. -/
lemma sin2ThetaW_eq_one_sub_massSqRatio (P : Parameters)
    (h : weakMassRatioConsistency P) (hZ : P.mZ ^ 2 ≠ 0) :
    P.sin2ThetaW = 1 - P.mW ^ 2 / P.mZ ^ 2 := by
  have hEq : P.mW ^ 2 = P.mZ ^ 2 * (1 - P.sin2ThetaW) := h
  have hdiv : P.mW ^ 2 / P.mZ ^ 2 = 1 - P.sin2ThetaW := by
    rw [hEq]
    exact mul_div_cancel_left₀ _ hZ
  rw [hdiv]
  ring

/-!

## Tree-level couplings and weak charges

Conventions follow the Particle Data Group review of the electroweak model:
`g_V^f = T_3^f - 2 Q_f sin^2(theta_W)` and `g_A^f = T_3^f`, and the low-energy
electron-quark couplings `C_{1q} = 2 g_A^e g_V^q`.  The weak charges below are the
quantities parity-violating electron scattering actually reports.

-/

/-- Standard-model tree-level neutral-current couplings at a given `sin^2(theta_W)`. -/
def smTreeLevelCouplings (s2 : ℝ) : NeutralCurrentCouplings where
  electron := { gV := -1 / 2 + 2 * s2, gA := -1 / 2 }
  upType := { gV := 1 / 2 - 4 / 3 * s2, gA := 1 / 2 }
  downType := { gV := -1 / 2 + 2 / 3 * s2, gA := -1 / 2 }

/-- Low-energy electron-up-quark coupling `C_{1u} = -1/2 + (4/3) sin^2(theta_W)`. -/
def c1Up (s2 : ℝ) : ℝ :=
  -1 / 2 + 4 / 3 * s2

/-- Low-energy electron-down-quark coupling `C_{1d} = 1/2 - (2/3) sin^2(theta_W)`. -/
def c1Down (s2 : ℝ) : ℝ :=
  1 / 2 - 2 / 3 * s2

lemma c1Up_eq_two_mul_gA_mul_gV (s2 : ℝ) :
    c1Up s2
      = 2 * (smTreeLevelCouplings s2).electron.gA * (smTreeLevelCouplings s2).upType.gV := by
  simp only [c1Up, smTreeLevelCouplings]
  ring

lemma c1Down_eq_two_mul_gA_mul_gV (s2 : ℝ) :
    c1Down s2
      = 2 * (smTreeLevelCouplings s2).electron.gA * (smTreeLevelCouplings s2).downType.gV := by
  simp only [c1Down, smTreeLevelCouplings]
  ring

/-- Weak charge of the electron, `Q_W^e = 1 - 4 sin^2(theta_W)`. -/
def electronWeakCharge (s2 : ℝ) : ℝ :=
  1 - 4 * s2

/-- Weak charge of the proton, `Q_W^p = -2 (2 C_{1u} + C_{1d})`. -/
def protonWeakCharge (s2 : ℝ) : ℝ :=
  -2 * (2 * c1Up s2 + c1Down s2)

/-- Weak charge of the neutron, `Q_W^n = -2 (C_{1u} + 2 C_{1d})`. -/
def neutronWeakCharge (s2 : ℝ) : ℝ :=
  -2 * (c1Up s2 + 2 * c1Down s2)

/-- Weak charge of a nucleus with `Z` protons and `N` neutrons. -/
def nuclearWeakCharge (Z N s2 : ℝ) : ℝ :=
  Z * protonWeakCharge s2 + N * neutronWeakCharge s2

/-- The electron weak charge is four times the product of its tree-level neutral-current
couplings. -/
lemma electronWeakCharge_eq_four_mul_gA_mul_gV (s2 : ℝ) :
    electronWeakCharge s2
      = 4 * (smTreeLevelCouplings s2).electron.gA
          * (smTreeLevelCouplings s2).electron.gV := by
  simp only [electronWeakCharge, smTreeLevelCouplings]
  ring

/-- At tree level the proton weak charge equals `1 - 4 sin^2(theta_W)`. -/
lemma protonWeakCharge_eq (s2 : ℝ) : protonWeakCharge s2 = 1 - 4 * s2 := by
  simp only [protonWeakCharge, c1Up, c1Down]
  ring

/-- At tree level the proton and the electron carry the same weak charge. -/
lemma protonWeakCharge_eq_electronWeakCharge (s2 : ℝ) :
    protonWeakCharge s2 = electronWeakCharge s2 := by
  rw [protonWeakCharge_eq, electronWeakCharge]

/-- **The neutron weak charge is `-1`, independently of the weak-mixing angle.** The
`sin^2(theta_W)` dependence of `C_{1u}` and `C_{1d}` cancels in the combination
`C_{1u} + 2 C_{1d}`.  This is why a heavy nucleus, whose weak charge is dominated by `-N`,
is a weak-mixing-angle probe only through its proton term. -/
theorem neutronWeakCharge_eq_neg_one (s2 : ℝ) : neutronWeakCharge s2 = -1 := by
  simp only [neutronWeakCharge, c1Up, c1Down]
  ring

/-- Nuclear weak charge in the form used by parity-violating electron-nucleus scattering,
`Q_W(Z, N) = Z (1 - 4 sin^2(theta_W)) - N`. -/
lemma nuclearWeakCharge_eq (Z N s2 : ℝ) :
    nuclearWeakCharge Z N s2 = Z * (1 - 4 * s2) - N := by
  rw [nuclearWeakCharge, protonWeakCharge_eq, neutronWeakCharge_eq_neg_one]
  ring

/-- The electron weak charge vanishes exactly at `sin^2(theta_W) = 1/4`.  Its accidental
smallness at the physical value is the reason the Moller asymmetry is a sensitive
weak-mixing-angle probe, and the reason the electron's tree-level *vector* coupling nearly
vanishes there as well. -/
lemma electronWeakCharge_eq_zero_iff (s2 : ℝ) :
    electronWeakCharge s2 = 0 ↔ s2 = 1 / 4 := by
  unfold electronWeakCharge
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

lemma electron_gV_eq_zero_iff (s2 : ℝ) :
    (smTreeLevelCouplings s2).electron.gV = 0 ↔ s2 = 1 / 4 := by
  simp only [smTreeLevelCouplings]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

/-- Full effective electroweak model used by PVES interfaces.

Standard-model compatibility is carried by `consistency`, i.e. by the three tree-level
relations of `ConsistencyAssumptions`, which are statements about `params`.

An earlier version of this structure carried instead a pair of fields

```
  smCompatible : Prop
  hSmCompatible : smCompatible
```

which asserts nothing: `smCompatible := True`, `hSmCompatible := trivial` satisfies it for
every choice of `params` and `couplings`, so the field name overstated its content. -/
structure EffectiveModel where
  /-- Electroweak parameters. -/
  params : Parameters
  /-- Effective neutral-current couplings for fermions. -/
  couplings : NeutralCurrentCouplings
  /-- The tree-level electroweak relations hold for `params`. -/
  consistency : ConsistencyAssumptions params

end Electroweak
end PVES
end DIS
end Scattering
end QFT
end Physlib
