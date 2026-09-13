/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.Basic
public import Physlib.QFT.PerturbationTheory.DimensionalRegularization.Basic
/-!

# QCD Renormalization Interfaces

This module introduces a minimal renormalization-constant interface for deriving
beta-function coefficients from coupling counterterm data.

The design is interface-first: the algebraic identities needed in concrete
renormalization schemes are represented as explicit assumptions.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace Renormalization

open Physlib.QFT.PerturbationTheory.DimensionalRegularization

/-- Minimal renormalization constants used in gauge-theory bookkeeping. -/
structure RenormalizationConstants : Type where
  /-- Coupling renormalization constant. -/
  zG : LaurentExpansionAtZero
  /-- Gluon-field renormalization constant. -/
  z3 : LaurentExpansionAtZero
  /-- Quark-field renormalization constant. -/
  z2 : LaurentExpansionAtZero
  /-- Quark-gluon vertex renormalization constant. -/
  z1F : LaurentExpansionAtZero
  /-- Ghost-gluon vertex renormalization constant. -/
  z1c : LaurentExpansionAtZero
  /-- Ghost-field renormalization constant. -/
  z3c : LaurentExpansionAtZero

/-- Slavnov-Taylor compatibility contracts for renormalization constants.

Concrete gauge-theory realizations can later replace these abstract contracts
with explicit identities.
-/
structure SlavnovTaylorAssumptions (Z : RenormalizationConstants) : Type where
  /-- Quark-gauge vertex identity placeholder. -/
  gaugeVertexIdentity : Prop
  /-- Ghost-gauge vertex identity placeholder. -/
  ghostVertexIdentity : Prop
  /-- Witness for quark-gauge vertex identity. -/
  hGaugeVertexIdentity : gaugeVertexIdentity
  /-- Witness for ghost-gauge vertex identity. -/
  hGhostVertexIdentity : ghostVertexIdentity

/-- Extract the `1/ε` coefficient from a Laurent expansion.

This is the concrete pole-extraction seam used by the renormalization layer.
Later dimensional-regularization modules will supply actual Laurent expansions
for loop integrals and counterterms.
-/
def poleCoeff (x : LaurentExpansionAtZero) : ℝ :=
  Physlib.QFT.PerturbationTheory.DimensionalRegularization.poleCoeff x

/-- Minimal subtraction-like data needed to map renormalization constants to beta input. -/
structure MSLikeRenormalizationData : Type where
  /-- MS-like renormalization scheme tag. -/
  scheme : RenormalizationScheme := .MS
  /-- Renormalization constants. -/
  Z : RenormalizationConstants
  /-- Extracted one-loop coupling pole coefficient. -/
  couplingPole : ℝ
  /-- Coupling pole is read from the coupling renormalization constant. -/
  hCouplingPole : couplingPole = poleCoeff Z.zG

/-- One-loop beta coefficient reconstructed from coupling-pole input. -/
def beta0FromCouplingPole (couplingPole : ℝ) : ℝ :=
  -2 * couplingPole

/-- Contract linking color-factor beta coefficient to renormalization-pole data. -/
structure Beta0RenormalizationAssumptions
    (cf : ColorFactors)
    (ms : MSLikeRenormalizationData) : Prop where
  /-- Scheme-specific relation between coupling pole and beta coefficient. -/
  couplingPole_formula : ms.couplingPole = -(beta0 cf) / 2

/-- If coupling-pole data satisfy the beta-link contract, the reconstructed
beta coefficient equals the color-factor beta coefficient. -/
lemma beta0_eq_from_renormalization
    (cf : ColorFactors)
    (ms : MSLikeRenormalizationData)
    (h : Beta0RenormalizationAssumptions cf ms) :
    beta0 cf = beta0FromCouplingPole ms.couplingPole := by
  unfold beta0FromCouplingPole
  rw [h.couplingPole_formula]
  ring

/-- Group-parameterized corollary of `beta0_eq_from_renormalization`. -/
lemma beta0Of_eq_from_renormalization
    (G : Type) [HasColorInvariants G]
    (nF : ℝ)
    (ms : MSLikeRenormalizationData)
    (h : Beta0RenormalizationAssumptions (colorFactorsOf G nF) ms) :
    beta0Of G nF = beta0FromCouplingPole ms.couplingPole := by
  simpa [beta0Of] using beta0_eq_from_renormalization (cf := colorFactorsOf G nF) (ms := ms) h

end Renormalization
end QCD
end QFT
end Physlib
