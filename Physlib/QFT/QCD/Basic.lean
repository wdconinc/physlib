/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# QCD Core Interfaces

This module introduces a minimal QCD core for DIS factorization and evolution:

- color-factor bookkeeping,
- perturbative beta-function coefficients,
- running-coupling interfaces,
- asymptotic-freedom contracts.

The content is intentionally interface-first: physically meaningful assumptions are
explicitly separated from structural algebraic definitions.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD

/-- Group-level color invariants independent of active-flavor count. -/
structure ColorInvariants : Type where
  /-- Fundamental Casimir `C_F`. -/
  cF : ℝ
  /-- Adjoint Casimir `C_A`. -/
  cA : ℝ
  /-- Trace normalization `T_F`. -/
  tF : ℝ

/-- Typeclass exposing color invariants derived from an underlying gauge-group model. -/
class HasColorInvariants (G : Type) : Type where
  invariants : ColorInvariants

/-- QCD color and flavor constants used by perturbative evolution formulas. -/
structure ColorFactors : Type where
  /-- Number of active quark flavors. -/
  nF : ℝ
  /-- Fundamental Casimir `C_F`. -/
  cF : ℝ
  /-- Adjoint Casimir `C_A`. -/
  cA : ℝ
  /-- Trace normalization `T_F`. -/
  tF : ℝ

/-- Build flavor-aware color factors from group-level color invariants. -/
def ColorInvariants.toColorFactors (inv : ColorInvariants) (nF : ℝ) : ColorFactors where
  nF := nF
  cF := inv.cF
  cA := inv.cA
  tF := inv.tF

/-- Build flavor-aware color factors from a gauge-group instance. -/
def colorFactorsOf (G : Type) [HasColorInvariants G] (nF : ℝ) : ColorFactors :=
  (HasColorInvariants.invariants (G := G)).toColorFactors nF

/-- SU(Nc)-inspired color-factor constructor used in practical interfaces. -/
def suNColorFactors (nC nF : ℝ) : ColorFactors where
  nF := nF
  cF := (nC ^ 2 - 1) / (2 * nC)
  cA := nC
  tF := 1 / 2

/-- Marker type for an `SU(Nc)` gauge-group model. -/
structure SUN (nC : ℝ) : Type where
  unit : Unit

/-- `SU(Nc)` color invariants packaged as a typeclass instance. -/
instance instHasColorInvariantsSUN (nC : ℝ) : HasColorInvariants (SUN nC) where
  invariants := {
    cF := (nC ^ 2 - 1) / (2 * nC)
    cA := nC
    tF := 1 / 2
  }

/-- Compatibility lemma: `colorFactorsOf` reproduces the existing `SU(Nc)` constructor. -/
lemma colorFactorsOf_suN_eq (nC nF : ℝ) :
    colorFactorsOf (SUN nC) nF = suNColorFactors nC nF := by
  rfl

/-- One-loop QCD beta-function coefficient. -/
def beta0 (cf : ColorFactors) : ℝ :=
  (11 / 3) * cf.cA - (4 / 3) * cf.tF * cf.nF

/-- One-loop beta-function coefficient from group-level color invariants. -/
def beta0Of (G : Type) [HasColorInvariants G] (nF : ℝ) : ℝ :=
  beta0 (colorFactorsOf G nF)

/-- Two-loop QCD beta-function coefficient in the common color-factor basis. -/
def beta1 (cf : ColorFactors) : ℝ :=
  (34 / 3) * cf.cA ^ 2
    - (20 / 3) * cf.cA * cf.tF * cf.nF
    - 4 * cf.cF * cf.tF * cf.nF

/-- Two-loop beta-function coefficient from group-level color invariants. -/
def beta1Of (G : Type) [HasColorInvariants G] (nF : ℝ) : ℝ :=
  beta1 (colorFactorsOf G nF)

/-- Asymptotic-freedom criterion for the one-loop running. -/
def IsAsymptoticallyFree (cf : ColorFactors) : Prop :=
  0 < beta0 cf

/-- One-loop beta-function coefficient of an `SU(Nc)` color-factor model:
`β₀ = (11/3) Nc - (2/3) nF`. -/
lemma beta0_suNColorFactors (nC nF : ℝ) :
    beta0 (suNColorFactors nC nF) = (11 / 3) * nC - (2 / 3) * nF := by
  simp only [beta0, suNColorFactors]
  ring

/-- One-loop asymptotic freedom of an `SU(Nc)` gauge theory in the active-flavor window
`2 nF < 11 Nc`. For `Nc = 3` this is the familiar `nF < 16.5`. -/
lemma isAsymptoticallyFree_suNColorFactors (nC nF : ℝ) (h : 2 * nF < 11 * nC) :
    IsAsymptoticallyFree (suNColorFactors nC nF) := by
  show (0 : ℝ) < beta0 (suNColorFactors nC nF)
  rw [beta0_suNColorFactors]
  linarith

/-- Three-color QCD is one-loop asymptotically free for fewer than `16.5` active flavors. -/
lemma isAsymptoticallyFree_qcd (nF : ℝ) (h : 2 * nF < 33) :
    IsAsymptoticallyFree (suNColorFactors 3 nF) := by
  refine isAsymptoticallyFree_suNColorFactors 3 nF ?_
  linarith

-- A `RunningCouplingAssumptions` bundle used to sit here. It had no dependent declaration
-- anywhere in the repository, and its two fields did not survive inspection: the first,
-- `lambdaQCD2_pos : 0 < (1 : ℝ)`, is a theorem of arithmetic that mentions no parameter of
-- the structure (the intended `0 < Λ²` cannot be stated, since `Λ²` is not a parameter, and
-- `oneLoopAlphaS` regularizes the scale as `|Λ²| + 1` so needs no such hypothesis anyway).
-- The second field was exactly `IsAsymptoticallyFree cf`, which is a standalone definition
-- above and is usable directly. Nothing that was asserted has been lost; the lemmas above
-- now discharge that condition for the `SU(Nc)` and QCD color-factor models.

/-- One-loop running-coupling proxy for interfaces.
The denominator regularization keeps the map total at all inputs while retaining
qualitative dependence on `log(Q2 / Λ^2)`. -/
def oneLoopAlphaS (cf : ColorFactors) (Q2 lambdaQCD2 : ℝ) : ℝ :=
  (4 * Real.pi) /
    (|beta0 cf| * (|Real.log (Q2 / (|lambdaQCD2| + 1))| + 1))

/-- Positivity/nonnegativity interface for one-loop running coupling proxy. -/
lemma oneLoopAlphaS_nonneg (cf : ColorFactors) (Q2 lambdaQCD2 : ℝ) :
    0 ≤ oneLoopAlphaS cf Q2 lambdaQCD2 := by
  unfold oneLoopAlphaS
  positivity

/-- Monotone perturbative-order profile used for truncation bookkeeping. -/
inductive PerturbativeOrder where
  | LO
  | NLO
  | NNLO

/-- Coefficient-function truncation order metadata. -/
structure CoefficientProfile : Type where
  order : PerturbativeOrder
  value : ℝ → ℝ

/-- Truncation is stable under identical order tags. -/
lemma coefficientProfile_order_stability (p : CoefficientProfile) :
    p.order = p.order := rfl

/-- Practical sufficient criterion for asymptotic freedom in a color-factor basis. -/
lemma asymptoticFreedom_of_beta0_pos
    (cf : ColorFactors)
    (h : 0 < beta0 cf) :
    IsAsymptoticallyFree cf :=
  h

end QCD
end QFT
end Physlib
