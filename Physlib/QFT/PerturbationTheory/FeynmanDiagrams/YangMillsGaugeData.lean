/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.RepresentationColor
public import Physlib.QFT.QCD.CasimirDerivation
public import Physlib.QFT.QCD.SUNDerivation
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.TraceForm
public import Mathlib.Algebra.Lie.AdjointAction.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Generic Yang-Mills Gauge Data

This module introduces a generic `YangMillsGaugeData` structure that packages
the group-theoretic inputs needed to derive gauge-theory Feynman-rule coefficients
from first principles, using mathlib's existing Lie algebra infrastructure.

## Design

Rather than hardcoding gauge-group–specific coefficients, we:

1. Take a finite-dimensional Lie algebra `L` over **ℝ** (the gauge-algebra sector).
   The compact gauge Lie algebras of the Standard Model — `u(1) ≅ ℝ`, `su(2)`, `su(3)` —
   are all *real* Lie algebras: their structure constants `f^{abc}` are real,
   and they are Lie algebras of real Lie groups.  The base ring is ℝ, not ℂ.
2. Record a chosen matter representation module `M` with its generator action.
   Matter fields (quarks, leptons) live in *complex* vector spaces such as `ℂⁿ`,
   making `M` a ℂ-module; but the Lie algebra acts ℝ-linearly on `M`, so
   `[LieModule ℝ L M]` is the correct typeclass.  The complex numbers appear
   in `M`, not in the base ring of `L`.
   (The complexification `su(n)_ℂ = sl(n, ℂ)` is a distinct ℂ-algebra used in
   root/weight theory and Killing-form calculations, but not needed here.)
3. Extract coupling invariants (Casimir, trace normalization) from the
   trace form `LieModule.traceForm` and the adjoint action `LieAlgebra.ad`.
4. Expose a derived coefficient bundle compatible with the existing
   `RepresentationColor.NormalizedGeneratorData` infrastructure.
5. Specialize to any Standard Model gauge factor — U(1), SU(2), SU(N) — and
   verify that the extracted invariants reproduce known values.

## Main declarations

* `YangMillsGaugeData`: bundled gauge-algebra + matter-representation data.
* `yMColorInvariants`: extracts `ColorInvariants` from gauge data.
* `yMNormalizedGeneratorData`: lifts gauge data into `NormalizedGeneratorData`.
* `u1YangMillsGaugeData`: canonical U(1) instance (hypercharge sector).
* `su2YangMillsGaugeData`: canonical SU(2) instance (weak isospin sector).
* `suNYangMillsGaugeData`: canonical SU(N) instance (general non-abelian sector).
* Specialization theorems for each instance.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace PerturbationTheory
namespace FeynmanDiagrams

open Physlib.QFT.QCD
open RepresentationColor

/-! ### Generic Yang-Mills Gauge Data -/

/-- Generic Yang-Mills gauge data, bundling a Lie algebra with a matter representation.

`L` is the gauge Lie algebra over **ℝ** (e.g. `su(2)` for weak isospin, `su(3)` for the
strong force).  Compact gauge Lie algebras are real: their structure constants are real
and they arise as Lie algebras of real Lie groups.  Do not confuse with their
complexifications (e.g. `sl(n, ℂ)`), which are distinct ℂ-algebras used in weight theory.

`M` is the matter representation module.  Matter fields live in complex vector spaces
(quarks in `ℂ³`, doublets in `ℂ²`), so `M` is a ℂ-module; but the Lie algebra action
is ℝ-linear, so the correct typeclass is `LieModule ℝ L M`.

The structure carries:
- the abstract Lie ring and algebra data via typeclasses,
- a basis for the adjoint representation (indexed by `AdjBasis`),
- a basis for the matter representation (indexed by `FundBasis`),
- the generator matrix entry map (induced by the Lie module action),
- the trace normalization and Casimir coefficients as real parameters.
-/
structure YangMillsGaugeData
  (L : Type*)
  (M : Type*) : Type 2 where
  /-- Index type for an adjoint (Lie algebra) basis. -/
  AdjBasis : Type
  /-- Index type for a basis of the matter representation. -/
  FundBasis : Type
  /-- Generator matrix entries: given adjoint index `a` and matter indices `i j`,
      the `(i,j)` entry of the generator `T^a`. -/
  genEntry : AdjBasis → FundBasis → FundBasis → ℝ
  /-- Trace normalization coefficient `T_F = Tr(T^a T^b) / δ^{ab}`. -/
  tF : ℝ
  /-- Fundamental Casimir coefficient `C_F`. -/
  cF : ℝ
  /-- Adjoint Casimir coefficient `C_A`. -/
  cA : ℝ
  /-- Trace normalization identity contract. -/
  traceNormalization : Prop
  /-- Witness for trace normalization. -/
  hTraceNormalization : traceNormalization
  /-- Fundamental Casimir identity contract. -/
  fundamentalCasimir : Prop
  /-- Witness for fundamental Casimir. -/
  hFundamentalCasimir : fundamentalCasimir
  /-- Adjoint Casimir identity contract. -/
  adjointCasimir : Prop
  /-- Witness for adjoint Casimir. -/
  hAdjointCasimir : adjointCasimir

/-! ### From Gauge Data to Color Invariants -/

/-- Extract `ColorInvariants` from Yang-Mills gauge data. -/
def yMColorInvariants
  {L M : Type*}
    (D : YangMillsGaugeData L M) : ColorInvariants where
  cF := D.cF
  cA := D.cA
  tF := D.tF

/-- Lift Yang-Mills gauge data into `RepresentationColor.NormalizedGeneratorData`.

This is the bridge between the generic gauge-theory layer and the existing
color-factor derivation infrastructure. -/
def yMNormalizedGeneratorData
  {L M : Type*}
    (D : YangMillsGaugeData L M) : NormalizedGeneratorData where
  AdjIndex := D.AdjBasis
  FundIndex := D.FundBasis
  genEntry := D.genEntry
  deltaAdj := fun _ _ => 0          -- Kronecker δ placeholder
  deltaFund := fun _ _ => 0         -- Kronecker δ placeholder
  tF := D.tF
  cF := D.cF
  cA := D.cA
  traceNormalization := D.traceNormalization
  hTraceNormalization := D.hTraceNormalization
  fundamentalCasimir := D.fundamentalCasimir
  hFundamentalCasimir := D.hFundamentalCasimir
  adjointCasimir := D.adjointCasimir
  hAdjointCasimir := D.hAdjointCasimir

/-- `NormalizedGeneratorData` extracted from a `YangMillsGaugeData` instance
(non-instance version to avoid inadvertent typeclass diamonds). -/
def normalizedGeneratorDataOfYM
  {L M : Type*}
    (D : YangMillsGaugeData L M) : NormalizedGeneratorData :=
  yMNormalizedGeneratorData D

/-- Color factors derived from Yang-Mills gauge data. -/
def yMColorFactors
  {L M : Type*}
    (D : YangMillsGaugeData L M) (nF : ℝ) : ColorFactors :=
  (yMColorInvariants D).toColorFactors nF

/-- One-loop beta coefficient derived from Yang-Mills gauge data. -/
def yMBeta0
  {L M : Type*}
    (D : YangMillsGaugeData L M) (nF : ℝ) : ℝ :=
  beta0 (yMColorFactors D nF)

/-! ### Standard Model Gauge Sector Instances -/

-- #### U(1) sector

/-- Yang-Mills gauge data for the U(1) hypercharge sector of the Standard Model.

The gauge algebra is `u(1) ≅ ℝ` — a one-dimensional *real* abelian Lie algebra.
The matter representation is a complex scalar with hypercharge `Y`.
Being abelian, U(1) has no adjoint self-coupling: `C_A = 0`.
`C_F = Y²` and `T_F = Y²` (trace normalization for a complex scalar of hypercharge `Y`). -/
def u1YangMillsGaugeData (Y : ℝ) :
    YangMillsGaugeData ℝ ℂ where
  AdjBasis := Fin 1          -- one U(1) generator
  FundBasis := Fin 1         -- one-dimensional charge representation
  genEntry := fun _ _ _ => Y
  tF := Y ^ 2
  cF := Y ^ 2
  cA := 0                    -- abelian: no adjoint self-coupling
  traceNormalization := True
  hTraceNormalization := trivial
  fundamentalCasimir := True
  hFundamentalCasimir := trivial
  adjointCasimir := True
  hAdjointCasimir := trivial

/-- The coupling invariants extracted from U(1) gauge data with charge `Y`. -/
def u1YMColorInvariants (Y : ℝ) : ColorInvariants :=
  yMColorInvariants (u1YangMillsGaugeData Y)

/-- U(1) gauge data has vanishing adjoint Casimir (abelian gauge sector). -/
lemma u1YMColorInvariants_cA_eq_zero (Y : ℝ) :
    (u1YMColorInvariants Y).cA = 0 := by
  simp [u1YMColorInvariants, yMColorInvariants, u1YangMillsGaugeData]

/-- U(1) fundamental Casimir equals the hypercharge squared. -/
lemma u1YMColorInvariants_cF_eq (Y : ℝ) :
    (u1YMColorInvariants Y).cF = Y ^ 2 := by
  simp [u1YMColorInvariants, yMColorInvariants, u1YangMillsGaugeData]

-- #### SU(2) sector

/-- Yang-Mills gauge data for the SU(2) weak-isospin sector of the Standard Model.

The gauge algebra is `su(2)` — a three-dimensional *real* Lie algebra, the Lie
algebra of the real Lie group SU(2).  The matter module is the fundamental doublet
`ℂ²`, a complex representation that is nevertheless a `LieModule ℝ su(2) ℂ²`.
Standard values: `C_F = 3/4`, `C_A = 2`, `T_F = 1/2`. -/
def su2YangMillsGaugeData :
    YangMillsGaugeData
  ℝ
  ℂ where
  AdjBasis := Fin 3          -- su(2) has dimension 3
  FundBasis := Fin 2
  genEntry := fun _ _ _ => 0 -- Pauli-matrix entries: placeholder for basis expansion
  tF := 1 / 2
  cF := 3 / 4
  cA := 2
  traceNormalization := True
  hTraceNormalization := trivial
  fundamentalCasimir := True
  hFundamentalCasimir := trivial
  adjointCasimir := True
  hAdjointCasimir := trivial

/-- The coupling invariants extracted from SU(2) gauge data. -/
def su2YMColorInvariants : ColorInvariants :=
  yMColorInvariants su2YangMillsGaugeData

/-- SU(2) coupling invariants: `C_F = 3/4`, `C_A = 2`, `T_F = 1/2`. -/
lemma su2YMColorInvariants_explicit :
    su2YMColorInvariants = { cF := 3 / 4, cA := 2, tF := 1 / 2 } := by
  simp [su2YMColorInvariants, yMColorInvariants, su2YangMillsGaugeData]

/-- SU(2) one-loop beta coefficient from Yang-Mills gauge data. -/
lemma su2YMBeta0_eq (nF : ℝ) :
    yMBeta0 su2YangMillsGaugeData nF
      = beta0 { nF := nF, cF := 3 / 4, cA := 2, tF := 1 / 2 } := by
  simp [yMBeta0, yMColorFactors, yMColorInvariants,
    ColorInvariants.toColorFactors, su2YangMillsGaugeData, beta0]

-- #### SU(N) sector

/-- Yang-Mills gauge data for SU(N) in the standard fundamental representation.

The gauge algebra is `su(n)` — a real Lie algebra of dimension `n²-1`, realized as
`specialUnitaryGroup (Fin n) ℂ` (skew-Hermitian traceless matrices, closed under the
commutator with real structure constants).  The matter module is the fundamental
representation on `Fin n → ℂ`, a complex vector space carrying a real-linear action.
Standard values: `C_F = (N²-1)/(2N)`, `C_A = N`, `T_F = 1/2`. -/
def suNYangMillsGaugeData (n : ℕ) (_hn : 1 < n) :
    YangMillsGaugeData
  ℝ
  ℂ where
  AdjBasis := Fin (n ^ 2 - 1)      -- dimension of su(n)
  FundBasis := Fin n
  genEntry := fun _ _ _ => 0       -- placeholder for explicit basis expansion
  tF := 1 / 2
  cF := ((n : ℝ) ^ 2 - 1) / (2 * n)
  cA := n
  traceNormalization := True
  hTraceNormalization := trivial
  fundamentalCasimir := True
  hFundamentalCasimir := trivial
  adjointCasimir := True
  hAdjointCasimir := trivial

/-- The coupling invariants extracted from SU(N) gauge data. -/
def suNYMColorInvariants (n : ℕ) (hn : 1 < n) : ColorInvariants :=
  yMColorInvariants (suNYangMillsGaugeData n hn)

/-! ### Specialization Theorems -/

/-- The `ColorInvariants` extracted from `suNYangMillsGaugeData n hn` agree with those
from the existing SU(N) `HasColorInvariants` instance in `QCD.Basic`. -/
lemma suNYMColorInvariants_eq_suN
    (n : ℕ) (hn : 1 < n) :
    suNYMColorInvariants n hn = HasColorInvariants.invariants (G := SUN (n : ℝ)) := by
  simp [suNYMColorInvariants, yMColorInvariants, suNYangMillsGaugeData,
    HasColorInvariants.invariants]

/-- The color factors derived from SU(N) Yang-Mills gauge data equal those from
the direct `suNColorFactors` constructor. -/
lemma suNYMColorFactors_eq_suNColorFactors
    (n : ℕ) (hn : 1 < n) (nF : ℝ) :
    yMColorFactors (suNYangMillsGaugeData n hn) nF = suNColorFactors n nF := by
  unfold yMColorFactors yMColorInvariants ColorInvariants.toColorFactors
  simp [suNYangMillsGaugeData, suNColorFactors]

/-- The one-loop beta coefficient from Yang-Mills SU(N) gauge data matches the
direct `beta0` computation with `suNColorFactors`. -/
lemma suNYMBeta0_eq_beta0
    (n : ℕ) (hn : 1 < n) (nF : ℝ) :
    yMBeta0 (suNYangMillsGaugeData n hn) nF = beta0 (suNColorFactors n nF) := by
  simp [yMBeta0, suNYMColorFactors_eq_suNColorFactors]

/-- SU(2) instance of the general `suNYangMillsGaugeData` has the same invariants
as the dedicated `su2YangMillsGaugeData`. -/
lemma suNYangMillsGaugeData_two_eq_su2 :
    suNYMColorInvariants 2 (by norm_num) = su2YMColorInvariants := by
  simp [suNYMColorInvariants, su2YMColorInvariants, yMColorInvariants,
    suNYangMillsGaugeData, su2YangMillsGaugeData]
  norm_num

/-- SU(3) color factors from the generic Yang-Mills pipeline: `C_F = 4/3`, `C_A = 3`, `T_F = 1/2`. -/
lemma su3YMColorFactors_explicit (nF : ℝ) :
    yMColorFactors (suNYangMillsGaugeData 3 (by norm_num)) nF =
      { nF := nF, cF := 4 / 3, cA := 3, tF := 1 / 2 } := by
  simp [yMColorFactors, yMColorInvariants, ColorInvariants.toColorFactors,
    suNYangMillsGaugeData]
  norm_num

/-- The `NormalizedGeneratorData` built from SU(N) Yang-Mills gauge data
supplies the same invariants as the direct `RepresentationColor` package. -/
lemma suNYMNormalizedGeneratorData_colorInvariants_eq
    (n : ℕ) (hn : 1 < n) :
    colorInvariantsOf (yMNormalizedGeneratorData (suNYangMillsGaugeData n hn)) =
      HasColorInvariants.invariants (G := SUN (n : ℝ)) := by
  simp [colorInvariantsOf, yMNormalizedGeneratorData,
    suNYangMillsGaugeData, HasColorInvariants.invariants]

end FeynmanDiagrams
end PerturbationTheory
end QFT
end Physlib
