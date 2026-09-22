/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.CasimirDerivation
public import Physlib.Relativity.PauliMatrices.Basic
/-!

# Genuine `su(2)` normalized generator data

`Physlib.QFT.QCD.RepresentationColor` packages representation-theoretic input for
colour-factor extraction in `NormalizedGeneratorData`, together with three identities
that such a package is supposed to satisfy:

* `NormalizedGeneratorData.TraceIdentity` — `Tr(TᵃTᵇ) = T_F δᵃᵇ`;
* `NormalizedGeneratorData.FundamentalCasimirIdentity` — `Σₐ TᵃTᵃ = C_F 1`;
* `NormalizedGeneratorData.AdjointCasimirIdentity` — `f^{acd} f^{bcd} = C_A δᵃᵇ`.

Until now the only package satisfying all three was the abelian `u1NormalizedData`.
This module supplies the first genuinely non-abelian one: the fundamental
representation of `su(2)`, with generators `Tᵃ = σᵃ / 2` built from
`PauliMatrix.pauliMatrix`, structure constants `f^{abc} = ε^{abc}`, and the standard
invariants `T_F = 1/2`, `C_F = 3/4`, `C_A = 2`.

All three identities are *proved*, and — unlike the placeholder packages — the
`Prop`-valued contract fields of `NormalizedGeneratorData` are instantiated to those
same identities rather than to a reflexive triviality, so they assert something.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace RepresentationColor

open PauliMatrix

/-! ### Data -/

/-- The three-index Levi-Civita symbol on `Fin 3`, real valued.

Mathlib at this pin has no Levi-Civita symbol, so it is given here as an explicit
table: `ε^{012} = ε^{120} = ε^{201} = 1`, `ε^{021} = ε^{210} = ε^{102} = -1`, and
`ε` vanishes whenever two indices coincide. -/
def epsilon3 : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

/-- Matrix entries of the fundamental `su(2)` generators `Tᵃ = σᵃ / 2`.

These are genuinely complex: `T² = σ²/2 = (1/2) · !![0, -I; I, 0]`. -/
def su2GenEntry (a : Fin 3) (i j : Fin 2) : ℂ :=
  (1 / 2 : ℂ) * pauliMatrix (Sum.inr a) i j

/-- Kronecker delta on the adjoint index set of `su(2)`. -/
def su2DeltaAdj (a b : Fin 3) : ℝ := if a = b then 1 else 0

/-- Kronecker delta on the fundamental index set of `su(2)`. -/
def su2DeltaFund (i j : Fin 2) : ℝ := if i = j then 1 else 0

/-! ### The three identities, stated concretely

These are the statements that the `Prop`-valued contract fields of the package below
are instantiated to.  Stating them separately keeps the package readable and lets the
same proposition be used both as the contract and as the witness for
`NormalizedGeneratorData.TraceIdentity` and friends. -/

/-- Trace normalization for `su(2)`: `Σᵢⱼ (Tᵃ)ᵢⱼ (Tᵇ)ⱼᵢ = (1/2) δᵃᵇ`. -/
def SU2TraceStatement : Prop :=
  ∀ a b : Fin 3,
    (∑ i : Fin 2, ∑ j : Fin 2, su2GenEntry a i j * su2GenEntry b j i)
      = ((1 / 2 : ℝ) : ℂ) * ((su2DeltaAdj a b : ℝ) : ℂ)

/-- Fundamental Casimir for `su(2)`: `Σₐ Σₖ (Tᵃ)ᵢₖ (Tᵃ)ₖⱼ = (3/4) δᵢⱼ`. -/
def SU2FundamentalStatement : Prop :=
  ∀ i j : Fin 2,
    (∑ a : Fin 3, ∑ k : Fin 2, su2GenEntry a i k * su2GenEntry a k j)
      = ((3 / 4 : ℝ) : ℂ) * ((su2DeltaFund i j : ℝ) : ℂ)

/-- Adjoint Casimir for `su(2)`: `Σ_{cd} ε^{acd} ε^{bcd} = 2 δᵃᵇ`. -/
def SU2AdjointStatement : Prop :=
  ∀ a b : Fin 3,
    (∑ c : Fin 3, ∑ d : Fin 3, epsilon3 a c d * epsilon3 b c d)
      = (2 : ℝ) * su2DeltaAdj a b

/-! ### Proofs of the identities -/

/-- The fundamental `su(2)` generators `σᵃ/2` are trace-normalized with `T_F = 1/2`. -/
theorem su2TraceStatement : SU2TraceStatement := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [su2GenEntry, su2DeltaAdj, Fin.sum_univ_two, pauliMatrix, Complex.ext_iff] <;>
    norm_num

/-- The fundamental `su(2)` Casimir: `Σₐ (σᵃ/2)(σᵃ/2) = (3/4) · 1`. -/
theorem su2FundamentalStatement : SU2FundamentalStatement := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [su2GenEntry, su2DeltaFund, Fin.sum_univ_two, Fin.sum_univ_three, pauliMatrix,
      Complex.ext_iff] <;>
    norm_num

/-- The adjoint `su(2)` Casimir: `Σ_{cd} ε^{acd} ε^{bcd} = 2 δᵃᵇ`, i.e. `C_A = 2`. -/
theorem su2AdjointStatement : SU2AdjointStatement := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [epsilon3, su2DeltaAdj, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.vecHead, Matrix.vecTail] <;>
    norm_num

/-! ### The package -/

/-- Normalized generator data for the fundamental representation of `su(2)`.

Unlike `sunNormalizedData`, the generator entries are the real thing — `Tᵃ = σᵃ/2` —
and the three `Prop`-valued contract fields are instantiated to the actual identities
`SU2TraceStatement`, `SU2FundamentalStatement`, `SU2AdjointStatement`, each discharged
by a proof rather than by `rfl` on a triviality. -/
def su2NormalizedData : NormalizedGeneratorData where
  AdjIndex := Fin 3
  FundIndex := Fin 2
  adjFintype := inferInstance
  fundFintype := inferInstance
  genEntry := su2GenEntry
  structConst := epsilon3
  deltaAdj := su2DeltaAdj
  deltaFund := su2DeltaFund
  tF := 1 / 2
  cF := 3 / 4
  cA := 2
  traceNormalization := SU2TraceStatement
  hTraceNormalization := su2TraceStatement
  fundamentalCasimir := SU2FundamentalStatement
  hFundamentalCasimir := su2FundamentalStatement
  adjointCasimir := SU2AdjointStatement
  hAdjointCasimir := su2AdjointStatement

/-- `su(2)` satisfies the trace-normalization identity of `NormalizedGeneratorData`. -/
theorem su2NormalizedData_traceIdentity : su2NormalizedData.TraceIdentity :=
  su2TraceStatement

/-- `su(2)` satisfies the fundamental Casimir identity of `NormalizedGeneratorData`. -/
theorem su2NormalizedData_fundamentalIdentity :
    su2NormalizedData.FundamentalCasimirIdentity :=
  su2FundamentalStatement

/-- `su(2)` satisfies the adjoint Casimir identity of `NormalizedGeneratorData`. -/
theorem su2NormalizedData_adjointIdentity : su2NormalizedData.AdjointCasimirIdentity :=
  su2AdjointStatement

/-- The `su(2)` sector carries a full derivation package: all three
representation-level identities are proved, not assumed, and the contract bridges are
the identity map because the contracts *are* the identities. -/
def su2CasimirDerivationAssumptions :
    CasimirDerivationAssumptions su2NormalizedData where
  hTraceIdentity := su2NormalizedData_traceIdentity
  hFundamentalIdentity := su2NormalizedData_fundamentalIdentity
  hAdjointIdentity := su2NormalizedData_adjointIdentity
  traceImpliesContract := fun h => h
  fundamentalImpliesContract := fun h => h
  adjointImpliesContract := fun h => h

/-- The colour invariants of the genuine `su(2)` package are the standard ones. -/
theorem su2NormalizedData_colorInvariants :
    colorInvariantsOf su2NormalizedData = { cF := 3 / 4, cA := 2, tF := 1 / 2 } := by
  rfl

end RepresentationColor
end QCD
end QFT
end Physlib
