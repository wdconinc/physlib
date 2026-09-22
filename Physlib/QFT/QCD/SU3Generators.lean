/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.SU2Generators
/-!

# Genuine `su(3)` normalized generator data

The `su(2)` package of `Physlib.QFT.QCD.SU2Generators` is repeated here for `su(3)`,
the colour algebra of QCD: generators `Tᵃ = λᵃ / 2` built from the Gell-Mann matrices,
structure constants `f^{abc}` given by the standard table, and invariants
`T_F = 1/2`, `C_F = 4/3`, `C_A = 3`.

Mathlib at this pin has no Gell-Mann matrices, so they are defined here.  Everything
about the eighth generator is controlled by `invSqrt3 = 1/√3`; it is kept opaque and
handled through `invSqrt3_mul_self` rather than unfolded, so that the case sweeps stay
arithmetic in `ℂ`.

As in the `su(2)` module, all three representation-level identities are proved and the
`Prop`-valued contract fields of `NormalizedGeneratorData` are instantiated to those
identities instead of to a reflexive triviality.

-/

@[expose] public section

-- The identity proofs below are 64-case sweeps over explicit 3x3 / 8x8x8 tables;
-- they need considerably more than the default elaboration budget.
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace RepresentationColor

open Matrix Complex

/-! ### The irrational normalization of the eighth generator -/

/-- `√3`, the normalization appearing in the eighth Gell-Mann matrix and in the
structure constants `f^{458} = f^{678} = √3/2`. -/
def rt3 : ℝ := Real.sqrt 3

lemma rt3_mul_self : rt3 * rt3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

lemma rt3_sq : rt3 ^ 2 = 3 := by
  rw [sq, rt3_mul_self]

/-- `1/√3`, as a complex number.  Deliberately opaque: the proofs below never unfold
it, they only use `invSqrt3_mul_self`. -/
def invSqrt3 : ℂ := ((rt3⁻¹ : ℝ) : ℂ)

lemma invSqrt3_mul_self : invSqrt3 * invSqrt3 = (3 : ℂ)⁻¹ := by
  rw [invSqrt3, ← Complex.ofReal_mul, ← mul_inv, rt3_mul_self]
  norm_num

lemma invSqrt3_sq : invSqrt3 ^ 2 = (3 : ℂ)⁻¹ := by
  rw [sq, invSqrt3_mul_self]

/-! ### Data -/

/-- The Gell-Mann matrices `λ¹, …, λ⁸`, indexed by `Fin 8` (so `gellMann3 0 = λ¹`). -/
def gellMann3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  | 1 => !![0, -I, 0; I, 0, 0; 0, 0, 0]
  | 2 => !![1, 0, 0; 0, -1, 0; 0, 0, 0]
  | 3 => !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  | 4 => !![0, 0, -I; 0, 0, 0; I, 0, 0]
  | 5 => !![0, 0, 0; 0, 0, 1; 0, 1, 0]
  | 6 => !![0, 0, 0; 0, 0, -I; 0, I, 0]
  | 7 => !![invSqrt3, 0, 0; 0, invSqrt3, 0; 0, 0, -2 * invSqrt3]

/-- Matrix entries of the fundamental `su(3)` generators `Tᵃ = λᵃ / 2`. -/
def su3GenEntry (a : Fin 8) (i j : Fin 3) : ℂ :=
  (1 / 2 : ℂ) * gellMann3 a i j

/-- The `su(3)` structure constants `f^{abc}`, indexed by `Fin 8` (so the entry
`0, 1, 2` is the standard `f^{123} = 1`).  Totally antisymmetric; the nonzero
independent values are `f^{123} = 1`, `f^{147} = f^{246} = f^{257} = f^{345} = 1/2`,
`f^{156} = f^{367} = -1/2` and `f^{458} = f^{678} = √3/2`. -/
def structConst3 : Fin 8 → Fin 8 → Fin 8 → ℝ
  | 0, 1, 2 => 1
  | 0, 2, 1 => -1
  | 0, 3, 6 => 1 / 2
  | 0, 4, 5 => -(1 / 2)
  | 0, 5, 4 => 1 / 2
  | 0, 6, 3 => -(1 / 2)
  | 1, 0, 2 => -1
  | 1, 2, 0 => 1
  | 1, 3, 5 => 1 / 2
  | 1, 4, 6 => 1 / 2
  | 1, 5, 3 => -(1 / 2)
  | 1, 6, 4 => -(1 / 2)
  | 2, 0, 1 => 1
  | 2, 1, 0 => -1
  | 2, 3, 4 => 1 / 2
  | 2, 4, 3 => -(1 / 2)
  | 2, 5, 6 => -(1 / 2)
  | 2, 6, 5 => 1 / 2
  | 3, 0, 6 => -(1 / 2)
  | 3, 1, 5 => -(1 / 2)
  | 3, 2, 4 => -(1 / 2)
  | 3, 4, 2 => 1 / 2
  | 3, 4, 7 => rt3 / 2
  | 3, 5, 1 => 1 / 2
  | 3, 6, 0 => 1 / 2
  | 3, 7, 4 => -(rt3 / 2)
  | 4, 0, 5 => 1 / 2
  | 4, 1, 6 => -(1 / 2)
  | 4, 2, 3 => 1 / 2
  | 4, 3, 2 => -(1 / 2)
  | 4, 3, 7 => -(rt3 / 2)
  | 4, 5, 0 => -(1 / 2)
  | 4, 6, 1 => 1 / 2
  | 4, 7, 3 => rt3 / 2
  | 5, 0, 4 => -(1 / 2)
  | 5, 1, 3 => 1 / 2
  | 5, 2, 6 => 1 / 2
  | 5, 3, 1 => -(1 / 2)
  | 5, 4, 0 => 1 / 2
  | 5, 6, 2 => -(1 / 2)
  | 5, 6, 7 => rt3 / 2
  | 5, 7, 6 => -(rt3 / 2)
  | 6, 0, 3 => 1 / 2
  | 6, 1, 4 => 1 / 2
  | 6, 2, 5 => -(1 / 2)
  | 6, 3, 0 => -(1 / 2)
  | 6, 4, 1 => -(1 / 2)
  | 6, 5, 2 => 1 / 2
  | 6, 5, 7 => -(rt3 / 2)
  | 6, 7, 5 => rt3 / 2
  | 7, 3, 4 => rt3 / 2
  | 7, 4, 3 => -(rt3 / 2)
  | 7, 5, 6 => rt3 / 2
  | 7, 6, 5 => -(rt3 / 2)
  | _, _, _ => 0

/-- Kronecker delta on the adjoint index set of `su(3)`. -/
def su3DeltaAdj (a b : Fin 8) : ℝ := if a = b then 1 else 0

/-- Kronecker delta on the fundamental index set of `su(3)`. -/
def su3DeltaFund (i j : Fin 3) : ℝ := if i = j then 1 else 0

/-! ### The three identities, stated concretely -/

/-- Trace normalization for `su(3)`: `Σᵢⱼ (Tᵃ)ᵢⱼ (Tᵇ)ⱼᵢ = (1/2) δᵃᵇ`. -/
def SU3TraceStatement : Prop :=
  ∀ a b : Fin 8,
    (∑ i : Fin 3, ∑ j : Fin 3, su3GenEntry a i j * su3GenEntry b j i)
      = ((1 / 2 : ℝ) : ℂ) * ((su3DeltaAdj a b : ℝ) : ℂ)

/-- Fundamental Casimir for `su(3)`: `Σₐ Σₖ (Tᵃ)ᵢₖ (Tᵃ)ₖⱼ = (4/3) δᵢⱼ`. -/
def SU3FundamentalStatement : Prop :=
  ∀ i j : Fin 3,
    (∑ a : Fin 8, ∑ k : Fin 3, su3GenEntry a i k * su3GenEntry a k j)
      = ((4 / 3 : ℝ) : ℂ) * ((su3DeltaFund i j : ℝ) : ℂ)

/-- Adjoint Casimir for `su(3)`: `Σ_{cd} f^{acd} f^{bcd} = 3 δᵃᵇ`. -/
def SU3AdjointStatement : Prop :=
  ∀ a b : Fin 8,
    (∑ c : Fin 8, ∑ d : Fin 8, structConst3 a c d * structConst3 b c d)
      = (3 : ℝ) * su3DeltaAdj a b

/-! ### Proofs of the identities -/

/-- The fundamental `su(3)` generators `λᵃ/2` are trace-normalized with `T_F = 1/2`. -/
theorem su3TraceStatement : SU3TraceStatement := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [su3GenEntry, su3DeltaAdj, gellMann3, Fin.sum_univ_three] <;>
    ring_nf <;>
    simp [invSqrt3_sq, Complex.I_sq] <;>
    ring_nf

/-- The fundamental `su(3)` Casimir: `Σₐ (λᵃ/2)(λᵃ/2) = (4/3) · 1`. -/
theorem su3FundamentalStatement : SU3FundamentalStatement := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [su3GenEntry, su3DeltaFund, gellMann3, Fin.sum_univ_three, Fin.sum_univ_eight] <;>
    ring_nf <;>
    simp [invSqrt3_sq, Complex.I_sq] <;>
    ring_nf

/-- The adjoint `su(3)` Casimir: `Σ_{cd} f^{acd} f^{bcd} = 3 δᵃᵇ`, i.e. `C_A = 3`. -/
theorem su3AdjointStatement : SU3AdjointStatement := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [structConst3, su3DeltaAdj, Fin.sum_univ_eight] <;>
    ring_nf <;>
    simp [rt3_sq, rt3_mul_self] <;>
    ring_nf

/-! ### The package -/

/-- Normalized generator data for the fundamental representation of `su(3)`: the
colour algebra of QCD, with `T_F = 1/2`, `C_F = 4/3`, `C_A = 3`.

As for `su2NormalizedData`, the generator entries are real matrices and the three
`Prop`-valued contract fields are instantiated to the actual identities. -/
def su3NormalizedData : NormalizedGeneratorData where
  AdjIndex := Fin 8
  FundIndex := Fin 3
  adjFintype := inferInstance
  fundFintype := inferInstance
  genEntry := su3GenEntry
  structConst := structConst3
  deltaAdj := su3DeltaAdj
  deltaFund := su3DeltaFund
  tF := 1 / 2
  cF := 4 / 3
  cA := 3
  traceNormalization := SU3TraceStatement
  hTraceNormalization := su3TraceStatement
  fundamentalCasimir := SU3FundamentalStatement
  hFundamentalCasimir := su3FundamentalStatement
  adjointCasimir := SU3AdjointStatement
  hAdjointCasimir := su3AdjointStatement

/-- `su(3)` satisfies the trace-normalization identity of `NormalizedGeneratorData`. -/
theorem su3NormalizedData_traceIdentity : su3NormalizedData.TraceIdentity :=
  su3TraceStatement

/-- `su(3)` satisfies the fundamental Casimir identity of `NormalizedGeneratorData`. -/
theorem su3NormalizedData_fundamentalIdentity :
    su3NormalizedData.FundamentalCasimirIdentity :=
  su3FundamentalStatement

/-- `su(3)` satisfies the adjoint Casimir identity of `NormalizedGeneratorData`. -/
theorem su3NormalizedData_adjointIdentity : su3NormalizedData.AdjointCasimirIdentity :=
  su3AdjointStatement

/-- The `su(3)` sector carries a full derivation package: all three
representation-level identities are proved, not assumed. -/
def su3CasimirDerivationAssumptions :
    CasimirDerivationAssumptions su3NormalizedData where
  hTraceIdentity := su3NormalizedData_traceIdentity
  hFundamentalIdentity := su3NormalizedData_fundamentalIdentity
  hAdjointIdentity := su3NormalizedData_adjointIdentity
  traceImpliesContract := fun h => h
  fundamentalImpliesContract := fun h => h
  adjointImpliesContract := fun h => h

/-- The colour invariants of the genuine `su(3)` package are the standard QCD ones. -/
theorem su3NormalizedData_colorInvariants :
    colorInvariantsOf su3NormalizedData = { cF := 4 / 3, cA := 3, tF := 1 / 2 } := by
  rfl

end RepresentationColor
end QCD
end QFT
end Physlib
