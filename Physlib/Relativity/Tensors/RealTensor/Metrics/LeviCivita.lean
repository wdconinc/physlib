/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
public import Physlib.Relativity.MinkowskiMatrix
public import Physlib.Mathematics.KroneckerDelta

@[expose] public section

open Matrix KroneckerDelta

noncomputable section

namespace realLorentzTensor

/-- The rank-4 Levi-Civita symbol in 3+1 dimensions, as an integer-valued tensor coefficient.
The value is `0` unless `(μ, ν, ρ, σ)` is a permutation of `(0,1,2,3)`, in which case it is
the sign of that permutation.

This is fundamentally a generalized Kronecker delta: it computes the determinant of the
permutation matrix mapping the indices to the standard basis. The Levi-Civita symbol and
generalized Kronecker delta are equivalent abstractions for capturing permutation signatures. -/
-- This definition is intentionally 3+1-dimensional: the index type is fixed to `Fin 4`.
abbrev leviCivita4Int (μ ν ρ σ : Fin 4) : ℤ :=
  generalizedKroneckerDelta ![μ, ν, ρ, σ] id

/-- The rank-4 contravariant Levi-Civita symbol in 3+1 dimensions.
With signature `(+, -, -, -)`, each index raise contributes a diagonal metric factor,
so raising all four indices contributes the product
`η μ μ * η ν ν * η ρ ρ * η σ σ`.

This is the negative of the covariant Levi-Civita symbol, also a generalized Kronecker delta
up to sign. -/
def fin4ToMinkowskiIdx : Fin 4 → Fin 1 ⊕ Fin 3
  | ⟨0, _⟩ => Sum.inl 0
  | ⟨n + 1, hn⟩ => Sum.inr ⟨n, by omega⟩

def metricDiagSignInt (i : Fin 4) : ℤ :=
  if minkowskiMatrix (fin4ToMinkowskiIdx i) (fin4ToMinkowskiIdx i) = (1 : ℝ) then 1 else -1

lemma metricDiagSignInt_eq_if_zero (i : Fin 4) :
    metricDiagSignInt i = if i.1 = 0 then 1 else -1 := by
  fin_cases i <;> simp [metricDiagSignInt, fin4ToMinkowskiIdx] <;> norm_num

def leviCivita4UpInt (μ ν ρ σ : Fin 4) : ℤ :=
  - leviCivita4Int μ ν ρ σ

lemma metricDiagSignInt_mul_leviCivita4Int (μ ν ρ σ : Fin 4) :
    (metricDiagSignInt μ * metricDiagSignInt ν * metricDiagSignInt ρ * metricDiagSignInt σ)
      * leviCivita4Int μ ν ρ σ
      = -leviCivita4Int μ ν ρ σ := by
  have h :
      ∀ μ ν ρ σ : Fin 4,
        ((if μ.1 = 0 then 1 else -1) * (if ν.1 = 0 then 1 else -1)
          * (if ρ.1 = 0 then 1 else -1) * (if σ.1 = 0 then 1 else -1))
          * leviCivita4Int μ ν ρ σ
          = -leviCivita4Int μ ν ρ σ := by
    decide
  simpa [metricDiagSignInt_eq_if_zero] using h μ ν ρ σ

lemma leviCivita4UpInt_eq_neg (μ ν ρ σ : Fin 4) :
    leviCivita4UpInt μ ν ρ σ = -leviCivita4Int μ ν ρ σ := by
  unfold leviCivita4UpInt
  simpa using metricDiagSignInt_mul_leviCivita4Int μ ν ρ σ

/- The two-index Levi-Civita contraction identity
`ε^{μνρσ} ε_{μντω} = -2 (g^ρ_τ g^σ_ω - g^ρ_ω g^σ_τ)`,
where each mixed metric factor is a Kronecker delta. -/
lemma leviCivita4UpInt_contract_two (ρ σ τ ω : Fin 4) :
    (∑ μ, ∑ ν,
      leviCivita4UpInt μ ν ρ σ * leviCivita4Int μ ν τ ω)
      = (-2 : ℤ) *
        ((if ρ = τ then 1 else 0) * (if σ = ω then 1 else 0)
          - (if ρ = ω then 1 else 0) * (if σ = τ then 1 else 0)) := by
  have h :
      ∀ ρ σ τ ω : Fin 4,
        (∑ μ, ∑ ν,
          (-leviCivita4Int μ ν ρ σ) * leviCivita4Int μ ν τ ω)
          = (-2 : ℤ) *
            ((if ρ = τ then 1 else 0) * (if σ = ω then 1 else 0)
              - (if ρ = ω then 1 else 0) * (if σ = τ then 1 else 0)) := by
    decide
  simpa [leviCivita4UpInt_eq_neg] using h ρ σ τ ω

/- The three-index Levi-Civita contraction identity
`ε^{μνρσ} ε_{μνρτ} = -6 g^σ_τ`,
where the result is a mixed metric (Kronecker delta). -/
lemma leviCivita4UpInt_contract_three (σ τ : Fin 4) :
    (∑ μ, ∑ ν, ∑ ρ,
      leviCivita4UpInt μ ν ρ σ * leviCivita4Int μ ν ρ τ)
      = (-6 : ℤ) * (if σ = τ then 1 else 0) := by
  have h : ∀ σ τ : Fin 4,
    (∑ μ, ∑ ν, ∑ ρ,
      (-leviCivita4Int μ ν ρ σ) * leviCivita4Int μ ν ρ τ)
      = (-6 : ℤ) * (if σ = τ then 1 else 0) := by
    decide
  simpa [leviCivita4UpInt_eq_neg] using h σ τ

/- The four-index Levi-Civita contraction identity
`ε^{μνρσ} ε_{μνρσ} = -24`. -/
lemma leviCivita4UpInt_contract_four :
    (∑ μ, ∑ ν, ∑ ρ, ∑ σ,
      leviCivita4UpInt μ ν ρ σ * leviCivita4Int μ ν ρ σ)
      = (-24 : ℤ) := by
  have h :
      (∑ μ, ∑ ν, ∑ ρ, ∑ σ,
        (-leviCivita4Int μ ν ρ σ) * leviCivita4Int μ ν ρ σ)
        = (-24 : ℤ) := by
    decide
  simpa [leviCivita4UpInt_eq_neg] using h

end realLorentzTensor
