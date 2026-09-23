/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.CasimirDerivation
public import Mathlib.Analysis.Real.Sqrt
/-!

# Generalized Gell-Mann generators for `su(N)`

`Physlib.QFT.QCD.SU2Generators` and `Physlib.QFT.QCD.SU3Generators` supply explicit
generator matrices for the two smallest colour algebras by writing out finite tables.
That route does not generalize: the tables grow like `N²`, and the proofs are case
sweeps.  This module gives the construction for *every* `N` at once.

## The basis

The generalized Gell-Mann basis of `su(N)` has `N² - 1` elements in three families,
indexed here by

```
SUNIndex N = OffPair N ⊕ OffPair N ⊕ Fin (N - 1)
```

where `OffPair N = {p : Fin N × Fin N // p.1 < p.2}`.  A sum type is used rather than
`Fin (N² - 1)`: the three families need genuinely different arguments in every proof
below, and a sum type makes the case split structural (`rcases a with o | o | d`)
instead of arithmetic.  The price is that the count `#(SUNIndex N) = N² - 1` is not
definitional; it is not needed for the trace identity.

With `Tᵃ = λᵃ/2` the three families are

* `Sum.inl ⟨(j,k),_⟩`: the symmetric pair `(E_{jk} + E_{kj})/2`;
* `Sum.inr (Sum.inl ⟨(j,k),_⟩)`: the antisymmetric pair `-i(E_{jk} - E_{kj})/2`;
* `Sum.inr (Sum.inr l)`: the diagonal generator
  `diag(1,…,1,-L,0,…,0) / √(2L(L+1))` with `L = l+1` ones.

Matrices are never formed: everything is written in entries, because
`NormalizedGeneratorData.TraceIdentity` is itself an identity between entry sums.
`Matrix.single` would work equally well, but the entry form keeps the algebra inside
`Finset.sum` lemmas that `simp` already knows.

## What is proved

`suNTraceStatement` — `Tr(TᵃTᵇ) = (1/2) δᵃᵇ` for every `N` and every pair of
generators, all nine family pairs.  This is the identity that fixes `T_F = 1/2`, and it
is what lets `sunNormalizedData` and `suNYangMillsGaugeData` carry real generator
entries instead of the zero placeholder.

The fundamental Casimir `C_F = (N²-1)/(2N)` and the adjoint Casimir `C_A = N` are not
proved here; see the closing note.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace RepresentationColor

namespace SUNGen

open Complex

variable {N : ℕ}

/-! ### Kronecker delta and matrix units -/

/-- Kronecker delta on the fundamental index set, complex valued. -/
def kd (i j : Fin N) : ℂ := if i = j then 1 else 0

lemma kd_self (i : Fin N) : kd i i = 1 := by simp [kd]

lemma kd_eq_zero {i j : Fin N} (h : i ≠ j) : kd i j = 0 := by simp [kd, h]

lemma kd_comm (i j : Fin N) : kd i j = kd j i := by
  by_cases h : i = j
  · simp [h]
  · simp [kd, h, Ne.symm h]

/-- Collapsing a sum against a Kronecker delta. -/
lemma kd_sum (f : Fin N → ℂ) (j : Fin N) : (∑ i : Fin N, kd i j * f i) = f j := by
  simp [kd, ite_mul]

lemma kd_kd_sum (j q : Fin N) : (∑ i : Fin N, kd i j * kd i q) = kd j q :=
  kd_sum (fun i => kd i q) j

/-- The trace of a product of two matrix units: `Tr(E_{jk} E_{pq}) = δ_{jq} δ_{kp}`.
Every off-diagonal case below is four applications of this lemma. -/
lemma sum_unit (j k p q : Fin N) :
    (∑ i : Fin N, ∑ l : Fin N, (kd i j * kd l k) * (kd l p * kd i q)) = kd j q * kd k p := by
  have h : ∀ i : Fin N, (∑ l : Fin N, (kd i j * kd l k) * (kd l p * kd i q))
      = (kd i j * kd i q) * kd k p := by
    intro i
    have h2 : ∀ l : Fin N, (kd i j * kd l k) * (kd l p * kd i q)
        = (kd i j * kd i q) * (kd l k * kd l p) := by
      intro l; ring
    rw [Finset.sum_congr rfl (fun l _ => h2 l), ← Finset.mul_sum, kd_kd_sum]
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.sum_mul, kd_kd_sum]

/-- Two Kronecker deltas on a pair of indices. -/
lemma kd_pair (j k j' k' : Fin N) :
    kd j j' * kd k k' = if j = j' ∧ k = k' then 1 else 0 := by
  by_cases h1 : j = j' <;> by_cases h2 : k = k' <;> simp [kd, h1, h2]

/-- The "crossed" delta product vanishes on ordered pairs: `j < k` and `j' < k'` cannot
both be reversed images of each other. -/
lemma kd_cross {j k j' k' : Fin N} (h : j < k) (h' : j' < k') :
    kd j k' * kd k j' = 0 := by
  by_cases h1 : j = k'
  · by_cases h2 : k = j'
    · exfalso
      have e1 : (j : ℕ) = (k' : ℕ) := congrArg Fin.val h1
      have e2 : (k : ℕ) = (j' : ℕ) := congrArg Fin.val h2
      have l1 : (j : ℕ) < (k : ℕ) := h
      have l2 : (j' : ℕ) < (k' : ℕ) := h'
      omega
    · simp [kd_eq_zero h2]
  · simp [kd_eq_zero h1]

/-! ### The two off-diagonal families -/

/-- Entries of the matrix `c₁ E_{jk} + c₂ E_{kj}`. -/
def offGen (c₁ c₂ : ℂ) (j k : Fin N) (i l : Fin N) : ℂ :=
  c₁ * (kd i j * kd l k) + c₂ * (kd i k * kd l j)

/-- The trace of a product of two off-diagonal generators, for arbitrary coefficients.
All four off-diagonal family pairs are instances of this one computation. -/
lemma trace_offGen (c₁ c₂ d₁ d₂ : ℂ) (j k j' k' : Fin N) :
    (∑ i : Fin N, ∑ l : Fin N, offGen c₁ c₂ j k i l * offGen d₁ d₂ j' k' l i)
      = (c₁ * d₁ + c₂ * d₂) * (kd j k' * kd k j')
        + (c₁ * d₂ + c₂ * d₁) * (kd j j' * kd k k') := by
  have h : ∀ i l : Fin N, offGen c₁ c₂ j k i l * offGen d₁ d₂ j' k' l i
      = c₁ * d₁ * ((kd i j * kd l k) * (kd l j' * kd i k'))
        + c₁ * d₂ * ((kd i j * kd l k) * (kd l k' * kd i j'))
        + c₂ * d₁ * ((kd i k * kd l j) * (kd l j' * kd i k'))
        + c₂ * d₂ * ((kd i k * kd l j) * (kd l k' * kd i j')) := by
    intro i l; simp only [offGen]; ring
  have expand : (∑ i : Fin N, ∑ l : Fin N, offGen c₁ c₂ j k i l * offGen d₁ d₂ j' k' l i)
      = c₁ * d₁ * (∑ i : Fin N, ∑ l : Fin N, (kd i j * kd l k) * (kd l j' * kd i k'))
        + c₁ * d₂ * (∑ i : Fin N, ∑ l : Fin N, (kd i j * kd l k) * (kd l k' * kd i j'))
        + c₂ * d₁ * (∑ i : Fin N, ∑ l : Fin N, (kd i k * kd l j) * (kd l j' * kd i k'))
        + c₂ * d₂ * (∑ i : Fin N, ∑ l : Fin N, (kd i k * kd l j) * (kd l k' * kd i j')) := by
    simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [expand, sum_unit, sum_unit, sum_unit, sum_unit]
  ring

/-! ### The diagonal family -/

/-- The pivot position of the `l`-th diagonal generator: the entry carrying `-L`. -/
def piv (l : Fin (N - 1)) : Fin N := ⟨(l : ℕ) + 1, by have := l.isLt; omega⟩

lemma piv_val (l : Fin (N - 1)) : ((piv l : Fin N) : ℕ) = (l : ℕ) + 1 := rfl

lemma piv_pos (l : Fin (N - 1)) : 0 < ((piv l : Fin N) : ℕ) := by
  rw [piv_val]; omega

lemma piv_lt_piv {l m : Fin (N - 1)} (h : l < m) : (piv l : Fin N) < piv m := by
  have : (l : ℕ) < (m : ℕ) := h
  show ((piv l : Fin N) : ℕ) < ((piv m : Fin N) : ℕ)
  rw [piv_val, piv_val]; omega

lemma piv_ne_piv {l m : Fin (N - 1)} (h : l ≠ m) : (piv l : Fin N) ≠ piv m := by
  intro hc
  apply h
  have := congrArg Fin.val hc
  rw [piv_val, piv_val] at this
  exact Fin.ext (by omega)

/-- The unnormalized diagonal vector `(1, …, 1, -L, 0, …, 0)` with `L = l+1` leading
ones, complex valued. -/
def dVec (l : Fin (N - 1)) (p : Fin N) : ℂ :=
  (if p < piv l then 1 else 0) - (if p = piv l then (((piv l : Fin N) : ℕ) : ℂ) else 0)

/-- The normalization `1/√(2L(L+1))` making `Σ_p (dNorm l · dVec l p)² = 1/2`. -/
def dNorm (l : Fin (N - 1)) : ℂ :=
  ((Real.sqrt (2 * (((piv l : Fin N) : ℕ) : ℝ) * ((((piv l : Fin N) : ℕ) : ℝ) + 1)))⁻¹ : ℝ)

lemma dNorm_mul_self (l : Fin (N - 1)) :
    dNorm l * dNorm l
      = (2 * ((((piv l : Fin N) : ℕ)) : ℂ) * (((((piv l : Fin N) : ℕ)) : ℂ) + 1))⁻¹ := by
  rw [dNorm, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

/-! #### Counting sums over `Fin N` -/

/-- Counting the elements of `Fin N` below a threshold. -/
lemma sum_lt_card (L : Fin N) :
    (∑ p : Fin N, (if p < L then (1 : ℂ) else 0)) = ((L : ℕ) : ℂ) := by
  have hfil : (Finset.univ.filter (fun p : Fin N => p < L)) = Finset.Iio L := by
    ext p; simp
  rw [Finset.sum_boole, hfil, Fin.card_Iio]

lemma sum_lt_lt {L M : Fin N} (h : L ≤ M) :
    (∑ p : Fin N, (if p < L then (1 : ℂ) else 0) * (if p < M then (1 : ℂ) else 0))
      = ((L : ℕ) : ℂ) := by
  rw [← sum_lt_card L]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hp : p < L
  · have hpm : p < M := lt_of_lt_of_le hp h
    simp [hp, hpm]
  · simp [hp]

lemma sum_lt_gt {L M : Fin N} (h : M ≤ L) :
    (∑ p : Fin N, (if p < L then (1 : ℂ) else 0) * (if p < M then (1 : ℂ) else 0))
      = ((M : ℕ) : ℂ) := by
  rw [← sum_lt_card M]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hp : p < M
  · have hpl : p < L := lt_of_lt_of_le hp h
    simp [hp, hpl]
  · simp [hp]

lemma sum_lt_eq (L M : Fin N) (c : ℂ) :
    (∑ p : Fin N, (if p < L then (1 : ℂ) else 0) * (if p = M then c else 0))
      = if M < L then c else 0 := by
  have h : ∀ p : Fin N, (if p < L then (1 : ℂ) else 0) * (if p = M then c else 0)
      = if p = M then (if M < L then c else 0) else 0 := by
    intro p
    by_cases hp : p = M
    · subst hp; by_cases h2 : p < L <;> simp [h2]
    · simp [hp]
  rw [Finset.sum_congr rfl (fun p _ => h p)]
  simp

lemma sum_eq_lt (L M : Fin N) (c : ℂ) :
    (∑ p : Fin N, (if p = L then c else 0) * (if p < M then (1 : ℂ) else 0))
      = if L < M then c else 0 := by
  have h : ∀ p : Fin N, (if p = L then c else 0) * (if p < M then (1 : ℂ) else 0)
      = if p = L then (if L < M then c else 0) else 0 := by
    intro p
    by_cases hp : p = L
    · subst hp; by_cases h2 : p < M <;> simp [h2]
    · simp [hp]
  rw [Finset.sum_congr rfl (fun p _ => h p)]
  simp

lemma sum_eq_eq (L M : Fin N) (c e : ℂ) :
    (∑ p : Fin N, (if p = L then c else 0) * (if p = M then e else 0))
      = if L = M then c * e else 0 := by
  have h : ∀ p : Fin N, (if p = L then c else 0) * (if p = M then e else 0)
      = if p = L then (if L = M then c * e else 0) else 0 := by
    intro p
    by_cases hp : p = L
    · subst hp; by_cases h2 : p = M <;> simp [h2]
    · simp [hp]
  rw [Finset.sum_congr rfl (fun p _ => h p)]
  simp

/-- Orthogonality of the unnormalized diagonal vectors:
`Σ_p v^l_p v^m_p = L(L+1) δ^{lm}`.  The `l ≠ m` cases are the telescoping cancellation
`L - L = 0`; the diagonal case is `L + L² = L(L+1)`. -/
lemma dVec_orth (l m : Fin (N - 1)) :
    (∑ p : Fin N, dVec l p * dVec m p)
      = if l = m then ((((piv l : Fin N) : ℕ)) : ℂ) * (((((piv l : Fin N) : ℕ)) : ℂ) + 1)
        else 0 := by
  have hexp : ∀ p : Fin N, dVec l p * dVec m p
      = (if p < piv l then (1 : ℂ) else 0) * (if p < piv m then (1 : ℂ) else 0)
        - (if p < piv l then (1 : ℂ) else 0)
            * (if p = piv m then ((((piv m : Fin N) : ℕ)) : ℂ) else 0)
        - (if p = piv l then ((((piv l : Fin N) : ℕ)) : ℂ) else 0)
            * (if p < piv m then (1 : ℂ) else 0)
        + (if p = piv l then ((((piv l : Fin N) : ℕ)) : ℂ) else 0)
            * (if p = piv m then ((((piv m : Fin N) : ℕ)) : ℂ) else 0) := by
    intro p; simp only [dVec]; ring
  rw [Finset.sum_congr rfl (fun p _ => hexp p), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_lt_eq, sum_eq_lt, sum_eq_eq]
  rcases lt_trichotomy l m with h | h | h
  · have hlt : (piv l : Fin N) < piv m := piv_lt_piv h
    have hne : (piv l : Fin N) ≠ piv m := ne_of_lt hlt
    rw [sum_lt_lt (le_of_lt hlt), if_neg (lt_asymm hlt), if_pos hlt, if_neg hne,
      if_neg (ne_of_lt h)]
    ring
  · subst h
    rw [sum_lt_lt (le_refl (piv l : Fin N)), if_neg (lt_irrefl (piv l : Fin N)),
      if_pos (rfl : (piv l : Fin N) = piv l), if_pos (rfl : l = l)]
    ring
  · have hlt : (piv m : Fin N) < piv l := piv_lt_piv h
    have hne : (piv l : Fin N) ≠ piv m := (ne_of_lt hlt).symm
    rw [sum_lt_gt (le_of_lt hlt), if_pos hlt, if_neg (lt_asymm hlt), if_neg hne,
      if_neg (Ne.symm (ne_of_lt h))]
    ring

/-- The normalized diagonal generators are trace-orthonormal with `T_F = 1/2`. -/
lemma dSum (l m : Fin (N - 1)) :
    (∑ p : Fin N, (dNorm l * dVec l p) * (dNorm m * dVec m p))
      = if l = m then (1 / 2 : ℂ) else 0 := by
  have hfac : ∀ p : Fin N, (dNorm l * dVec l p) * (dNorm m * dVec m p)
      = (dNorm l * dNorm m) * (dVec l p * dVec m p) := by
    intro p; ring
  rw [Finset.sum_congr rfl (fun p _ => hfac p), ← Finset.mul_sum, dVec_orth]
  by_cases h : l = m
  · subst h
    rw [if_pos rfl, if_pos rfl, dNorm_mul_self]
    have hL : ((((piv l : Fin N) : ℕ)) : ℂ) ≠ 0 := by
      have := piv_pos l
      exact_mod_cast Nat.cast_ne_zero.mpr (by omega)
    have hL1 : ((((piv l : Fin N) : ℕ)) : ℂ) + 1 ≠ 0 := by
      rw [piv_val]
      push_cast
      intro hc
      have : ((l : ℕ) : ℂ) = -2 := by linear_combination hc
      have hre := congrArg Complex.re this
      simp at hre
      have : (0 : ℝ) ≤ ((l : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith [hre ▸ this]
    field_simp
  · rw [if_neg h, if_neg h, mul_zero]

/-! ### The generators -/

/-- Ordered pairs `j < k` in `Fin N`: the index set of each off-diagonal family. -/
abbrev OffPair (N : ℕ) : Type := {p : Fin N × Fin N // p.1 < p.2}

/-- The adjoint index set of `su(N)`: symmetric off-diagonal, antisymmetric
off-diagonal, diagonal traceless. -/
abbrev SUNIndex (N : ℕ) : Type := OffPair N ⊕ OffPair N ⊕ Fin (N - 1)

/-- Matrix entries of the fundamental `su(N)` generators `Tᵃ = λᵃ/2` in the generalized
Gell-Mann basis. -/
def suNGenEntry (N : ℕ) : SUNIndex N → Fin N → Fin N → ℂ
  | Sum.inl o, i, l => offGen (1 / 2) (1 / 2) o.1.1 o.1.2 i l
  | Sum.inr (Sum.inl o), i, l => offGen (-I / 2) (I / 2) o.1.1 o.1.2 i l
  | Sum.inr (Sum.inr d), i, l => kd i l * (dNorm d * dVec d i)

/-- Kronecker delta on the adjoint index set of `su(N)`. -/
def suNDeltaAdj (a b : SUNIndex N) : ℝ := if a = b then 1 else 0

/-- Kronecker delta on the fundamental index set of `su(N)`. -/
def suNDeltaFund (i j : Fin N) : ℝ := if i = j then 1 else 0

/-! ### Auxiliary traces mixing the families -/

lemma sum_off_diag (c₁ c₂ : ℂ) {j k : Fin N} (hjk : j ≠ k) (r : Fin N → ℂ) :
    (∑ i : Fin N, ∑ l : Fin N, offGen c₁ c₂ j k i l * (kd l i * r l)) = 0 := by
  have h : ∀ i l : Fin N, offGen c₁ c₂ j k i l * (kd l i * r l)
      = c₁ * (kd i j * (kd l k * (kd l i * r l)))
        + c₂ * (kd i k * (kd l j * (kd l i * r l))) := by
    intro i l; simp only [offGen]; ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, kd_sum]
  rw [kd_eq_zero hjk, kd_eq_zero (Ne.symm hjk)]
  ring

lemma sum_diag_off (c₁ c₂ : ℂ) {j k : Fin N} (hjk : j ≠ k) (r : Fin N → ℂ) :
    (∑ i : Fin N, ∑ l : Fin N, (kd i l * r i) * offGen c₁ c₂ j k l i) = 0 := by
  have h : ∀ i l : Fin N, (kd i l * r i) * offGen c₁ c₂ j k l i
      = c₁ * (kd i k * (kd l j * (kd i l * r i)))
        + c₂ * (kd i j * (kd l k * (kd i l * r i))) := by
    intro i l; simp only [offGen]; ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, kd_sum]
  rw [kd_eq_zero hjk, kd_eq_zero (Ne.symm hjk)]
  ring

lemma sum_diag_diag (r r' : Fin N → ℂ) :
    (∑ i : Fin N, ∑ l : Fin N, (kd i l * r i) * (kd l i * r' l))
      = ∑ i : Fin N, r i * r' i := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : ∀ l : Fin N, (kd i l * r i) * (kd l i * r' l) = kd l i * (r i * r' l) := by
    intro l
    by_cases hl : i = l
    · subst hl; simp [kd_self]
    · simp [kd_eq_zero hl, kd_eq_zero (Ne.symm hl)]
  rw [Finset.sum_congr rfl (fun l _ => h l), kd_sum]

/-! ### The trace identity -/

/-- Trace normalization for `su(N)`: `Σᵢⱼ (Tᵃ)ᵢⱼ (Tᵇ)ⱼᵢ = (1/2) δᵃᵇ`. -/
def SUNTraceStatement (N : ℕ) : Prop :=
  ∀ a b : SUNIndex N,
    (∑ i : Fin N, ∑ l : Fin N, suNGenEntry N a i l * suNGenEntry N b l i)
      = ((1 / 2 : ℝ) : ℂ) * ((suNDeltaAdj a b : ℝ) : ℂ)

/-- The generalized Gell-Mann generators of `su(N)` are trace-normalized with
`T_F = 1/2`, for every `N`.

The proof is nine family pairs.  The four off-diagonal ones are instances of
`trace_offGen`, differing only in the coefficients `(c₁, c₂)`; the mixed
off-diagonal/diagonal ones vanish because the off-diagonal generators have no diagonal
support; and the diagonal one is `dSum`, whose content is the telescoping
orthogonality `dVec_orth`. -/
lemma suNTraceStatement (N : ℕ) : SUNTraceStatement N := by
  intro a b
  rcases a with o | o | d <;> rcases b with o' | o' | d'
  -- symmetric × symmetric
  · obtain ⟨⟨j, k⟩, hjk⟩ := o
    obtain ⟨⟨j', k'⟩, hjk'⟩ := o'
    simp only [suNGenEntry]
    rw [trace_offGen, kd_cross hjk hjk', kd_pair]
    simp only [suNDeltaAdj, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq]
    by_cases h : j = j' ∧ k = k' <;> simp [h] <;> ring
  -- symmetric × antisymmetric
  · obtain ⟨⟨j, k⟩, hjk⟩ := o
    obtain ⟨⟨j', k'⟩, hjk'⟩ := o'
    simp only [suNGenEntry]
    rw [trace_offGen]
    simp only [suNDeltaAdj]
    rw [if_neg (by simp)]
    push_cast
    ring_nf
  -- symmetric × diagonal
  · obtain ⟨⟨j, k⟩, hjk⟩ := o
    simp only [suNGenEntry]
    rw [sum_off_diag _ _ (ne_of_lt hjk)]
    simp only [suNDeltaAdj]
    rw [if_neg (by simp)]
    simp
  -- antisymmetric × symmetric
  · obtain ⟨⟨j, k⟩, hjk⟩ := o
    obtain ⟨⟨j', k'⟩, hjk'⟩ := o'
    simp only [suNGenEntry]
    rw [trace_offGen]
    simp only [suNDeltaAdj]
    rw [if_neg (by simp)]
    push_cast
    ring_nf
  -- antisymmetric × antisymmetric
  · obtain ⟨⟨j, k⟩, hjk⟩ := o
    obtain ⟨⟨j', k'⟩, hjk'⟩ := o'
    simp only [suNGenEntry]
    rw [trace_offGen, kd_cross hjk hjk', kd_pair]
    simp only [suNDeltaAdj, Sum.inr.injEq, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq]
    by_cases h : j = j' ∧ k = k' <;> simp [h] <;>
      linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
  -- antisymmetric × diagonal
  · obtain ⟨⟨j, k⟩, hjk⟩ := o
    simp only [suNGenEntry]
    rw [sum_off_diag _ _ (ne_of_lt hjk)]
    simp only [suNDeltaAdj]
    rw [if_neg (by simp)]
    simp
  -- diagonal × symmetric
  · obtain ⟨⟨j', k'⟩, hjk'⟩ := o'
    simp only [suNGenEntry]
    rw [sum_diag_off _ _ (ne_of_lt hjk')]
    simp only [suNDeltaAdj]
    rw [if_neg (by simp)]
    simp
  -- diagonal × antisymmetric
  · obtain ⟨⟨j', k'⟩, hjk'⟩ := o'
    simp only [suNGenEntry]
    rw [sum_diag_off _ _ (ne_of_lt hjk')]
    simp only [suNDeltaAdj]
    rw [if_neg (by simp)]
    simp
  -- diagonal × diagonal
  · simp only [suNGenEntry]
    rw [sum_diag_diag, dSum]
    simp only [suNDeltaAdj, Sum.inr.injEq]
    by_cases h : d = d' <;> simp [h]

/-! ### Status: the two Casimirs

The trace identity above is the whole of what is proved here.  Two things are not.

`C_F = (N²-1)/(2N)`, the fundamental Casimir `Σₐ TᵃTᵃ = C_F · 1`, does not follow from
the trace identity alone.  Tracing the Casimir identity gives `N · C_F = Σₐ Tr(TᵃTᵃ) =
T_F · (N²-1)`, hence `C_F = T_F (N²-1)/N`, but only *given* that `Σₐ TᵃTᵃ` is a scalar
matrix — which is Schur's lemma for the fundamental representation and is not available
at this pin.  Proving it directly means summing over the three families: the
off-diagonal pairs contribute `(N-1)/2 · 1`, which needs the count `#{(j,k) | j < k with
j or k = p} = N-1`, and the diagonal family contributes `(N-1)/(2N) · 1`, which needs
the telescoping sum `Σ_{L>p} 1/(2L(L+1)) + p/(2(p+1)) = (N-1)/(2N)`.  Neither is hard
mathematics; both are real Lean work, and neither is done.

`C_A = N`, the adjoint Casimir, additionally needs the general-`N` structure constants
`f^{abc}`, which are not defined in this module at all.  `su(3)` is in the same
position: see the closing note of `Physlib.QFT.QCD.SU3Generators`. -/

end SUNGen

end RepresentationColor
end QCD
end QFT
end Physlib
