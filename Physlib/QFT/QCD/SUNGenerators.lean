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

`suN_completeness` — the Fierz relation
`Σₐ (Tᵃ)_{ij} (Tᵃ)_{kl} = (1/2)(δ_{il} δ_{jk} - δ_{ij} δ_{kl}/N)`, for every `N`.

`suNFundamentalStatement` — `Σₐ TᵃTᵃ = C_F · 1` with `C_F = (N²-1)/(2N)`, a short
consequence of completeness.  Completeness *derives* the scalarity of the Casimir, so
Schur's lemma is not used anywhere.

The adjoint Casimir `C_A = N` is not proved: the general-`N` structure constants do not
exist in this development.  See the closing note.

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
    by_cases h : j = j' ∧ k = k' <;> simp [h]
    all_goals ring
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
    by_cases h : j = j' ∧ k = k' <;> simp [h]
    all_goals linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
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

/-! ### Completeness (Fierz) relation

The trace identity fixes the normalization of the basis.  The *completeness* relation

```
Σₐ (Tᵃ)_{ij} (Tᵃ)_{kl} = (1/2) ( δ_{il} δ_{jk} - δ_{ij} δ_{kl} / N )
```

says that the `N²-1` generators together with the identity matrix span `M_N(ℂ)`.  It is
strictly stronger than the trace identity, and both Casimirs follow from it.  For `C_F`
this matters for a specific reason: setting `k = j` and summing over `j` turns the
right-hand side into `((N²-1)/(2N)) δ_{il}`, so the completeness relation *derives* the
scalarity of `Σₐ TᵃTᵃ` rather than assuming it.  Assuming it would be Schur's lemma for
the fundamental representation, which is not available at this pin.

The two off-diagonal families combine to the `δ_{il} δ_{jk}` term — the `-1/N` piece is
not theirs — and the diagonal family supplies the rest.  The diagonal part is the work:
its content is the rank-one identity `Σ_d u^d_i u^d_k = (1/2)(δ_{ik} - 1/N)`, which is a
telescoping sum over the normalizations `1/(2L(L+1))`.  Telescoping is easiest over `ℕ`,
so the diagonal generators are first transported to natural-number index form (`dWt`,
`dEnt`, `dVec_eq_dEnt`).
-/

/-! #### A four-fold Kronecker sum -/

/-- `Σ_p δ_{ip} δ_{lp} δ_{jp} δ_{kp} = δ_{ij} δ_{kl} δ_{ik}`: both sides are `1` exactly
when all four indices agree.  This is the diagonal correction that the two off-diagonal
families cannot reach, being indexed by ordered pairs. -/
lemma kd_quad (i j k l : Fin N) :
    (∑ p : Fin N, (kd i p * kd l p) * (kd j p * kd k p)) = (kd i j * kd k l) * kd i k := by
  have h : ∀ p : Fin N, (kd i p * kd l p) * (kd j p * kd k p)
      = (if p = i then (kd i j * kd k l) * kd i k else 0) := by
    intro p
    by_cases hpi : i = p
    · rw [← hpi, if_pos rfl, kd_self, kd_comm l i, kd_comm j i, kd_comm k i]
      by_cases hik : i = k
      · rw [← hik, kd_self]
        ring
      · rw [kd_eq_zero hik]
        ring
    · rw [if_neg (fun hc => hpi hc.symm), kd_eq_zero hpi]
      ring
  rw [Finset.sum_congr rfl (fun p _ => h p), Finset.sum_ite_eq']
  simp

/-- The Kronecker delta on `Fin N` compared through the underlying naturals. -/
lemma kd_eq_ite_val (i k : Fin N) : kd i k = (if (i : ℕ) = (k : ℕ) then (1 : ℂ) else 0) := by
  have h : (i = k) ↔ ((i : ℕ) = (k : ℕ)) := Fin.ext_iff
  simp only [kd, h]

/-- `kd` is the complexification of `suNDeltaFund`. -/
lemma kd_eq_deltaFund (i j : Fin N) : kd i j = ((suNDeltaFund i j : ℝ) : ℂ) := by
  simp only [kd, suNDeltaFund]
  split_ifs <;> simp

/-! #### Summing a symmetric function over ordered pairs -/

/-- A symmetric function summed over the ordered pairs `j < k` is half of its full
double sum minus its diagonal.  This is how the two off-diagonal families, which are
indexed by `OffPair N`, are converted into unrestricted sums over `Fin N × Fin N`. -/
lemma sum_offPair (h : Fin N → Fin N → ℂ) (hs : ∀ p q, h p q = h q p) :
    (∑ o : OffPair N, h o.1.1 o.1.2)
      = (1 / 2 : ℂ) * ((∑ p : Fin N, ∑ q : Fin N, h p q) - ∑ p : Fin N, h p p) := by
  have hmem : ∀ x : Fin N × Fin N,
      x ∈ Finset.univ.filter (fun x : Fin N × Fin N => x.1 < x.2) ↔ x.1 < x.2 := by
    intro x
    simp
  have e1 : (∑ o : OffPair N, h o.1.1 o.1.2)
      = ∑ x ∈ Finset.univ.filter (fun x : Fin N × Fin N => x.1 < x.2), h x.1 x.2 :=
    (Finset.sum_subtype _ hmem (fun x : Fin N × Fin N => h x.1 x.2)).symm
  have e2 : (∑ x ∈ Finset.univ.filter (fun x : Fin N × Fin N => x.1 < x.2), h x.1 x.2)
      = ∑ p : Fin N, ∑ q : Fin N, (if p < q then h p q else 0) := by
    simp only [Finset.sum_filter, Fintype.sum_prod_type]
  have key : (∑ p : Fin N, ∑ q : Fin N, (if q < p then h p q else 0))
      = ∑ p : Fin N, ∑ q : Fin N, (if p < q then h p q else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
    rw [hs]
  have hsplit : ∀ p q : Fin N, (if p < q then h p q else 0) + (if q < p then h p q else 0)
      = h p q - (if p = q then h p q else 0) := by
    intro p q
    rcases lt_trichotomy p q with hc | hc | hc
    · rw [if_pos hc, if_neg (lt_asymm hc), if_neg (ne_of_lt hc)]; ring
    · rw [hc, if_neg (lt_irrefl q), if_pos rfl]; ring
    · rw [if_neg (lt_asymm hc), if_pos hc, if_neg (Ne.symm (ne_of_lt hc))]; ring
  have hsum : (∑ p : Fin N, ∑ q : Fin N, (if p < q then h p q else 0))
      + (∑ p : Fin N, ∑ q : Fin N, (if q < p then h p q else 0))
      = (∑ p : Fin N, ∑ q : Fin N, h p q) - ∑ p : Fin N, h p p := by
    rw [← Finset.sum_add_distrib]
    have step : ∀ p : Fin N,
        (∑ q : Fin N, (if p < q then h p q else 0))
          + (∑ q : Fin N, (if q < p then h p q else 0))
          = (∑ q : Fin N, h p q) - h p p := by
      intro p
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun q _ => hsplit p q),
        Finset.sum_sub_distrib]
      have hpp : (∑ q : Fin N, (if p = q then h p q else 0)) = h p p := by
        rw [Finset.sum_ite_eq]; simp
      rw [hpp]
    rw [Finset.sum_congr rfl (fun p _ => step p), Finset.sum_sub_distrib]
  rw [key] at hsum
  have htwo : (∑ p : Fin N, ∑ q : Fin N, (if p < q then h p q else 0)) * 2
      = (∑ p : Fin N, ∑ q : Fin N, h p q) - ∑ p : Fin N, h p p := by
    rw [← hsum]; ring
  rw [e1, e2, ← htwo]
  ring

/-! #### The two off-diagonal families -/

/-- The symmetric and antisymmetric generators built on the same ordered pair `(p,q)`
contribute, to the completeness sum, exactly
`(1/2)(δ_{ip}δ_{lp}δ_{jq}δ_{kq} + δ_{iq}δ_{lq}δ_{jp}δ_{kp})`.

The `δ_{ip}δ_{jq}δ_{kp}δ_{lq}` terms — the ones that would produce `δ_{ij}δ_{kl}` rather
than `δ_{il}δ_{jk}` — cancel between the two families, because the antisymmetric pair
carries `(-i/2)(-i/2) = -1/4` against the symmetric pair's `+1/4`.  That cancellation is
the only place the factor `i` does any work. -/
lemma offGen_pair_sum (p q i j k l : Fin N) :
    offGen (1 / 2) (1 / 2) p q i j * offGen (1 / 2) (1 / 2) p q k l
      + offGen (-I / 2) (I / 2) p q i j * offGen (-I / 2) (I / 2) p q k l
      = (1 / 2 : ℂ) * ((kd i p * kd l p) * (kd j q * kd k q)
          + (kd i q * kd l q) * (kd j p * kd k p)) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [offGen]
  linear_combination (kd i p * kd j q * (kd k p * kd l q) / 4
    - kd i p * kd j q * (kd k q * kd l p) / 4
    - kd i q * kd j p * (kd k p * kd l q) / 4
    + kd i q * kd j p * (kd k q * kd l p) / 4) * hI

/-- The off-diagonal families' total contribution to the completeness sum. -/
lemma sum_offPair_kd (i j k l : Fin N) :
    (∑ o : OffPair N, ((kd i o.1.1 * kd l o.1.1) * (kd j o.1.2 * kd k o.1.2)
        + (kd i o.1.2 * kd l o.1.2) * (kd j o.1.1 * kd k o.1.1)))
      = (kd i l * kd j k) - (kd i j * kd k l) * kd i k := by
  have hkk : ∀ x y : Fin N, (∑ p : Fin N, kd x p * kd y p) = kd x y := by
    intro x y
    have hc : ∀ p : Fin N, kd x p * kd y p = kd p x * kd p y := by
      intro p; rw [kd_comm x p, kd_comm y p]
    rw [Finset.sum_congr rfl (fun p _ => hc p), kd_kd_sum]
  rw [sum_offPair (fun p q => (kd i p * kd l p) * (kd j q * kd k q)
      + (kd i q * kd l q) * (kd j p * kd k p)) (fun p q => by ring)]
  have hS : (∑ p : Fin N, ∑ q : Fin N, ((kd i p * kd l p) * (kd j q * kd k q)
        + (kd i q * kd l q) * (kd j p * kd k p)))
      = 2 * (kd i l * kd j k) := by
    have h1 : ∀ p : Fin N, (∑ q : Fin N, ((kd i p * kd l p) * (kd j q * kd k q)
        + (kd i q * kd l q) * (kd j p * kd k p)))
        = (kd i p * kd l p) * kd j k + kd i l * (kd j p * kd k p) := by
      intro p
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hkk j k]
      congr 1
      rw [← Finset.sum_mul, hkk i l]
    rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_add_distrib,
      ← Finset.sum_mul, hkk i l, ← Finset.mul_sum, hkk j k]
    ring
  have hD : (∑ p : Fin N, ((kd i p * kd l p) * (kd j p * kd k p)
        + (kd i p * kd l p) * (kd j p * kd k p)))
      = 2 * ((kd i j * kd k l) * kd i k) := by
    have h2 : ∀ p : Fin N, ((kd i p * kd l p) * (kd j p * kd k p)
        + (kd i p * kd l p) * (kd j p * kd k p))
        = 2 * ((kd i p * kd l p) * (kd j p * kd k p)) := by
      intro p; ring
    rw [Finset.sum_congr rfl (fun p _ => h2 p), ← Finset.mul_sum, kd_quad]
  rw [hS, hD]
  ring

/-! #### The diagonal family over `ℕ` -/

/-- The squared normalization `1/(2(l+1)(l+2))` of the `l`-th diagonal generator, as a
function of the natural index `l`; see `dNorm_sq_eq`. -/
def dWt (l : ℕ) : ℂ := ((2 : ℂ) * ((l : ℂ) + 1) * ((l : ℂ) + 2))⁻¹

/-- Entry `p` of the `l`-th unnormalized diagonal vector in natural-number index form:
`1` for `p ≤ l`, `-(l+1)` at `p = l+1`, and `0` beyond; see `dVec_eq_dEnt`. -/
def dEnt (p l : ℕ) : ℂ :=
  (if p < l + 1 then (1 : ℂ) else 0) - (if p = l + 1 then ((l : ℂ) + 1) else 0)

/-- `(n : ℂ) + 1 ≠ 0`.  `Nat.cast_add_one_ne_zero` is stated for ordered semirings, which
`ℂ` is not; this is the `CharZero` argument instead. -/
lemma cast_succ_ne_zero (n : ℕ) : ((n : ℂ) + 1) ≠ 0 := by
  have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h, Ne, Nat.cast_eq_zero]
  omega

/-- `(n : ℂ) + 2 ≠ 0`. -/
lemma cast_add_two_ne_zero (n : ℕ) : ((n : ℂ) + 2) ≠ 0 := by
  have h : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [h, Ne, Nat.cast_eq_zero]
  omega

/-- The telescoping sum of the diagonal weights,
`Σ_{l ∈ [a, m)} 1/(2(l+1)(l+2)) = 1/(2(a+1)) - 1/(2(m+1))`.  Every statement about the
diagonal family reduces to this one. -/
lemma sum_dWt_Ico (a m : ℕ) (h : a ≤ m) :
    (∑ l ∈ Finset.Ico a m, dWt l)
      = (2 * ((a : ℂ) + 1))⁻¹ - (2 * ((m : ℂ) + 1))⁻¹ := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    simp only [dWt]
    have h0 := cast_succ_ne_zero a
    have h1 := cast_succ_ne_zero n
    have h2 := cast_add_two_ne_zero n
    have h3 : ((n : ℂ) + 1 + 1) ≠ 0 := by
      have he : ((n : ℂ) + 1 + 1) = (n : ℂ) + 2 := by ring
      rw [he]; exact h2
    push_cast
    field_simp
    ring

/-- A `range` sum restricted by a lower threshold is an `Ico` sum. -/
lemma sum_range_ite_lt (m a : ℕ) (f : ℕ → ℂ) :
    (∑ l ∈ Finset.range m, if a < l + 1 then f l else 0) = ∑ l ∈ Finset.Ico a m, f l := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext l
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

/-- The single surviving term of a `range` sum whose condition pins `l = j`. -/
lemma sum_range_ite_eq_succ (m j : ℕ) (hj : j < m) (f : ℕ → ℂ) :
    (∑ l ∈ Finset.range m, if j + 1 = l + 1 then f l else 0) = f j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    exact if_neg (by omega)
  · intro hc
    exact absurd (Finset.mem_range.mpr hj) hc

/-- The diagonal-family completeness sum on the diagonal `p = q`:
`Σ_l 1/(2(l+1)(l+2)) · (v^l_p)² = (1/2)(1 - 1/n)`.  The telescoping tail
`1/(2(p+1)) - 1/(2n)` and the pivot term `p/(2(p+1))` add to `1/2 - 1/(2n)`. -/
lemma sum_dEnt_diag (n p : ℕ) (hp : p < n) :
    (∑ l ∈ Finset.range (n - 1), dWt l * (dEnt p l * dEnt p l))
      = (1 / 2 : ℂ) * (1 - (n : ℂ)⁻¹) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  have hexp : ∀ l : ℕ, dWt l * (dEnt p l * dEnt p l)
      = (if p < l + 1 then dWt l else 0)
        + (if p = l + 1 then dWt l * ((l : ℂ) + 1) ^ 2 else 0) := by
    intro l
    simp only [dEnt]
    split_ifs <;> first
      | (exfalso; omega)
      | ring
  rw [Finset.sum_congr rfl (fun l _ => hexp l), Finset.sum_add_distrib,
    sum_range_ite_lt, sum_dWt_Ico p (n - 1) (by omega), hcast]
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0
    have hz : ∀ l ∈ Finset.range (n - 1),
        (if (0 : ℕ) = l + 1 then dWt l * ((l : ℂ) + 1) ^ 2 else 0) = 0 :=
      fun l _ => if_neg (by omega)
    rw [Finset.sum_eq_zero hz, add_zero]
    push_cast
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, p = j + 1 := ⟨p - 1, by omega⟩
    rw [sum_range_ite_eq_succ (n - 1) j (by omega) (fun l => dWt l * ((l : ℂ) + 1) ^ 2)]
    simp only [dWt]
    have h1 := cast_succ_ne_zero j
    have h2 := cast_add_two_ne_zero j
    have h3 : ((j : ℂ) + 1 + 1) ≠ 0 := by
      have he : ((j : ℂ) + 1 + 1) = (j : ℂ) + 2 := by ring
      rw [he]; exact h2
    push_cast
    field_simp
    ring

/-- The diagonal-family completeness sum off the diagonal, `p < q`:
`Σ_l 1/(2(l+1)(l+2)) · v^l_p v^l_q = -1/(2n)`.  The telescoping tail and the pivot term
now cancel exactly, leaving only the endpoint `-1/(2n)`. -/
lemma sum_dEnt_off (n p q : ℕ) (hq : q < n) (hpq : p < q) :
    (∑ l ∈ Finset.range (n - 1), dWt l * (dEnt p l * dEnt q l))
      = (1 / 2 : ℂ) * (0 - (n : ℂ)⁻¹) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  have hexp : ∀ l : ℕ, dWt l * (dEnt p l * dEnt (j + 1) l)
      = (if j + 1 < l + 1 then dWt l else 0)
        - (if j + 1 = l + 1 then dWt l * ((l : ℂ) + 1) else 0) := by
    intro l
    simp only [dEnt]
    split_ifs <;> first
      | (exfalso; omega)
      | ring
  rw [Finset.sum_congr rfl (fun l _ => hexp l), Finset.sum_sub_distrib,
    sum_range_ite_lt, sum_dWt_Ico (j + 1) (n - 1) (by omega), hcast,
    sum_range_ite_eq_succ (n - 1) j (by omega) (fun l => dWt l * ((l : ℂ) + 1))]
  simp only [dWt]
  have h1 := cast_succ_ne_zero j
  have h2 := cast_add_two_ne_zero j
  have h3 : ((j : ℂ) + 1 + 1) ≠ 0 := by
    have he : ((j : ℂ) + 1 + 1) = (j : ℂ) + 2 := by ring
    rw [he]; exact h2
  push_cast
  field_simp
  ring

/-- The diagonal-family completeness sum, in natural-number index form. -/
lemma sum_dEnt (n p q : ℕ) (hp : p < n) (hq : q < n) :
    (∑ l ∈ Finset.range (n - 1), dWt l * (dEnt p l * dEnt q l))
      = (1 / 2 : ℂ) * ((if p = q then (1 : ℂ) else 0) - (n : ℂ)⁻¹) := by
  rcases lt_trichotomy p q with hc | hc | hc
  · rw [sum_dEnt_off n p q hq hc, if_neg (by omega : ¬ (p = q))]
  · rw [hc, sum_dEnt_diag n q hq, if_pos rfl]
  · have hsymm : ∀ l : ℕ, dWt l * (dEnt p l * dEnt q l) = dWt l * (dEnt q l * dEnt p l) := by
      intro l; ring
    rw [Finset.sum_congr rfl (fun l _ => hsymm l), sum_dEnt_off n q p hp hc,
      if_neg (by omega : ¬ (p = q))]

/-! #### Transporting the diagonal family back to `Fin` -/

/-- `dNorm` squared, in natural-number index form. -/
lemma dNorm_sq_eq (d : Fin (N - 1)) : dNorm d * dNorm d = dWt (d : ℕ) := by
  rw [dNorm_mul_self]
  simp only [dWt]
  congr 1
  rw [piv_val]
  push_cast
  ring

/-- `dVec` in natural-number index form. -/
lemma dVec_eq_dEnt (d : Fin (N - 1)) (p : Fin N) : dVec d p = dEnt (p : ℕ) (d : ℕ) := by
  have h1 : (p < piv d) ↔ ((p : ℕ) < (d : ℕ) + 1) := by rw [Fin.lt_def, piv_val]
  have h2 : (p = piv d) ↔ ((p : ℕ) = (d : ℕ) + 1) := by rw [Fin.ext_iff, piv_val]
  simp only [dVec, dEnt, piv_val, h1, h2]
  push_cast
  ring

/-- **Diagonal completeness**: `Σ_d u^d_i u^d_k = (1/2)(δ_{ik} - 1/N)`, where
`u^d = dNorm d • dVec d` is the `d`-th normalized diagonal generator.  This is the piece
of the completeness relation that supplies the `-1/N`. -/
lemma dComplete (i k : Fin N) :
    (∑ d : Fin (N - 1), (dNorm d * dVec d i) * (dNorm d * dVec d k))
      = (1 / 2 : ℂ) * (kd i k - ((N : ℂ))⁻¹) := by
  have hterm : ∀ d : Fin (N - 1), (dNorm d * dVec d i) * (dNorm d * dVec d k)
      = dWt (d : ℕ) * (dEnt (i : ℕ) (d : ℕ) * dEnt (k : ℕ) (d : ℕ)) := by
    intro d
    rw [dVec_eq_dEnt, dVec_eq_dEnt, ← dNorm_sq_eq]
    ring
  rw [Finset.sum_congr rfl (fun d _ => hterm d),
    Fin.sum_univ_eq_sum_range (fun l => dWt l * (dEnt (i : ℕ) l * dEnt (k : ℕ) l)) (N - 1),
    sum_dEnt N (i : ℕ) (k : ℕ) i.isLt k.isLt, kd_eq_ite_val]

/-! ### The completeness relation and the fundamental Casimir -/

/-- **Completeness (Fierz) relation** for the generalized Gell-Mann basis of `su(N)`:
`Σₐ (Tᵃ)_{ij} (Tᵃ)_{kl} = (1/2)(δ_{il} δ_{jk} - δ_{ij} δ_{kl} / N)`, for every `N`.

The two off-diagonal families give `(1/2)(δ_{il}δ_{jk} - δ_{ij}δ_{kl}δ_{ik})`: the full
`δ_{il}δ_{jk}` minus the all-indices-equal term they cannot reach, since they are indexed
by *ordered* pairs `j < k`.  The diagonal family gives
`δ_{ij}δ_{kl}((1/2)δ_{ik} - 1/(2N))`, whose first half restores exactly that missing
term. -/
lemma suN_completeness (i j k l : Fin N) :
    (∑ a : SUNIndex N, suNGenEntry N a i j * suNGenEntry N a k l)
      = (1 / 2 : ℂ) * (kd i l * kd j k - ((N : ℂ))⁻¹ * (kd i j * kd k l)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, ← add_assoc]
  have hcomb : (∑ o : OffPair N, suNGenEntry N (Sum.inl o) i j * suNGenEntry N (Sum.inl o) k l)
      + (∑ o : OffPair N, suNGenEntry N (Sum.inr (Sum.inl o)) i j
          * suNGenEntry N (Sum.inr (Sum.inl o)) k l)
      = (1 / 2 : ℂ) * ((kd i l * kd j k) - (kd i j * kd k l) * kd i k) := by
    rw [← Finset.sum_add_distrib]
    have hp : ∀ o : OffPair N,
        suNGenEntry N (Sum.inl o) i j * suNGenEntry N (Sum.inl o) k l
          + suNGenEntry N (Sum.inr (Sum.inl o)) i j
            * suNGenEntry N (Sum.inr (Sum.inl o)) k l
        = (1 / 2 : ℂ) * ((kd i o.1.1 * kd l o.1.1) * (kd j o.1.2 * kd k o.1.2)
            + (kd i o.1.2 * kd l o.1.2) * (kd j o.1.1 * kd k o.1.1)) := by
      intro o
      simp only [suNGenEntry]
      exact offGen_pair_sum o.1.1 o.1.2 i j k l
    rw [Finset.sum_congr rfl (fun o _ => hp o), ← Finset.mul_sum, sum_offPair_kd]
  have hdiag : (∑ d : Fin (N - 1), suNGenEntry N (Sum.inr (Sum.inr d)) i j
      * suNGenEntry N (Sum.inr (Sum.inr d)) k l)
      = (kd i j * kd k l) * ((1 / 2 : ℂ) * (kd i k - ((N : ℂ))⁻¹)) := by
    have hp : ∀ d : Fin (N - 1), suNGenEntry N (Sum.inr (Sum.inr d)) i j
        * suNGenEntry N (Sum.inr (Sum.inr d)) k l
        = (kd i j * kd k l) * ((dNorm d * dVec d i) * (dNorm d * dVec d k)) := by
      intro d
      simp only [suNGenEntry]
      ring
    rw [Finset.sum_congr rfl (fun d _ => hp d), ← Finset.mul_sum, dComplete]
  rw [hcomb, hdiag]
  ring

/-- Fundamental Casimir for `su(N)`: `Σₐ TᵃTᵃ = ((N²-1)/(2N)) · 1`, so `C_F = (N²-1)/(2N)`.
An identity in `ℂ`, matching `NormalizedGeneratorData.FundamentalCasimirIdentity`. -/
def SUNFundamentalStatement (N : ℕ) : Prop :=
  ∀ i j : Fin N,
    (∑ a : SUNIndex N, ∑ k : Fin N, suNGenEntry N a i k * suNGenEntry N a k j)
      = ((((N : ℝ) ^ 2 - 1) / (2 * N) : ℝ) : ℂ) * ((suNDeltaFund i j : ℝ) : ℂ)

/-- The generalized Gell-Mann generators of `su(N)` satisfy the fundamental Casimir
identity with `C_F = (N²-1)/(2N)`, for every `N`.

This is the completeness relation with `k = j`, summed over `j`: the `δ_{ij}δ_{kk}` term
contributes `N δ_{il}` and the `δ_{ik}δ_{kj}` term contributes `δ_{il}/N`.  Scalarity of
`Σₐ TᵃTᵃ` is an output of that computation, not an input, so Schur's lemma is nowhere
used. -/
lemma suNFundamentalStatement (N : ℕ) : SUNFundamentalStatement N := by
  intro i j
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := i.isLt; omega)
  rw [Finset.sum_comm]
  have hterm : ∀ k : Fin N, (∑ a : SUNIndex N, suNGenEntry N a i k * suNGenEntry N a k j)
      = (1 / 2 : ℂ) * (kd i j * kd k k - ((N : ℂ))⁻¹ * (kd i k * kd k j)) :=
    fun k => suN_completeness i k k j
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, Finset.sum_sub_distrib]
  have h1 : (∑ k : Fin N, kd i j * kd k k) = (N : ℂ) * kd i j := by
    have hc : ∀ k : Fin N, kd i j * kd k k = kd i j := by
      intro k; rw [kd_self, mul_one]
    rw [Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have h2 : (∑ k : Fin N, ((N : ℂ))⁻¹ * (kd i k * kd k j)) = ((N : ℂ))⁻¹ * kd i j := by
    rw [← Finset.mul_sum]
    congr 1
    have hc : ∀ k : Fin N, kd i k * kd k j = kd k i * kd k j := by
      intro k; rw [kd_comm i k]
    rw [Finset.sum_congr rfl (fun k _ => hc k), kd_kd_sum]
  have hscal : (1 / 2 : ℂ) * ((N : ℂ) - ((N : ℂ))⁻¹)
      = ((N : ℂ) ^ 2 - 1) / (2 * (N : ℂ)) := by
    field_simp
  have hcast : ((((N : ℝ) ^ 2 - 1) / (2 * N) : ℝ) : ℂ) = ((N : ℂ) ^ 2 - 1) / (2 * (N : ℂ)) := by
    push_cast
    ring
  rw [h1, h2, hcast, ← kd_eq_deltaFund]
  linear_combination (kd i j) * hscal

/-! ### Status: the adjoint Casimir

`C_F` is proved above.  `C_A = N` is not, and the obstruction is not the Casimir sum
itself: it is that the general-`N` structure constants `f^{abc}` do not exist in this
development.  `su(2)` and `su(3)` carry them as finite tables (`epsilon3`,
`structConst3`); for arbitrary `N` the only available definition is through the trace,

```
f^{abc} = -2i · Tr([Tᵃ, Tᵇ] Tᶜ),
```

which is well posed precisely because `suNTraceStatement` is proved.  With that
definition `Σ_{c,d} f^{acd} f^{bcd} = N δ^{ab}` follows from `suN_completeness` applied
twice — once to collapse the `d` sum, once for `c` — but each application first needs the
four-generator trace expanded over the three families and the sum over the adjoint index
`SUNIndex N` handled as a sum type, which is a module's worth of work rather than a
lemma's.  `su(3)`'s analogue fell only to a trick specific to a finite table (rewriting
the lookup as vector literals), which does not generalize.

The single named goal is therefore: define `suNStructConst : SUNIndex N → SUNIndex N →
SUNIndex N → ℝ` by the trace formula above, and prove
`Σ_{c,d} f^{acd} f^{bcd} = N · δ^{ab}`. -/

end SUNGen

end RepresentationColor
end QCD
end QFT
end Physlib
