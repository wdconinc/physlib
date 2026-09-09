/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic
/-!

# Kronecker delta

This module defines the Kronecker delta.

-/

@[expose] public section

namespace KroneckerDelta

variable {α M : Type*} [DecidableEq α]

/-- The Kronecker delta function, `ite (i = j) 1 0`. -/
def kroneckerDelta (i j : α) : ℕ := if i = j then 1 else 0

@[inherit_doc]
notation "δ[" i "," j "]" => kroneckerDelta i j

@[simp]
lemma eq_one_of_same (i : α) : δ[i,i] = 1 := if_pos rfl

lemma eq_zero_of_ne {i j : α} (h : i ≠ j) : δ[i,j] = 0 := if_neg h

@[simp]
lemma eq_of_coe {p : α → Prop} (i j : Subtype p) : δ[(i : α),j] = δ[i,j] := by
  rcases eq_or_ne i j with (rfl | hne)
  · repeat rw [eq_one_of_same]
  · rw [eq_zero_of_ne hne, eq_zero_of_ne <| Subtype.coe_ne_coe.mpr hne]

lemma eq_zero_of_not {p : α → Prop} {i j : α} (hi : ¬p i) (hj : p j) : δ[i,j] = 0 :=
  eq_zero_of_ne (fun h ↦ hi (h ▸ hj))

/-!
### Conditions for smul to vanish
-/

lemma smul_of_eq_zero [AddMonoid M] (i j : α) {f : α → α → M} (hf : f i i = 0) :
    δ[i,j] • f i j = 0 := by
  rcases eq_or_ne i j with (rfl | hne)
  · exact smul_eq_zero_of_right _ hf
  · exact smul_eq_zero_of_left (eq_zero_of_ne hne) _

lemma smul_eq_zero_iff [AddMonoid M] (i j : α) (f : α → α → M) :
    δ[i,j] • f i j = 0 ↔ i ≠ j ∨ f i i = 0 := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp
  · simp [eq_zero_of_ne, hne]

lemma smul_eq_zero_iff' [AddMonoid M] (i : α) (f : α → α → M) :
    (∀ j : α, δ[i,j] • f i j = 0) ↔ f i i = 0 := by
  refine ⟨fun h ↦ ?_, fun hf j ↦ smul_of_eq_zero i j hf⟩
  simpa [one_nsmul] using h i

lemma smul_eq_zero_iff'' [AddMonoid M] (f : α → α → M) :
    (∀ i j : α, δ[i,j] • f i j = 0) ↔ ∀ i : α, f i i = 0 :=
  forall_congr' fun j ↦ smul_eq_zero_iff' j f

/-!
### Symmetrization
-/

lemma symm (i j : α) : δ[i,j] = δ[j,i] := ite_cond_congr <| Eq.propIntro Eq.symm Eq.symm

lemma smul_symm [AddMonoid M] (i j : α) (f : α → α → M) : δ[i,j] • f j i = δ[i,j] • f i j := by
  rcases eq_or_ne i j with (rfl | hne)
  · rfl
  · simp only [eq_zero_of_ne hne, zero_smul]

lemma symmetrize [AddMonoid M] (i j : α) (f : α → α → M) :
    δ[i,j] • (f i j + f j i) = (2 * δ[i,j]) • f i j := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp [two_nsmul]
  · simp [eq_zero_of_ne hne]

lemma symmetrize' [AddCommMonoid M] {K : Type*} [Semifield K] [CharZero K] [Module K M]
    (i j : α) (f : α → α → M) : δ[i,j] • (2 : K)⁻¹ • (f i j + f j i) = δ[i,j] • f i j := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp only [eq_one_of_same, one_nsmul, ← two_smul K, smul_smul]
    rw [inv_mul_cancel₀ (OfNat.zero_ne_ofNat 2).symm, one_smul]
  · simp [eq_zero_of_ne hne]

@[simp]
lemma smul_sub_eq_zero [AddGroup M] (i j : α) (f : α → α → M) : δ[i,j] • (f i j - f j i) = 0 := by
  rcases eq_or_ne i j with (rfl | hne)
  · exact smul_eq_zero_of_right _ (sub_self <| f i i)
  · exact smul_eq_zero_of_left (eq_zero_of_ne hne) _

/-!
### Sums
-/

section Sums
open Finset

variable [AddCommMonoid M]

@[simp]
lemma sum_mul [Fintype α] (i j : α) : ∑ k : α, δ[i,k] * δ[k,j] = δ[i,j] := by
  simp [kroneckerDelta]

@[simp]
lemma sum_smul [Fintype α] (i : α) (f : α → M) : ∑ j : α, δ[i,j] • f j = f i := by
  simp [kroneckerDelta]

lemma sum_sum_smul_eq_zero [Fintype α] {f : α → α → M} (hf : ∀ i : α, f i i = 0) :
    ∑ i : α, ∑ j : α, δ[i,j] • f i j = 0 := by
  simp [sum_smul, hf, sum_const_zero]

lemma finset_sum_smul (s : Finset α) (i : α) (f : α → M) :
    ∑ j ∈ s, δ[i,j] • f j = if i ∈ s then f i else 0 := by
  simp [kroneckerDelta]

lemma finset_sum_sum_smul_eq_zero {s s' : Finset α} {f : α → α → M}
    (hf : ∀ i ∈ s ∩ s', f i i = 0) : ∑ i ∈ s, ∑ j ∈ s', δ[i,j] • f i j = 0 := by
  simp only [finset_sum_smul, Finset.sum_ite_mem]
  rw [← sum_coe_sort]
  simp [hf]

end Sums

/-!

# Generalized Kronecker delta

-/

section Generalized
open Matrix

/-- Integer-valued Kronecker entry via the existing `kroneckerDelta`. -/
local notation "δℤ" => (fun ρ σ => ((kroneckerDelta ρ σ : ℕ) : ℤ))

/-- Generalized Kronecker delta:
`δ^{μ₁...μₙ}_{ν₁...νₙ} = det (δ[μᵢ, νⱼ])`.

This is defined for any finite type `α` with decidable equality. -/
def generalizedKroneckerDelta {α ι : Type} [DecidableEq α]
    [DecidableEq ι] [Fintype ι]
    (μ : ι → α) (ν : ι → α) : ℤ :=
  Matrix.det (fun i j => δℤ (μ i) (ν j))

/-- Extends two index blocks into a single `Fin n → α` map.
For indices `< k` it uses `μ`, and for indices `≥ k` it uses `lam` with the shifted index. -/
def extendIndices {α : Type} (k n : ℕ) (_hk : k ≤ n)
    (μ : Fin k → α) (lam : Fin (n - k) → α) : Fin n → α :=
  fun i =>
    if h : i.1 < k then μ ⟨i.1, h⟩
    else lam ⟨i.1 - k, Nat.sub_lt_sub_right (Nat.le_of_not_lt h) i.2⟩

/-- On indices `< k`, `extendIndices` returns the head function `μ`. -/
@[simp] lemma extendIndices_of_lt {α : Type} {k n : ℕ} (hk : k ≤ n)
    (μ : Fin k → α) (lam : Fin (n - k) → α) (i : Fin n) (h : i.1 < k) :
    extendIndices k n hk μ lam i = μ ⟨i.1, h⟩ := by simp [extendIndices, h]

/-- On indices `≥ k`, `extendIndices` returns the tail function `lam`. -/
@[simp] lemma extendIndices_of_not_lt {α : Type} {k n : ℕ} (hk : k ≤ n)
    (μ : Fin k → α) (lam : Fin (n - k) → α) (i : Fin n) (h : ¬ i.1 < k) :
    extendIndices k n hk μ lam i =
      lam ⟨i.1 - k, Nat.sub_lt_sub_right (Nat.le_of_not_lt h) i.2⟩ := by
  simp [extendIndices, h]

/-- The last index of an `extendIndices` map lands in the tail component. -/
@[simp] lemma extendIndices_last {α : Type} {m : ℕ} (hm : 1 ≤ m)
    (μ : Fin (m - 1) → α) (lam : Fin (m - (m - 1)) → α) :
    extendIndices (m - 1) m (Nat.sub_le _ _) μ lam ⟨m - 1, by omega⟩ =
      lam ⟨0, by omega⟩ := by simp [extendIndices]

private def finLastOfPos (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩

/-- The value of `finLastOfPos` is definitionally `n - 1`. -/
@[simp] private lemma finLastOfPos_val (n : ℕ) (hn : 0 < n) :
    (finLastOfPos n hn).1 = n - 1 := rfl

/-- Decomposes an `extendIndices` with `Fin.snoc` into a nested extension form. -/
private lemma extendIndices_snoc_comp {α : Type} {k m : ℕ} (hk : k + 1 ≤ m)
    (μ : Fin k → α) (l : α) (lam : Fin (m - (k + 1)) → α) :
    extendIndices (k + 1) m hk (Fin.snoc μ l) lam =
      extendIndices k m (by omega) μ
        (extendIndices 1 (m - k) (by omega) (fun _ : Fin 1 => l) lam) := by
  funext i
  by_cases hi : i.1 < k
  · have hi_succ : i.1 < k + 1 := by omega
    have hidx : (⟨i.1, hi_succ⟩ : Fin (k + 1)) = (⟨i.1, hi⟩ : Fin k).castSucc := by
      ext; rfl
    rw [extendIndices_of_lt hk (Fin.snoc μ l) lam i hi_succ]
    rw [extendIndices_of_lt (by omega) μ
      (extendIndices 1 (m - k) (by omega) (fun _ : Fin 1 => l) lam) i hi]
    rw [hidx, Fin.snoc_castSucc]
  · by_cases hi_eq : i.1 = k
    · have hi_succ : i.1 < k + 1 := by omega
      have hidx : (⟨i.1, hi_succ⟩ : Fin (k + 1)) = Fin.last k := by
        ext; simp [hi_eq, Fin.last]
      have hone : i.1 - k < 1 := by omega
      rw [extendIndices_of_lt hk (Fin.snoc μ l) lam i hi_succ]
      rw [extendIndices_of_not_lt (by omega) μ
        (extendIndices 1 (m - k) (by omega) (fun _ : Fin 1 => l) lam) i hi]
      rw [hidx, Fin.snoc_last]
      simp [extendIndices, hi_eq]
    · have hi_succ_not : ¬ i.1 < k + 1 := by omega
      have hnot_one : ¬ i.1 - k < 1 := by omega
      rw [extendIndices_of_not_lt hk (Fin.snoc μ l) lam i hi_succ_not]
      rw [extendIndices_of_not_lt (by omega) μ
        (extendIndices 1 (m - k) (by omega) (fun _ : Fin 1 => l) lam) i hi]
      simp [extendIndices, hnot_one]
      congr 1

/-- Reindexes functions on `Fin (k+1)` into head-tail (`Fin.cons`) form under summation. -/
lemma sum_univ_fin_succ_fun {α β : Type} [Fintype α] [DecidableEq α]
    [AddCommMonoid β] (k : ℕ) (f : (Fin (k + 1) → α) → β) :
    (∑ x, f x) = ∑ a, ∑ v : Fin k → α, f (Fin.cons a v) := by
  simpa [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => α)).symm
      (fun x : Fin (k + 1) → α => f x)
      (fun p : α × (Fin k → α) => f (Fin.cons p.1 p.2)) (by intro p; simp))

/-- Reindexes functions on `Fin (k+1)` into tail-last (`Fin.snoc`) form under summation. -/
lemma sum_univ_fin_succ_snoc {α β : Type} [Fintype α] [DecidableEq α]
    [AddCommMonoid β] (k : ℕ) (f : (Fin (k + 1) → α) → β) :
    (∑ x, f x) = ∑ v : Fin k → α, ∑ a, f (Fin.snoc v a) := by
  rw [show (∑ x, f x) = ∑ a, ∑ v : Fin k → α, f (Fin.snoc v a) by
    simpa [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (k + 1) => α)).symm
      (fun x : Fin (k + 1) → α => f x)
      (fun p : α × (Fin k → α) => f (Fin.snoc p.2 p.1)) (by intro p; simp))]
  rw [Finset.sum_comm]

private def contractionCoeff : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 1
  | k + 1, m, d => contractionCoeff k m d * ((d + 2 - (m - k) : ℕ) : ℤ)

/-- Base value of `contractionCoeff` at `k = 0`. -/
@[simp] private lemma contractionCoeff_zero (m d : ℕ) : contractionCoeff 0 m d = 1 := rfl

/-- Recursive step for `contractionCoeff`. -/
@[simp] private lemma contractionCoeff_succ (k m d : ℕ) :
    contractionCoeff (k + 1) m d =
  contractionCoeff k m d * ((d + 2 - (m - k) : ℕ) : ℤ) := rfl

/-- Moves the last appended index to the front using `Fin.cycleRange`. -/
private lemma extendIndices_last_eq_front_cycleRange {α : Type} {m : ℕ} (hm : 1 ≤ m)
    (μ : Fin (m - 1) → α) (l : α) :
    extendIndices (m - 1) m (Nat.sub_le _ _) μ (fun _ => l) =
      fun i => extendIndices 1 m hm (fun _ : Fin 1 => l) μ
        ((Fin.cycleRange (finLastOfPos m hm)) i) := by
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  funext i
  by_cases hlast : i = finLastOfPos m hm
  · subst i
    have hcycle : Fin.cycleRange (finLastOfPos m hm) (finLastOfPos m hm) = 0 := by
        simp
    rw [hcycle]
    simp [extendIndices, finLastOfPos]
  · have hlt : i < finLastOfPos m hm := by
      by_contra hi
      have hge : m - 1 ≤ i.1 := by
        exact le_of_not_gt (by intro h; exact hi (Fin.lt_def.mpr (by simpa [finLastOfPos] using h)))
      have hval : i.1 = m - 1 := by omega
      apply hlast
      ext
      simp [finLastOfPos, hval]
    have hcycle : Fin.cycleRange (finLastOfPos m hm) i = i + 1 :=
      Fin.cycleRange_of_lt hlt
    have hi_tail : i.1 < m - 1 := by
      change i.1 < m - 1 at hlt
      exact hlt
    rw [hcycle]
    simp [extendIndices, hi_tail, Fin.val_add, Nat.mod_eq_of_lt (by omega : i.1 + 1 < m)]

/-- Generalized Kronecker delta is invariant under moving the final repeated index to the front. -/
private lemma generalizedKroneckerDelta_last_eq_front {m d : ℕ} (hm : 1 ≤ m)
    (μ ν : Fin (m - 1) → Fin (d + 1)) (l : Fin (d + 1)) :
    generalizedKroneckerDelta
        (extendIndices (m - 1) m (Nat.sub_le _ _) μ (fun _ => l))
        (extendIndices (m - 1) m (Nat.sub_le _ _) ν (fun _ => l)) =
      generalizedKroneckerDelta
        (extendIndices 1 m hm (fun _ : Fin 1 => l) μ)
        (extendIndices 1 m hm (fun _ : Fin 1 => l) ν) := by
  simp only [generalizedKroneckerDelta]
  let σ : Equiv.Perm (Fin m) := Fin.cycleRange (finLastOfPos m hm)
  have hμ := extendIndices_last_eq_front_cycleRange hm μ l
  have hν := extendIndices_last_eq_front_cycleRange hm ν l
  calc
    Matrix.det (fun i j : Fin m =>
        δℤ
          (extendIndices (m - 1) m (Nat.sub_le _ _) μ (fun _ => l) i)
          (extendIndices (m - 1) m (Nat.sub_le _ _) ν (fun _ => l) j))
        = Matrix.det (Matrix.submatrix
            (fun i j : Fin m =>
              δℤ
                (extendIndices 1 m hm (fun _ : Fin 1 => l) μ i)
                (extendIndices 1 m hm (fun _ : Fin 1 => l) ν j)) σ σ) := by
          congr 1
          funext i j
          simp [Matrix.submatrix_apply, σ, hμ, hν]
    _ = Matrix.det (fun i j : Fin m =>
            δℤ
              (extendIndices 1 m hm (fun _ : Fin 1 => l) μ i)
              (extendIndices 1 m hm (fun _ : Fin 1 => l) ν j)) := by
          rw [Matrix.det_submatrix_equiv_self]

/-- Pulls a finite sum through determinant after updating a fixed row linearly. -/
private lemma det_updateRow_finsum_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n)
    {β : Type} [Fintype β] (w : β → ℤ) (f : β → Fin n → ℤ) :
    ∑ l, w l * Matrix.det (A.updateRow i (f l)) =
    Matrix.det (A.updateRow i (fun j => ∑ l, w l * f l j)) := by
  haveI := Classical.decEq β
  have key : ∀ (t : Finset β),
      ∑ l ∈ t, w l * Matrix.det (A.updateRow i (f l)) =
      Matrix.det (A.updateRow i (fun j => ∑ l ∈ t, w l * f l j)) := by
    intro t
    induction t using Finset.cons_induction with
    | empty =>
      simp only [Finset.sum_empty]
      symm
      exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [Matrix.updateRow_self])
    | cons a rest ha ih =>
      simp only [Finset.sum_cons, ih]
      rw [show (fun j => w a * f a j + ∑ l ∈ rest, w l * f l j) =
              w a • f a + (fun j => ∑ l ∈ rest, w l * f l j) from
              funext (fun j => by simp),
          Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  exact key Finset.univ

/-- Summing row updates against a Kronecker row recovers the original determinant. -/
private lemma sum_updateRow_delta {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n)
    (μ_i : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hrow : A i = fun j => δℤ μ_i (ν j)) :
    ∑ l : Fin (d + 1),
      δℤ μ_i l *
        Matrix.det (A.updateRow i (fun j => δℤ l (ν j))) =
    Matrix.det A := by
  rw [det_updateRow_finsum_smul]
  have hrow_eq : (fun j => ∑ l : Fin (d + 1),
      δℤ μ_i l * δℤ l (ν j)) = A i := by
    funext j
    calc
      ∑ l : Fin (d + 1), δℤ μ_i l * δℤ l (ν j) = ((δ[μ_i, ν j] : ℕ) : ℤ) := by
        by_cases h : μ_i = ν j
        · subst h
          simp [kroneckerDelta]
        · simp [kroneckerDelta, h]
      _ = (fun j => δℤ μ_i (ν j)) j := by rfl
      _ = A i j := by simp [hrow]
  rw [hrow_eq, Matrix.updateRow_eq_self]

/-- Identifies the bordered submatrix obtained by deleting the last row and column. -/
private lemma bordered_submatrix_last_eq {n d : ℕ}
    (μ ν : Fin n → Fin (d + 1)) (l : Fin (d + 1)) :
    Matrix.submatrix
      (fun (i j : Fin (n + 1)) =>
        δℤ
          (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) i)
          (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) j))
      (Fin.last n).succAbove (Fin.last n).succAbove =
    fun (i j : Fin n) => δℤ (μ i) (ν j) := by
  funext i j
  simp only [Matrix.submatrix_apply]
  have hi : (Fin.last n).succAbove i = i.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last i)
  have hj : (Fin.last n).succAbove j = j.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last j)
  rw [hi, hj]
  simp [extendIndices, Fin.val_castSucc, i.isLt, j.isLt]

/-- Computes `extendIndices` along a `succAbove` index as a `cycleIcc` action. -/
private lemma extendIndices_succAbove_eq_cycleIcc {n : ℕ} (hn : 0 < n)
    {α : Type} (μ : Fin n → α) (i p : Fin n) :
    extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => μ i) (i.castSucc.succAbove p) =
      μ ((Fin.cycleIcc i (finLastOfPos n hn)) p) := by
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  by_cases hlast : p = finLastOfPos n hn
  · subst p
    have hrow : i.castSucc.succAbove (finLastOfPos n hn) = Fin.last n := by
      have hle : i.castSucc ≤ (finLastOfPos n hn).castSucc :=
        Fin.le_def.mpr (by simp [finLastOfPos]; omega)
      rw [Fin.succAbove_of_le_castSucc _ _ hle]
      ext
      simp [Fin.last, finLastOfPos]
      omega
    have hcycle : (Fin.cycleIcc i (finLastOfPos n hn)) (finLastOfPos n hn) = i := by
      exact Fin.cycleIcc_of_last (i := i) (j := finLastOfPos n hn)
        (Fin.le_def.mpr (by change i.1 ≤ n - 1; omega))
    rw [hrow, hcycle]
    simp [extendIndices, Fin.last]
  · have hlt_last : p < finLastOfPos n hn := by
      by_contra hp
      have hpval : p.1 = n - 1 := by
        have hnot : ¬ p.1 < n - 1 := by
          intro h
          exact hp (Fin.lt_def.mpr (by simpa [finLastOfPos] using h))
        have hge : n - 1 ≤ p.1 := le_of_not_gt hnot
        omega
      apply hlast
      ext
      simp [finLastOfPos, hpval]
    by_cases hpi : p < i
    · have hrow : i.castSucc.succAbove p = p.castSucc :=
        Fin.succAbove_castSucc_of_lt i p hpi
      have hcycle : (Fin.cycleIcc i (finLastOfPos n hn)) p = p :=
        Fin.cycleIcc_of_lt (j := finLastOfPos n hn) hpi
      rw [hrow, hcycle]
      simp [extendIndices, Fin.val_castSucc, p.isLt]
    · have hip : i ≤ p := le_of_not_gt hpi
      have hrow : i.castSucc.succAbove p = p.succ :=
        Fin.succAbove_castSucc_of_le i p hip
      have hcycle : (Fin.cycleIcc i (finLastOfPos n hn)) p = p + 1 :=
        Fin.cycleIcc_of_ge_of_lt hip hlt_last
      rw [hrow, hcycle]
      have hsucc_lt : p.1 + 1 < n := by
        change p.1 < n - 1 at hlt_last
        omega
      have hfin : (⟨p.1 + 1, hsucc_lt⟩ : Fin n) = p + 1 := by
        ext
        simp [Fin.val_add, Nat.mod_eq_of_lt hsucc_lt]
      simp [extendIndices, Fin.val_succ, hsucc_lt, hfin]

/-- Rewrites the cast-succ minor as a `cycleIcc`-reindexed submatrix. -/
private lemma castSucc_minor_eq_cycleIcc {n : ℕ} (hn : 0 < n)
  {α : Type} [DecidableEq α] (μ ν : Fin n → α) (i : Fin n) :
    Matrix.submatrix
      (fun (p q : Fin (n + 1)) =>
        δℤ
          (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => μ i) p)
          (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => μ i) q))
      i.castSucc.succAbove (Fin.last n).succAbove =
    Matrix.submatrix
      (fun (p q : Fin n) => δℤ (μ p) (ν q))
      (Fin.cycleIcc i (finLastOfPos n hn)) id := by
  funext p q
  simp only [Matrix.submatrix_apply, id_eq]
  have hp := extendIndices_succAbove_eq_cycleIcc hn μ i p
  have hq : (Fin.last n).succAbove q = q.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last q)
  rw [hp, hq]
  simp [extendIndices, Fin.val_castSucc]

/-- Determinant of the cast-succ minor, expressed via a sign and the base determinant. -/
private lemma castSucc_minor_det {n : ℕ} (hn : 0 < n)
  {α : Type} [DecidableEq α] (μ ν : Fin n → α) (i : Fin n) :
    Matrix.det
      (Matrix.submatrix
        (fun (p q : Fin (n + 1)) =>
          δℤ
            (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => μ i) p)
            (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => μ i) q))
        i.castSucc.succAbove (Fin.last n).succAbove) =
    (-1 : ℤ) ^ (n - 1 - (i : ℕ)) *
      Matrix.det (fun (p q : Fin n) => δℤ (μ p) (ν q)) := by
  rw [castSucc_minor_eq_cycleIcc hn]
  rw [Matrix.det_permute]
  have hsign := Fin.sign_cycleIcc_of_le (i := i) (j := finLastOfPos n hn)
    (Fin.le_def.mpr (by simp [finLastOfPos]; omega))
  have hsub : (finLastOfPos n hn : ℕ) - (i : ℕ) = n - 1 - (i : ℕ) := by
    simp [finLastOfPos]
  rw [hsign, hsub]
  norm_num

/-- Laplace expansion identity for a cast-succ column term in the contraction proof. -/
private lemma laplace_castSucc_term {n d : ℕ} (_hnd : n + 1 ≤ d + 1)
    (μ ν : Fin n → Fin (d + 1)) (i : Fin n) :
    ∑ l : Fin (d + 1),
      (-1 : ℤ) ^ ((i : ℕ) + (Fin.last n : ℕ)) *
        (δℤ
          (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) i.castSucc)
          (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) (Fin.last n))) *
        Matrix.det
          (Matrix.submatrix
            (fun (p q : Fin (n + 1)) =>
              δℤ
                (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) p)
                (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) q))
            i.castSucc.succAbove (Fin.last n).succAbove) =
    -Matrix.det (fun (p q : Fin n) => δℤ (μ p) (ν q)) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.1) i.isLt
  have hleft : ∀ l : Fin (d + 1),
      extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) i.castSucc = μ i := by
    intro l
    simp [extendIndices, Fin.val_castSucc, i.isLt]
  have hright : ∀ l : Fin (d + 1),
      extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) (Fin.last n) = l := by
    intro l
    simp [extendIndices, Fin.last]
  simp_rw [hleft, hright]
  rw [Finset.sum_eq_single (μ i)]
  · have hdelta : (((δ[μ i, μ i]) : ℕ) : ℤ) = 1 := by
      simp [kroneckerDelta]
    rw [hdelta]
    simp only [mul_one]
    rw [castSucc_minor_det hn]
    have hpow :
        (-1 : ℤ) ^ (((i : ℕ) + (Fin.last n : ℕ)) + (n - 1 - (i : ℕ))) = -1 := by
      have hsum : ((i : ℕ) + (Fin.last n : ℕ)) + (n - 1 - (i : ℕ)) = 2 * n - 1 := by
        simp [Fin.last]
        omega
      rw [hsum]
      exact Odd.neg_one_pow (by use n - 1; omega)
    rw [← mul_assoc, ← pow_add, hpow]
    ring
  · intro l _ hl
    simp [kroneckerDelta, hl.symm]
  · intro hmem
    simp at hmem

/-- Laplace expansion identity for the last column term in the contraction proof. -/
private lemma laplace_last_term {n d : ℕ} (_hnd : n + 1 ≤ d + 1)
    (μ ν : Fin n → Fin (d + 1)) :
    ∑ l : Fin (d + 1),
      (-1 : ℤ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) *
        (δℤ
          (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) (Fin.last n))
          (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) (Fin.last n))) *
        Matrix.det
          (Matrix.submatrix
            (fun (i j : Fin (n + 1)) =>
              δℤ
                (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) i)
                (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) j))
            (Fin.last n).succAbove (Fin.last n).succAbove) =
    (d + 1 : ℤ) * Matrix.det (fun (i j : Fin n) => δℤ (μ i) (ν j)) := by
  have h_entry : ∀ l : Fin (d + 1),
      extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) (Fin.last n) = l ∧
      extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) (Fin.last n) = l := fun l =>
    ⟨by simp [extendIndices, Fin.last],
     by simp [extendIndices, Fin.last]⟩
  simp_rw [fun l => (h_entry l).1, fun l => (h_entry l).2]
  simp_rw [bordered_submatrix_last_eq]
  simp only [kroneckerDelta,
             show (Fin.last n : ℕ) = n from rfl,
             show n + n = 2 * n from by ring,
             pow_mul, neg_one_sq, one_pow, one_mul]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  push_cast; ring

/-!
## Generalized contraction over an arbitrary finite index type

The lemmas below mirror the `Fin (d + 1)` Laplace-based contraction proof but are
parametrized by an arbitrary finite index type `ι` with decidable equality.
The ambient-dimension coefficient `d + 2 - m` is replaced by `Fintype.card ι + 1 - m`.
-/

section GeneralizedContraction

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Cyclic reindexing invariance for repeated-index placement.

Mathematically, this is the statement that moving the repeated index `l`
from the last slot to the first slot on both upper and lower index lists
does not change the generalized Kronecker delta value:

`δ^{μ_1 ... μ_{m-1} l}_{ν_1 ... ν_{m-1} l} = δ^{l μ_1 ... μ_{m-1}}_{l ν_1 ... ν_{m-1}}`.

The proof is determinant-invariance under a common permutation of rows and columns
(implemented with `Fin.cycleRange`). -/
private lemma generalizedKroneckerDelta_last_eq_front' {m : ℕ} (hm : 1 ≤ m)
    (μ ν : Fin (m - 1) → ι) (l : ι) :
    generalizedKroneckerDelta
        (extendIndices (m - 1) m (Nat.sub_le _ _) μ (fun _ => l))
        (extendIndices (m - 1) m (Nat.sub_le _ _) ν (fun _ => l)) =
      generalizedKroneckerDelta
        (extendIndices 1 m hm (fun _ : Fin 1 => l) μ)
        (extendIndices 1 m hm (fun _ : Fin 1 => l) ν) := by
  simp only [generalizedKroneckerDelta]
  let σ : Equiv.Perm (Fin m) := Fin.cycleRange (finLastOfPos m hm)
  have hμ := extendIndices_last_eq_front_cycleRange hm μ l
  have hν := extendIndices_last_eq_front_cycleRange hm ν l
  calc
    Matrix.det (fun i j : Fin m =>
        δℤ
          (extendIndices (m - 1) m (Nat.sub_le _ _) μ (fun _ => l) i)
          (extendIndices (m - 1) m (Nat.sub_le _ _) ν (fun _ => l) j))
        = Matrix.det (Matrix.submatrix
            (fun i j : Fin m =>
              δℤ
                (extendIndices 1 m hm (fun _ : Fin 1 => l) μ i)
                (extendIndices 1 m hm (fun _ : Fin 1 => l) ν j)) σ σ) := by
          congr 1; funext i j
          simp [Matrix.submatrix_apply, σ, hμ, hν]
      _ = Matrix.det (fun i j : Fin m =>
              δℤ
                (extendIndices 1 m hm (fun _ : Fin 1 => l) μ i)
                (extendIndices 1 m hm (fun _ : Fin 1 => l) ν j)) := by
          rw [Matrix.det_submatrix_equiv_self]

/-- Generic version of `bordered_submatrix_last_eq`. -/
private lemma bordered_submatrix_last_eq' (μ ν : Fin n → ι) (l : ι) :
    Matrix.submatrix
      (fun (i j : Fin (n + 1)) =>
        δℤ
          (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) i)
          (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) j))
      (Fin.last n).succAbove (Fin.last n).succAbove =
    fun (i j : Fin n) => δℤ (μ i) (ν j) := by
  funext i j
  simp only [Matrix.submatrix_apply]
  have hi : (Fin.last n).succAbove i = i.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last i)
  have hj : (Fin.last n).succAbove j = j.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last j)
  rw [hi, hj]
  simp [extendIndices, Fin.val_castSucc, i.isLt, j.isLt]

/-- Generic version of `laplace_castSucc_term`: the off-diagonal Laplace terms
telescope to the negated minor determinant for any finite index type. -/
private lemma laplace_castSucc_term' (μ ν : Fin n → ι) (i : Fin n) :
    ∑ l : ι,
      (-1 : ℤ) ^ ((i : ℕ) + (Fin.last n : ℕ)) *
        (δℤ
          (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) i.castSucc)
          (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) (Fin.last n))) *
        Matrix.det
          (Matrix.submatrix
            (fun (p q : Fin (n + 1)) =>
              δℤ
                (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) p)
                (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) q))
            i.castSucc.succAbove (Fin.last n).succAbove) =
    -Matrix.det (fun (p q : Fin n) => δℤ (μ p) (ν q)) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.1) i.isLt
  have hleft : ∀ l : ι,
      extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) i.castSucc = μ i :=
    fun l => by simp [extendIndices, Fin.val_castSucc, i.isLt]
  have hright : ∀ l : ι,
      extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) (Fin.last n) = l :=
    fun l => by simp [extendIndices, Fin.last]
  simp_rw [hleft, hright]
  rw [Finset.sum_eq_single (μ i)]
  · simp only [kroneckerDelta]
    have hdelta : ((if True then 1 else 0 : ℕ) : ℤ) = 1 := by decide
    rw [hdelta]
    have hminor :
        (-1 : ℤ) ^ ((i : ℕ) + (Fin.last n : ℕ)) *
          Matrix.det
            (Matrix.submatrix
              (fun (p q : Fin (n + 1)) =>
                δℤ
                  (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => μ i) p)
                  (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => μ i) q))
              i.castSucc.succAbove (Fin.last n).succAbove) =
        -Matrix.det (fun (p q : Fin n) => δℤ (μ p) (ν q)) := by
      rw [castSucc_minor_det hn μ ν i]
      have hpow :
          (-1 : ℤ) ^ ((i : ℕ) + (Fin.last n : ℕ)) *
            (-1 : ℤ) ^ (n - 1 - (i : ℕ)) = -1 := by
        have hsum : ((i : ℕ) + (Fin.last n : ℕ)) + (n - 1 - (i : ℕ)) = 2 * n - 1 := by
          simp [Fin.last]; omega
        rw [← pow_add, hsum]
        exact Odd.neg_one_pow (by use n - 1; omega)
      have hpow' := congrArg (fun t : ℤ => t * Matrix.det (fun (p q : Fin n) => δℤ (μ p) (ν q))) hpow
      simpa [mul_assoc] using hpow'
    simpa [kroneckerDelta] using hminor
  · intro l _ hl; simp [kroneckerDelta, Ne.symm hl]
  · intro hmem; simp at hmem

/-- Generic version of `laplace_last_term`: the diagonal Laplace term sums to
`Fintype.card ι` times the minor determinant. -/
private lemma laplace_last_term' (μ ν : Fin n → ι) :
    ∑ l : ι,
      (-1 : ℤ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) *
        (δℤ
          (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) (Fin.last n))
          (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) (Fin.last n))) *
        Matrix.det
          (Matrix.submatrix
            (fun (i j : Fin (n + 1)) =>
              δℤ
                (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) i)
                (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) j))
            (Fin.last n).succAbove (Fin.last n).succAbove) =
    (Fintype.card ι : ℤ) * Matrix.det (fun (i j : Fin n) => δℤ (μ i) (ν j)) := by
  have h_entry : ∀ l : ι,
      extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) (Fin.last n) = l ∧
      extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) (Fin.last n) = l := fun l =>
    ⟨by simp [extendIndices, Fin.last], by simp [extendIndices, Fin.last]⟩
  simp_rw [fun l => (h_entry l).1, fun l => (h_entry l).2]
  simp_rw [bordered_submatrix_last_eq']
  simp only [kroneckerDelta,
             show (Fin.last n : ℕ) = n from rfl,
             show n + n = 2 * n from by ring,
             pow_mul, neg_one_sq, one_pow, one_mul]
  rw [Finset.sum_const, Finset.card_univ]
  push_cast; ring

/-- One-step contraction coefficient over a finite index type.

For rank `m`, summing over one repeated index pair contracts

`δ^{μ_1 ... μ_{m-1} l}_{ν_1 ... ν_{m-1} l}`

to a scalar multiple of the rank-`m-1` generalized delta:

`∑_l δ^{μ_1 ... μ_{m-1} l}_{ν_1 ... ν_{m-1} l}
  = (|ι| + 1 - m) · δ^{μ_1 ... μ_{m-1}}_{ν_1 ... ν_{m-1}}`.

Here `|ι| = Fintype.card ι` is the ambient index-set size. -/
private theorem generalizedKroneckerDeltaReal_contraction_base' (m : ℕ) (hm : 1 ≤ m)
    (hmd : m ≤ Fintype.card ι)
    (μ : Fin (m - 1) → ι) (ν : Fin (m - 1) → ι) :
    (∑ l : ι,
      generalizedKroneckerDelta
        (extendIndices (m - 1) m (Nat.sub_le _ _) μ (fun _ => l))
        (extendIndices (m - 1) m (Nat.sub_le _ _) ν (fun _ => l))) =
    ((Fintype.card ι + 1 - m : ℕ) : ℤ) * generalizedKroneckerDelta μ ν := by
  cases m with
  | zero => omega
  | succ n =>
    simp only [Nat.succ_sub_one, generalizedKroneckerDelta]
    simp_rw [Matrix.det_succ_column _ (Fin.last n)]
    rw [Finset.sum_comm, Fin.sum_univ_castSucc]
    have hlast :
        (∑ l : ι,
          (-1 : ℤ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) *
            (δℤ
              (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) (Fin.last n))
              (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) (Fin.last n))) *
            Matrix.det
              (Matrix.submatrix
                (fun (i j : Fin (n + 1)) =>
                  δℤ
                    (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) i)
                    (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) j))
                (Fin.last n).succAbove (Fin.last n).succAbove)) =
        (Fintype.card ι : ℤ) * Matrix.det (fun (i j : Fin n) => δℤ (μ i) (ν j)) := by
      exact laplace_last_term' (μ := μ) (ν := ν)
    rw [hlast]
    have hcast' : ∀ i : Fin n,
        ∑ l : ι,
          (-1 : ℤ) ^ ((i.castSucc : ℕ) + (Fin.last n : ℕ)) *
              δℤ
                (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) i.castSucc)
                (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) (Fin.last n)) *
            Matrix.det
              (Matrix.submatrix
                (fun p q : Fin (n + 1) =>
                  δℤ
                    (extendIndices n (n + 1) (Nat.le_succ n) μ (fun _ => l) p)
                    (extendIndices n (n + 1) (Nat.le_succ n) ν (fun _ => l) q))
                i.castSucc.succAbove (Fin.last n).succAbove) =
          -Matrix.det (fun p q : Fin n => δℤ (μ p) (ν q)) := by
      intro i
      exact laplace_castSucc_term' μ ν i
    simp_rw [hcast']
    rw [Finset.sum_const, Finset.card_univ]
    have hnd : n < Fintype.card ι := by omega
    have hcoeff : ((Fintype.card ι + 1 - (n + 1) : ℕ) : ℤ) =
        ((Fintype.card ι : ℤ) - n) := by
      have hnat : Fintype.card ι + 1 - (n + 1) = Fintype.card ι - n := by omega
      rw [hnat, Nat.cast_sub (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hnd))]
    rw [hcoeff]
    let D : ℤ := Matrix.det (fun p q => δℤ (μ p) (ν q))
    change (Fintype.card (Fin n) : ℤ) • (-D) + (Fintype.card ι : ℤ) * D =
      ((Fintype.card ι : ℤ) - n) * D
    rw [show (Fintype.card (Fin n) : ℤ) = n by simp]
    have hring : (n : ℤ) * (-D) + (Fintype.card ι : ℤ) * D = ((Fintype.card ι : ℤ) - n) * D := by
      ring
    simpa [zsmul_eq_mul] using hring

/-- Front-index form of the one-step contraction identity.

This is the same contraction factor as
`generalizedKroneckerDeltaReal_contraction_base'`, but with the summed index
inserted in the first position instead of the last:

`∑_l δ^{l μ_1 ... μ_{m-1}}_{l ν_1 ... ν_{m-1}}
  = (|ι| + 1 - m) · δ^{μ_1 ... μ_{m-1}}_{ν_1 ... ν_{m-1}}`.

It is obtained by combining cyclic reindexing invariance with the base lemma. -/
private lemma generalizedKroneckerDeltaReal_contraction_base_front' (m : ℕ) (hm : 1 ≤ m)
    (hmd : m ≤ Fintype.card ι)
    (μ : Fin (m - 1) → ι) (ν : Fin (m - 1) → ι) :
    (∑ l : ι,
      generalizedKroneckerDelta
        (extendIndices 1 m hm (fun _ : Fin 1 => l) μ)
        (extendIndices 1 m hm (fun _ : Fin 1 => l) ν)) =
    ((Fintype.card ι + 1 - m : ℕ) : ℤ) * generalizedKroneckerDelta μ ν :=
  calc
    _ = ∑ l : ι,
          generalizedKroneckerDelta
            (extendIndices (m - 1) m (Nat.sub_le _ _) μ (fun _ => l))
            (extendIndices (m - 1) m (Nat.sub_le _ _) ν (fun _ => l)) := by
          refine Finset.sum_congr rfl fun l _ =>
            (generalizedKroneckerDelta_last_eq_front' hm μ ν l).symm
    _ = _ := generalizedKroneckerDeltaReal_contraction_base' m hm hmd μ ν

/-- Zero-contraction identity (`k = 0`) for finite index type `ι`.

When no indices are contracted, the unique map `Fin 0 → ι` contributes exactly
the original expression, so the contraction sum is unchanged:

`∑_{μ : Fin 0 → ι} δ^{(μ,lam)}_{(μ,ω)} = δ^{lam}_{ω}`. -/
private lemma generalizedKroneckerDeltaReal_contraction_zero' (n : ℕ)
    (lam ω : Fin n → ι) :
    (∑ μ : Fin 0 → ι,
      generalizedKroneckerDelta
        (extendIndices 0 n (Nat.zero_le _) μ lam)
        (extendIndices 0 n (Nat.zero_le _) μ ω)) =
    generalizedKroneckerDelta lam ω := by
  simp; unfold generalizedKroneckerDelta; congr 1

/-- Full-rank `k`-index contraction via Laplace induction.

Assuming full rank `|ι| = n`, this proves the standard factorial contraction law:

`∑_{μ : Fin k → ι} δ^{(μ,lam)}_{(μ,ω)} = k! · δ^{lam}_{ω}`.

Interpretation:
- `μ` enumerates the contracted block of `k` repeated indices.
- `lam` and `ω` are the uncontracted tails of length `n - k`.
- each contraction step contributes the expected linear factor, and induction
  accumulates these factors to `k!`.

The proof structure is:
1. split `Fin (k+1)` as `Fin.snoc`;
2. commute the finite sums;
3. apply the one-step front-index contraction;
4. simplify coefficients under `|ι| = n`. -/
private theorem generalizedKroneckerDelta_contraction_fullRank_laplace' (k n : ℕ)
  (hk : k ≤ n) (hfull : Fintype.card ι = n)
    (lam : Fin (n - k) → ι) (ω : Fin (n - k) → ι) :
    (∑ μ : Fin k → ι,
      generalizedKroneckerDelta
        (extendIndices k n hk μ lam)
        (extendIndices k n hk μ ω)) =
    (Nat.factorial k : ℤ) * generalizedKroneckerDelta lam ω := by
  induction k generalizing n hfull with
  | zero =>
    simpa using (generalizedKroneckerDeltaReal_contraction_zero' (n := n) (lam := lam)
      (ω := ω))
  | succ k ih =>
    have hk' : k ≤ n := by omega
    rw [sum_univ_fin_succ_snoc k]
    simp_rw [extendIndices_snoc_comp (m := n) (hk := by omega)]
    rw [Finset.sum_comm]
    have hinner : ∀ l : ι,
        (∑ μ : Fin k → ι,
          generalizedKroneckerDelta
            (extendIndices k n (by omega) μ
              (extendIndices 1 (n - k) (by omega) (fun _ : Fin 1 => l) lam))
            (extendIndices k n (by omega) μ
              (extendIndices 1 (n - k) (by omega) (fun _ : Fin 1 => l) ω))) =
        (Nat.factorial k : ℤ) *
          generalizedKroneckerDelta
            (extendIndices 1 (n - k) (by omega) (fun _ : Fin 1 => l) lam)
            (extendIndices 1 (n - k) (by omega) (fun _ : Fin 1 => l) ω) :=
      fun l => by
        simpa using ih n hk' hfull
          (extendIndices 1 (n - k) (by omega) (fun _ : Fin 1 => l) lam)
          (extendIndices 1 (n - k) (by omega) (fun _ : Fin 1 => l) ω)
    simp_rw [hinner]
    rw [← Finset.mul_sum]
    rw [generalizedKroneckerDeltaReal_contraction_base_front' (n - k) (by omega)
      (by omega) lam ω]
    have hcoeff : ((Fintype.card ι + 1 - (n - k) : ℕ) : ℤ) = (k + 1 : ℤ) := by
      rw [hfull]
      have hnat : n + 1 - (n - k) = k + 1 := by omega
      exact_mod_cast hnat
    rw [hcoeff, Nat.factorial_succ, Nat.cast_mul]
    have hsub : n - k - 1 = n - (k + 1) := by omega
    have hgd : generalizedKroneckerDelta lam ω =
        generalizedKroneckerDelta lam ω := by
      rfl
    rw [hgd]
    have hkcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by norm_num
    rw [hkcast]; ring_nf

/-- Generalized Kronecker-delta contraction for an arbitrary finite index type `ι`.

For `k ≤ n` and `Fintype.card ι = n`:

`∑ μ : Fin k → ι, δ^{(μ,lam)}_{(μ,ω)} = k! · δ^{lam}_{ω}`

This is the coordinate-free finite-type form of generalized-delta contraction.
Compared to the old `Fin (d + 1)` presentation, the ambient index range is now
encoded intrinsically by `ι`, and the full-rank condition is `Fintype.card ι = n`.

So this theorem is the main contraction law to use in downstream files. -/
theorem generalizedKroneckerDelta_contraction (k n : ℕ) (hk : k ≤ n)
  (hfull : Fintype.card ι = n)
    (lam : Fin (n - k) → ι) (ω : Fin (n - k) → ι) :
    (∑ μ : Fin k → ι,
      generalizedKroneckerDelta
        (extendIndices k n hk μ lam)
        (extendIndices k n hk μ ω)) =
    (Nat.factorial k : ℤ) * generalizedKroneckerDelta lam ω :=
  generalizedKroneckerDelta_contraction_fullRank_laplace' k n hk hfull lam ω

end GeneralizedContraction

end Generalized

end KroneckerDelta
