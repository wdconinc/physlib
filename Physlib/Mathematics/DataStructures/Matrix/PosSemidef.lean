/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Linarith

/-!
# Entrywise bounds for real positive-semidefinite matrices

Evaluating the quadratic form of a real positive-semidefinite matrix `M` on the test vector
`e i + ε • e j` gives a nonnegative quadratic polynomial in `ε` for every pair of indices
`i, j`. Specialising `ε` to `0` and to `±1` yields the two entrywise bounds carried by the
principal `2 × 2` minors:

* `Matrix.PosSemidef.apply_self_nonneg`: `0 ≤ M i i`;
* `Matrix.PosSemidef.two_mul_abs_apply_le`: `2 * |M i j| ≤ M i i + M j j`.

The second is the arithmetic-mean form of the Cauchy-Schwarz inequality
`(M i j) ^ 2 ≤ M i i * M j j` for a positive-semidefinite matrix. It is stated multiplied out,
with no division, so that it applies without field side conditions. This is the form in which
positivity constraints are used in hadronic physics; see
`Physlib/Particles/Parton/PDF/Positivity.lean` for the Soffer bound on the quark transversity
distribution, which is exactly this inequality applied to the parton spin-density matrix.

## Main results

- `Matrix.PosSemidef.quadraticForm_nonneg`: the quadratic form written as an iterated sum.
- `Matrix.PosSemidef.quadraticForm_psdTestVector`: nonnegativity on `e i + ε • e j`.
- `Matrix.PosSemidef.apply_self_nonneg`: nonnegativity of the diagonal.
- `Matrix.PosSemidef.two_mul_abs_apply_le`: the entrywise arithmetic-mean bound.

## Implementation notes

Everything here is stated over `ℝ`. `Matrix.PosSemidef` is available over more general
star-ordered rings, and the corresponding statements over `RCLike 𝕜` replace `|·|` by `‖·‖`;
that generalisation is not needed for the leading-twist positivity bounds (whose relevant
block is real) and is left to whoever first needs the T-odd, genuinely complex entries.

These lemmas are stated for a general index type rather than for `Fin n`, and are candidates
for upstreaming to `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.
-/

@[expose] public section

namespace Matrix

open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The test vector `e i + ε • e j`: it takes the value `1` at `i`, the value `ε` at `j`, and
`0` elsewhere. For `i = j` it degenerates to `(1 + ε) • e i`, which is harmless: every lemma
below holds without an `i ≠ j` hypothesis. -/
def psdTestVector {R : Type*} [Semiring R] (i j : n) (ε : R) : n → R :=
  fun k => (if k = i then 1 else 0) + ε * (if k = j then 1 else 0)

/-- Contracting a function `g` against the test vector on the right picks out `g i + ε * g j`. -/
lemma sum_mul_psdTestVector (g : n → ℝ) (i j : n) (ε : ℝ) :
    ∑ l, g l * psdTestVector i j ε l = g i + ε * g j := by
  have hterm : ∀ l : n, g l * psdTestVector i j ε l
      = (if l = i then g l else 0) + (if l = j then ε * g l else 0) := by
    intro l
    simp only [psdTestVector, mul_add]
    by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [h1, h2] <;> ring
  calc ∑ l, g l * psdTestVector i j ε l
      = ∑ l, ((if l = i then g l else 0) + (if l = j then ε * g l else 0)) :=
        Finset.sum_congr rfl fun l _ => hterm l
    _ = (∑ l, if l = i then g l else 0) + ∑ l, if l = j then ε * g l else 0 :=
        Finset.sum_add_distrib
    _ = g i + ε * g j := by simp

/-- Contracting a function `g` against the test vector on the left picks out `g i + ε * g j`. -/
lemma sum_psdTestVector_mul (g : n → ℝ) (i j : n) (ε : ℝ) :
    ∑ l, psdTestVector i j ε l * g l = g i + ε * g j := by
  calc ∑ l, psdTestVector i j ε l * g l = ∑ l, g l * psdTestVector i j ε l :=
        Finset.sum_congr rfl fun l _ => mul_comm _ _
    _ = g i + ε * g j := sum_mul_psdTestVector g i j ε

/-- The quadratic form of a real positive-semidefinite matrix, written as an iterated sum. -/
lemma PosSemidef.quadraticForm_nonneg {M : Matrix n n ℝ} (hM : M.PosSemidef) (w : n → ℝ) :
    0 ≤ ∑ k, w k * ∑ l, M k l * w l := by
  -- `hM.2 w` is `0 ≤ star w ⬝ᵥ (M *ᵥ w)`; over `ℝ` the star is trivial, and `dotProduct`
  -- and `mulVec` unfold to finite sums.
  -- NOTE (build phase): if `Matrix.PosSemidef` at this mathlib pin is still the `RCLike`
  -- version, `hM.2 w` carries an `RCLike.re` around the dot product; the fix is to add the
  -- `ℝ`-valued `RCLike.re` simp lemma to the set below.
  simpa [dotProduct, mulVec, Pi.star_apply, star_trivial] using hM.2 w

/-- Nonnegativity of the quadratic form of a real positive-semidefinite matrix on the test
vector `e i + ε • e j`, expanded as a quadratic polynomial in `ε`. -/
lemma PosSemidef.quadraticForm_psdTestVector {M : Matrix n n ℝ} (hM : M.PosSemidef)
    (i j : n) (ε : ℝ) :
    0 ≤ M i i + ε * (M i j + M j i) + ε ^ 2 * M j j := by
  have h := hM.quadraticForm_nonneg (psdTestVector i j ε)
  have hinner : ∀ k : n, ∑ l, M k l * psdTestVector i j ε l = M k i + ε * M k j :=
    fun k => sum_mul_psdTestVector (fun l => M k l) i j ε
  have hstep : ∑ k, psdTestVector i j ε k * ∑ l, M k l * psdTestVector i j ε l
      = (M i i + ε * M i j) + ε * (M j i + ε * M j j) := by
    calc ∑ k, psdTestVector i j ε k * ∑ l, M k l * psdTestVector i j ε l
        = ∑ k, psdTestVector i j ε k * (M k i + ε * M k j) :=
          Finset.sum_congr rfl fun k _ => by rw [hinner k]
      _ = (M i i + ε * M i j) + ε * (M j i + ε * M j j) :=
          sum_psdTestVector_mul (fun k => M k i + ε * M k j) i j ε
  rw [hstep] at h
  have hring : M i i + ε * (M i j + M j i) + ε ^ 2 * M j j
      = (M i i + ε * M i j) + ε * (M j i + ε * M j j) := by ring
  rw [hring]
  exact h

/-- The diagonal entries of a real positive-semidefinite matrix are nonnegative. -/
lemma PosSemidef.apply_self_nonneg {M : Matrix n n ℝ} (hM : M.PosSemidef) (i : n) :
    0 ≤ M i i := by
  linarith [hM.quadraticForm_psdTestVector i i 0]

/-- **Entrywise arithmetic-mean bound for a real positive-semidefinite matrix.**
Twice the absolute value of an entry is bounded by the sum of the two diagonal entries of its
row and column. Equivalently: the principal `2 × 2` minor on `{i, j}` is nonnegative, in the
arithmetic-mean rather than the geometric-mean form.

Stated multiplied out, without a division, so that it applies with no field side conditions. -/
lemma PosSemidef.two_mul_abs_apply_le {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    2 * |M i j| ≤ M i i + M j j := by
  have hsymm : M j i = M i j := by
    -- `Matrix.IsHermitian.apply` is `star (M j i) = M i j`; over `ℝ` the star is trivial.
    -- NOTE (build phase): if the argument order of `IsHermitian.apply` is the other way
    -- round at this pin, use `hM.1.apply j i`.
    simpa using hM.1.apply i j
  have hplus := hM.quadraticForm_psdTestVector i j 1
  have hminus := hM.quadraticForm_psdTestVector i j (-1)
  rw [hsymm] at hplus hminus
  rcases abs_cases (M i j) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] <;> linarith

end Matrix
