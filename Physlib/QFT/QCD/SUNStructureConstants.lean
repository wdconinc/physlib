/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.SUNGenerators
/-!

# Structure constants and the adjoint Casimir for `su(N)`

`Physlib.QFT.QCD.SUNGenerators` builds the generalized Gell-Mann basis `Tᵃ` of `su(N)`
for every `N` and proves the trace identity `Tr(TᵃTᵇ) = δᵃᵇ/2`, the completeness (Fierz)
relation and the fundamental Casimir `C_F = (N²-1)/(2N)`.  What it does not have is the
structure constants: `su(2)` and `su(3)` carry them as finite tables, and no table
generalizes.

This module supplies them through the trace, following the convention recorded in
`RepresentationColor.NormalizedGeneratorData`: for a compact real form with Hermitian
generators normalized by `Tr(TᵃTᵇ) = T_F δᵃᵇ`,

```
f^{abc} = -(i / T_F) · Tr([Tᵃ, Tᵇ] Tᶜ) = -2i · Tr([Tᵃ, Tᵇ] Tᶜ)   at   T_F = 1/2,
```

which is well posed precisely because the trace identity is proved.  It is real because
the generators are Hermitian (`SUNGen.conj_suNGenEntry`), and with it the last of the
three colour invariants follows:

`suNAdjointStatement` — `Σ_{cd} f^{acd} f^{bcd} = N δᵃᵇ`, i.e. `C_A = N`, for every `N`.

## The derivation

Everything rests on two matrix forms of the completeness relation, both obtained from
`SUNGen.suN_completeness` by contracting the free indices against an arbitrary matrix
`X`:

* `sum_genM_sandwich` — `Σₐ Tᵃ X Tᵃ = (1/2)(Tr(X) · 1 - X/N)`;
* `sum_genM_proj` — `Σₐ Tr(X Tᵃ) Tᵃ = (1/2)(X - Tr(X)/N · 1)`.

From the second, `Σₐ Tr(X Tᵃ) Tr(Y Tᵃ) = (1/2)(Tr(YX) - Tr(X)Tr(Y)/N)` (`sum_trace_pair`),
which collapses the `d` sum: since the trace of a commutator vanishes, the `1/N` term
drops and

```
Σ_d f^{acd} f^{bcd} = (-2i)² · (1/2) · Tr([Tᵃ,Tᶜ][Tᵇ,Tᶜ]) = -2 Tr([Tᵃ,Tᶜ][Tᵇ,Tᶜ]).
```

Expanding the commutators and using cyclicity of the trace leaves only two distinct
sums over `c`, and the first matrix form evaluates both:

```
Σ_c Tr(Tᵃ Tᶜ Tᵇ Tᶜ) = -δᵃᵇ / (4N),        Σ_c Tr(Tᵃ Tᶜ Tᶜ Tᵇ) = ((N²-1)/(4N)) δᵃᵇ,
```

the first because `Tᵇ` is traceless (`SUNGen.sum_suNGenEntry_diag`), the second because
`Σ_c TᶜTᶜ` is the fundamental Casimir.  Together

```
Σ_c Tr([Tᵃ,Tᶜ][Tᵇ,Tᶜ]) = -(N/2) δᵃᵇ,   hence   Σ_{cd} f^{acd} f^{bcd} = N δᵃᵇ.
```

Working with `Matrix (Fin N) (Fin N) ℂ` rather than with entry sums is what makes the
middle of this argument short: associativity, distributivity over the commutators and
`Matrix.trace_mul_comm` do the bookkeeping that would otherwise be four nested
`Finset.sum` reorderings per term.  Only the two completeness contractions are done in
entries, where `SUNGen.suN_completeness` lives.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace RepresentationColor

namespace SUNGen

open Complex Matrix

variable {N : ℕ}

/-! ### The generators as matrices -/

/-- The generalized Gell-Mann generators of `su(N)` packaged as matrices.  The entry map
`suNGenEntry` is the primitive notion — it is what the `NormalizedGeneratorData`
contracts are stated in — but the adjoint Casimir is an identity about products of four
generators, and the matrix algebra supplies associativity and cyclicity for free. -/
def genM (N : ℕ) (a : SUNIndex N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => suNGenEntry N a i j

lemma genM_apply (a : SUNIndex N) (i j : Fin N) : genM N a i j = suNGenEntry N a i j := rfl

/-- The trace as a sum of diagonal entries, in the form used throughout this module. -/
lemma trace_eq_sum (M : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.trace M = ∑ i : Fin N, M i i := rfl

/-- Kronecker delta on the adjoint index set of `su(N)`, complex valued. -/
def kdA (a b : SUNIndex N) : ℂ := if a = b then 1 else 0

lemma kdA_eq_deltaAdj (a b : SUNIndex N) : ((suNDeltaAdj a b : ℝ) : ℂ) = kdA a b := by
  simp only [suNDeltaAdj, kdA]
  split_ifs <;> simp

lemma one_apply_kd (i j : Fin N) : (1 : Matrix (Fin N) (Fin N) ℂ) i j = kd i j := by
  simp only [Matrix.one_apply, kd]

/-! ### Sum-manipulation helpers

The two contractions of the completeness relation below are both of the shape "sum over
the adjoint index of a double sum over fundamental indices"; these three lemmas are the
reorderings they need. -/

/-- Moving a sum over the adjoint index past a double sum over fundamental indices. -/
lemma sum_swap_adj {α : Type*} [Fintype α] (g : α → Fin N → Fin N → ℂ) :
    (∑ a : α, ∑ j : Fin N, ∑ k : Fin N, g a j k)
      = ∑ j : Fin N, ∑ k : Fin N, ∑ a : α, g a j k := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Pulling a scalar out of a double sum. -/
lemma mul_sum₂ (c : ℂ) (h : Fin N → Fin N → ℂ) :
    (∑ j : Fin N, ∑ k : Fin N, c * h j k) = c * ∑ j : Fin N, ∑ k : Fin N, h j k := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm

/-- Splitting a double sum of a difference. -/
lemma sum_sub₂ (f g : Fin N → Fin N → ℂ) :
    (∑ j : Fin N, ∑ k : Fin N, (f j k - g j k))
      = (∑ j : Fin N, ∑ k : Fin N, f j k) - ∑ j : Fin N, ∑ k : Fin N, g j k := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_sub_distrib

/-- Contracting a matrix against two Kronecker deltas on opposite sides. -/
lemma sum_kd_sandwich (X : Fin N → Fin N → ℂ) (i l : Fin N) :
    (∑ j : Fin N, ∑ k : Fin N, X j k * (kd i j * kd k l)) = X i l := by
  have h1 : ∀ j : Fin N, (∑ k : Fin N, X j k * (kd i j * kd k l)) = kd j i * X j l := by
    intro j
    have h2 : ∀ k : Fin N, X j k * (kd i j * kd k l) = kd i j * (kd k l * X j k) := by
      intro k; ring
    rw [Finset.sum_congr rfl fun k _ => h2 k, ← Finset.mul_sum,
      kd_sum (fun k => X j k) l, kd_comm i j]
  rw [Finset.sum_congr rfl fun j _ => h1 j, kd_sum (fun j => X j l) i]

/-- Contracting a matrix against a Kronecker delta on both indices gives its trace. -/
lemma sum_kd_trace (X : Fin N → Fin N → ℂ) :
    (∑ j : Fin N, ∑ k : Fin N, X j k * kd j k) = ∑ j : Fin N, X j j := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ∀ k : Fin N, X j k * kd j k = kd k j * X j k := by
    intro k; rw [kd_comm j k]; ring
  rw [Finset.sum_congr rfl fun k _ => h k, kd_sum (fun k => X j k) j]

/-! ### Traces of the generators -/

/-- The `su(N)` generators are traceless; the matrix form of
`SUNGen.sum_suNGenEntry_diag`. -/
lemma trace_genM (a : SUNIndex N) : Matrix.trace (genM N a) = 0 :=
  sum_suNGenEntry_diag a

/-- The trace identity `Tr(TᵃTᵇ) = δᵃᵇ/2` in matrix form. -/
lemma trace_genM_mul (a b : SUNIndex N) :
    Matrix.trace (genM N a * genM N b) = (1 / 2 : ℂ) * kdA a b := by
  have h : Matrix.trace (genM N a * genM N b)
      = ∑ i : Fin N, ∑ l : Fin N, suNGenEntry N a i l * suNGenEntry N b l i := by
    rw [trace_eq_sum]
    exact Finset.sum_congr rfl fun _ _ => Matrix.mul_apply
  rw [h, suNTraceStatement N a b, kdA_eq_deltaAdj]
  norm_num

/-- The `su(N)` generators are Hermitian; the matrix form of
`SUNGen.conj_suNGenEntry`. -/
lemma genM_conjTranspose (a : SUNIndex N) : (genM N a)ᴴ = genM N a := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  simpa only [Complex.star_def, genM_apply] using conj_suNGenEntry a j i

/-! ### The two matrix forms of completeness -/

/-- **Completeness, sandwich form**, entrywise: `Σₐ (Tᵃ X Tᵃ)_{il} = (1/2)(Tr(X) δ_{il} -
X_{il}/N)`.  This is `SUNGen.suN_completeness` with both free index pairs contracted
against `X`. -/
lemma sum_genM_sandwich_apply (X : Matrix (Fin N) (Fin N) ℂ) (i l : Fin N) :
    (∑ a : SUNIndex N, (genM N a * X * genM N a) i l)
      = (1 / 2 : ℂ) * (Matrix.trace X * kd i l - ((N : ℂ))⁻¹ * X i l) := by
  rw [trace_eq_sum X]
  have hterm : ∀ a : SUNIndex N, (genM N a * X * genM N a) i l
      = ∑ j : Fin N, ∑ k : Fin N,
          (suNGenEntry N a i j * suNGenEntry N a k l) * X j k := by
    intro a
    rw [Matrix.mul_apply]
    have h1 : ∀ k : Fin N, (genM N a * X) i k * genM N a k l
        = ∑ j : Fin N, (suNGenEntry N a i j * suNGenEntry N a k l) * X j k := by
      intro k
      rw [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [genM_apply, genM_apply]; ring
    rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun a _ => hterm a, sum_swap_adj]
  have h2 : ∀ j k : Fin N,
      (∑ a : SUNIndex N, (suNGenEntry N a i j * suNGenEntry N a k l) * X j k)
        = ((1 / 2 : ℂ) * (kd i l * kd j k - ((N : ℂ))⁻¹ * (kd i j * kd k l))) * X j k := by
    intro j k
    rw [← Finset.sum_mul, suN_completeness]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => h2 j k]
  have h3 : ∀ j k : Fin N,
      ((1 / 2 : ℂ) * (kd i l * kd j k - ((N : ℂ))⁻¹ * (kd i j * kd k l))) * X j k
        = (1 / 2 : ℂ) * kd i l * (X j k * kd j k)
          - (1 / 2 : ℂ) * ((N : ℂ))⁻¹ * (X j k * (kd i j * kd k l)) := by
    intro j k; ring
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => h3 j k,
    sum_sub₂, mul_sum₂, mul_sum₂, sum_kd_trace, sum_kd_sandwich]
  ring

/-- **Completeness, projection form**, entrywise:
`Σₐ Tr(X Tᵃ) (Tᵃ)_{il} = (1/2)(X_{il} - Tr(X) δ_{il}/N)`.  Equivalently, `X ↦ Σₐ Tr(X Tᵃ)
Tᵃ` is half the projection of `X` onto the traceless part. -/
lemma sum_genM_proj_apply (X : Matrix (Fin N) (Fin N) ℂ) (i l : Fin N) :
    (∑ a : SUNIndex N, Matrix.trace (X * genM N a) * genM N a i l)
      = (1 / 2 : ℂ) * (X i l - ((N : ℂ))⁻¹ * Matrix.trace X * kd i l) := by
  rw [trace_eq_sum X]
  have hterm : ∀ a : SUNIndex N, Matrix.trace (X * genM N a) * genM N a i l
      = ∑ j : Fin N, ∑ k : Fin N,
          (suNGenEntry N a k j * suNGenEntry N a i l) * X j k := by
    intro a
    rw [trace_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [genM_apply, genM_apply]; ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, sum_swap_adj]
  have h2 : ∀ j k : Fin N,
      (∑ a : SUNIndex N, (suNGenEntry N a k j * suNGenEntry N a i l) * X j k)
        = ((1 / 2 : ℂ) * (kd k l * kd j i - ((N : ℂ))⁻¹ * (kd k j * kd i l))) * X j k := by
    intro j k
    rw [← Finset.sum_mul, suN_completeness]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => h2 j k]
  have h3 : ∀ j k : Fin N,
      ((1 / 2 : ℂ) * (kd k l * kd j i - ((N : ℂ))⁻¹ * (kd k j * kd i l))) * X j k
        = (1 / 2 : ℂ) * (X j k * (kd i j * kd k l))
          - (1 / 2 : ℂ) * (((N : ℂ))⁻¹ * kd i l) * (X j k * kd j k) := by
    intro j k
    rw [kd_comm j i, kd_comm k j]
    ring
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => h3 j k,
    sum_sub₂, mul_sum₂, mul_sum₂, sum_kd_sandwich, sum_kd_trace]
  ring

/-- **Completeness, sandwich form** as a matrix identity: `Σₐ Tᵃ X Tᵃ = (1/2)(Tr(X) · 1 -
X/N)`. -/
lemma sum_genM_sandwich (X : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : SUNIndex N, genM N a * X * genM N a)
      = (1 / 2 : ℂ) • (Matrix.trace X • (1 : Matrix (Fin N) (Fin N) ℂ)
          - ((N : ℂ))⁻¹ • X) := by
  ext i l
  rw [Matrix.sum_apply, sum_genM_sandwich_apply]
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, one_apply_kd]

/-- `Σ_c Tᶜ Tᵇ Tᶜ = -Tᵇ/(2N)`: the sandwich at a traceless matrix.  This is the step that
uses tracelessness of the individual generators. -/
lemma sum_genM_sandwich_gen (b : SUNIndex N) :
    (∑ c : SUNIndex N, genM N c * genM N b * genM N c)
      = (-((2 : ℂ)⁻¹ * ((N : ℂ))⁻¹)) • genM N b := by
  ext i l
  rw [Matrix.sum_apply, sum_genM_sandwich_apply, trace_genM, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- `Σ_c Tᶜ Tᶜ = C_F · 1` with `C_F = (N²-1)/(2N)`: the sandwich at `X = 1`.  This is the
fundamental Casimir again, obtained here from the matrix form so that the adjoint
computation needs only one primitive. -/
lemma sum_genM_sq :
    (∑ c : SUNIndex N, genM N c * genM N c)
      = ((2 : ℂ)⁻¹ * ((N : ℂ) - ((N : ℂ))⁻¹)) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  ext i l
  rw [Matrix.sum_apply]
  have h : ∀ c : SUNIndex N, (genM N c * genM N c) i l = (genM N c * 1 * genM N c) i l := by
    intro c; rw [mul_one]
  rw [Finset.sum_congr rfl fun c _ => h c, sum_genM_sandwich_apply, Matrix.trace_one,
    Matrix.smul_apply, smul_eq_mul, Fintype.card_fin]
  simp only [one_apply_kd]
  ring

/-- `Σₐ Tr(X Tᵃ) Tr(Y Tᵃ) = (1/2)(Tr(YX) - Tr(X)Tr(Y)/N)`: the projection form paired
against a second matrix.  This is the contraction that collapses the `d` sum in the
adjoint Casimir. -/
lemma sum_trace_pair (X Y : Matrix (Fin N) (Fin N) ℂ) :
    (∑ a : SUNIndex N, Matrix.trace (X * genM N a) * Matrix.trace (Y * genM N a))
      = (1 / 2 : ℂ) * (Matrix.trace (Y * X)
          - ((N : ℂ))⁻¹ * (Matrix.trace X * Matrix.trace Y)) := by
  have hterm : ∀ a : SUNIndex N,
      Matrix.trace (X * genM N a) * Matrix.trace (Y * genM N a)
        = ∑ i : Fin N, ∑ l : Fin N,
            (Matrix.trace (X * genM N a) * genM N a l i) * Y i l := by
    intro a
    rw [trace_eq_sum (Y * genM N a), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, sum_swap_adj]
  have h2 : ∀ i l : Fin N,
      (∑ a : SUNIndex N, (Matrix.trace (X * genM N a) * genM N a l i) * Y i l)
        = ((1 / 2 : ℂ) * (X l i - ((N : ℂ))⁻¹ * Matrix.trace X * kd l i)) * Y i l := by
    intro i l
    rw [← Finset.sum_mul, sum_genM_proj_apply]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => h2 i l]
  have h3 : ∀ i l : Fin N,
      ((1 / 2 : ℂ) * (X l i - ((N : ℂ))⁻¹ * Matrix.trace X * kd l i)) * Y i l
        = (1 / 2 : ℂ) * (Y i l * X l i)
          - (1 / 2 : ℂ) * (((N : ℂ))⁻¹ * Matrix.trace X) * (Y i l * kd i l) := by
    intro i l
    rw [kd_comm l i]
    ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => h3 i l,
    sum_sub₂, mul_sum₂, mul_sum₂, sum_kd_trace]
  have h4 : Matrix.trace (Y * X) = ∑ i : Fin N, ∑ l : Fin N, Y i l * X l i := by
    rw [trace_eq_sum]
    exact Finset.sum_congr rfl fun _ _ => Matrix.mul_apply
  rw [h4, ← trace_eq_sum Y]
  ring

/-! ### The structure constants -/

/-- The commutator `[Tᵃ, Tᵇ]` of two `su(N)` generators. -/
def genCommM (N : ℕ) (a b : SUNIndex N) : Matrix (Fin N) (Fin N) ℂ :=
  genM N a * genM N b - genM N b * genM N a

/-- The trace of a commutator vanishes. -/
lemma trace_genCommM (a b : SUNIndex N) : Matrix.trace (genCommM N a b) = 0 := by
  simp only [genCommM]
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- `Tr([Tᵃ,Tᵇ]Tᶜ)` is purely imaginary: `[Tᵃ,Tᵇ]` is anti-Hermitian and `Tᶜ` is
Hermitian, so the product's trace is reversed by conjugation. -/
lemma trace_genCommM_mul_re (a b c : SUNIndex N) :
    (Matrix.trace (genCommM N a b * genM N c)).re = 0 := by
  have hK : (genCommM N a b)ᴴ = -genCommM N a b := by
    simp only [genCommM, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      genM_conjTranspose]
    ring
  have h1 : (genCommM N a b * genM N c)ᴴ = -(genM N c * genCommM N a b) := by
    rw [Matrix.conjTranspose_mul, genM_conjTranspose, hK, mul_neg]
  have h2 : star (Matrix.trace (genCommM N a b * genM N c))
      = -Matrix.trace (genCommM N a b * genM N c) := by
    rw [← Matrix.trace_conjTranspose, h1, Matrix.trace_neg,
      Matrix.trace_mul_comm (genM N c) (genCommM N a b)]
  have h3 := congrArg Complex.re h2
  rw [Complex.star_def, Complex.conj_re, Complex.neg_re] at h3
  linarith

/-- The `su(N)` structure constants in complex form, `f^{abc} = -2i Tr([Tᵃ,Tᵇ]Tᶜ)`.  The
normalization is the one recorded in `NormalizedGeneratorData`, `-(i/T_F)` at
`T_F = 1/2`; for `N = 3` it reproduces `structConst3`, e.g.
`f^{123} = -2i Tr([T¹,T²]T³) = -2i · (i/2) = 1`. -/
def suNStructConstC (N : ℕ) (a b c : SUNIndex N) : ℂ :=
  -2 * I * Matrix.trace (genCommM N a b * genM N c)

/-- The `su(N)` structure constants, real valued.  Reality is
`trace_genCommM_mul_re`; see `suNStructConst_coe`. -/
def suNStructConst (N : ℕ) (a b c : SUNIndex N) : ℝ :=
  2 * (Matrix.trace (genCommM N a b * genM N c)).im

/-- The real structure constants are the complex ones. -/
lemma suNStructConst_coe (a b c : SUNIndex N) :
    ((suNStructConst N a b c : ℝ) : ℂ) = suNStructConstC N a b c := by
  have hre := trace_genCommM_mul_re a b c
  have hz : Matrix.trace (genCommM N a b * genM N c)
      = (((Matrix.trace (genCommM N a b * genM N c)).im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  rw [suNStructConstC, suNStructConst, hz]
  push_cast
  linear_combination
    (2 * ((Matrix.trace (genCommM N a b * genM N c)).im : ℂ)) * Complex.I_sq

/-! ### The adjoint Casimir -/

/-- **Step B**: the `d` sum collapses.  `Σ_d f^{acd} f^{bcd} = -2 Tr([Tᵃ,Tᶜ][Tᵇ,Tᶜ])`;
the `1/N` term of `sum_trace_pair` drops because the trace of a commutator vanishes. -/
lemma sum_d_structConstC (a b c : SUNIndex N) :
    (∑ d : SUNIndex N, suNStructConstC N a c d * suNStructConstC N b c d)
      = -2 * Matrix.trace (genCommM N a c * genCommM N b c) := by
  have hterm : ∀ d : SUNIndex N, suNStructConstC N a c d * suNStructConstC N b c d
      = (-2 * I) * (-2 * I) * (Matrix.trace (genCommM N a c * genM N d)
          * Matrix.trace (genCommM N b c * genM N d)) := by
    intro d
    simp only [suNStructConstC]
    ring
  rw [Finset.sum_congr rfl fun d _ => hterm d, ← Finset.mul_sum, sum_trace_pair,
    trace_genCommM, trace_genCommM,
    Matrix.trace_mul_comm (genCommM N b c) (genCommM N a c)]
  linear_combination
    (2 * Matrix.trace (genCommM N a c * genCommM N b c)) * Complex.I_sq

/-- Expanding a product of two commutators sharing a generator.  Cyclicity of the trace
identifies the first and fourth terms, leaving three. -/
lemma trace_genCommM_mul_genCommM (a b c : SUNIndex N) :
    Matrix.trace (genCommM N a c * genCommM N b c)
      = 2 * Matrix.trace (genM N a * (genM N c * genM N b * genM N c))
        - Matrix.trace (genM N a * (genM N c * genM N c) * genM N b)
        - Matrix.trace (genM N a * genM N b * (genM N c * genM N c)) := by
  have e1 : Matrix.trace (genM N a * genM N c * (genM N b * genM N c))
      = Matrix.trace (genM N a * (genM N c * genM N b * genM N c)) := by
    congr 1
    simp only [mul_assoc]
  have e2 : Matrix.trace (genM N a * genM N c * (genM N c * genM N b))
      = Matrix.trace (genM N a * (genM N c * genM N c) * genM N b) := by
    congr 1
    simp only [mul_assoc]
  have e3 : Matrix.trace (genM N c * genM N a * (genM N b * genM N c))
      = Matrix.trace (genM N a * genM N b * (genM N c * genM N c)) := by
    have h : genM N c * genM N a * (genM N b * genM N c)
        = genM N c * (genM N a * genM N b * genM N c) := by
      simp only [mul_assoc]
    rw [h, Matrix.trace_mul_comm]
    congr 1
    simp only [mul_assoc]
  have e4 : Matrix.trace (genM N c * genM N a * (genM N c * genM N b))
      = Matrix.trace (genM N a * (genM N c * genM N b * genM N c)) := by
    have h : genM N c * genM N a * (genM N c * genM N b)
        = genM N c * (genM N a * (genM N c * genM N b)) := by
      simp only [mul_assoc]
    rw [h, Matrix.trace_mul_comm]
    congr 1
    simp only [mul_assoc]
  simp only [genCommM, sub_mul, mul_sub, Matrix.trace_sub]
  rw [e1, e2, e3, e4]
  ring

/-- **Steps C and D**: `Σ_c Tr([Tᵃ,Tᶜ][Tᵇ,Tᶜ]) = -(N/2) δᵃᵇ`.  The three surviving sums
are evaluated by the two matrix forms of completeness: the first by
`sum_genM_sandwich_gen` (which contributes `-δᵃᵇ/(4N)` because the generators are
traceless), the other two by `sum_genM_sq` (each contributing `C_F δᵃᵇ/2`).  The `1/N`
pieces cancel and `-2 C_F · (1/2) = -N/2 + 1/(2N)` supplies the rest. -/
lemma sum_c_trace_genCommM (a b : SUNIndex N) :
    (∑ c : SUNIndex N, Matrix.trace (genCommM N a c * genCommM N b c))
      = -((N : ℂ) / 2) * kdA a b := by
  have hs1 : (∑ c : SUNIndex N,
      Matrix.trace (genM N a * (genM N c * genM N b * genM N c)))
      = (-((2 : ℂ)⁻¹ * ((N : ℂ))⁻¹)) * ((1 / 2 : ℂ) * kdA a b) := by
    rw [← Matrix.trace_sum, ← Finset.mul_sum, sum_genM_sandwich_gen, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul, trace_genM_mul]
  have hs2 : (∑ c : SUNIndex N,
      Matrix.trace (genM N a * (genM N c * genM N c) * genM N b))
      = ((2 : ℂ)⁻¹ * ((N : ℂ) - ((N : ℂ))⁻¹)) * ((1 / 2 : ℂ) * kdA a b) := by
    rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, sum_genM_sq,
      Matrix.mul_smul, mul_one, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      trace_genM_mul]
  have hs3 : (∑ c : SUNIndex N,
      Matrix.trace (genM N a * genM N b * (genM N c * genM N c)))
      = ((2 : ℂ)⁻¹ * ((N : ℂ) - ((N : ℂ))⁻¹)) * ((1 / 2 : ℂ) * kdA a b) := by
    rw [← Matrix.trace_sum, ← Finset.mul_sum, sum_genM_sq, Matrix.mul_smul, mul_one,
      Matrix.trace_smul, smul_eq_mul, trace_genM_mul]
  rw [Finset.sum_congr rfl fun c _ => trace_genCommM_mul_genCommM a b c,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs1, hs2, hs3]
  ring

/-- The adjoint Casimir identity for `su(N)` in complex form:
`Σ_{cd} f^{acd} f^{bcd} = N δᵃᵇ`. -/
lemma sum_cd_structConstC (a b : SUNIndex N) :
    (∑ c : SUNIndex N, ∑ d : SUNIndex N,
        suNStructConstC N a c d * suNStructConstC N b c d)
      = (N : ℂ) * kdA a b := by
  rw [Finset.sum_congr rfl fun c _ => sum_d_structConstC a b c, ← Finset.mul_sum,
    sum_c_trace_genCommM]
  ring

/-- Adjoint Casimir for `su(N)`: `Σ_{cd} f^{acd} f^{bcd} = N δᵃᵇ`, so `C_A = N`.  An
identity in `ℝ`, matching `NormalizedGeneratorData.AdjointCasimirIdentity`. -/
def SUNAdjointStatement (N : ℕ) : Prop :=
  ∀ a b : SUNIndex N,
    (∑ c : SUNIndex N, ∑ d : SUNIndex N,
        suNStructConst N a c d * suNStructConst N b c d)
      = (N : ℝ) * suNDeltaAdj a b

/-- The generalized Gell-Mann structure constants of `su(N)` satisfy the adjoint Casimir
identity with `C_A = N`, for every `N`. -/
lemma suNAdjointStatement (N : ℕ) : SUNAdjointStatement N := by
  intro a b
  apply Complex.ofReal_injective
  push_cast
  rw [kdA_eq_deltaAdj, ← sum_cd_structConstC a b]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
    rw [suNStructConst_coe, suNStructConst_coe]

end SUNGen

end RepresentationColor
end QCD
end QFT
end Physlib
