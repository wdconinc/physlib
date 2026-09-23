/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Analysis.Complex.Basic

/-!
# The special unitary Lie algebra

## Provenance

Mirror of the mathlib contribution on branch `m2-lie-classical-su`, commit `346daafa`
(`Mathlib/Algebra/Lie/SpecialUnitary.lean`). Namespaced under `Physlib` to avoid a collision
when that PR lands. When it does: delete this file, drop its import from `Physlib.lean`,
and replace `Physlib.LieAlgebra.SpecialUnitary.su` with `LieAlgebra.SpecialUnitary.su`.

Content is otherwise kept as close to the upstream file as possible so the two stay
diffable; the only edits are the `Physlib` namespace wrapper, the `theorem` -> `lemma`
conversion required by `AGENTS.md`, and the `open` needed to keep upstream names
reachable from inside the wrapper.

This file defines `LieAlgebra.SpecialUnitary.su n`, the Lie algebra `𝔰𝔲(n)` of skew-Hermitian
complex `n × n` matrices of trace zero, as a Lie subalgebra of `Matrix n n ℂ` **over `ℝ`**.

`Mathlib/Algebra/Lie/Classical.lean` already provides `sl`, `so`, `so'` and `sp`; `su` completes
the classical families. Unlike those, `su n` is a real form: if `A` is skew-Hermitian then `I • A`
is Hermitian, so the carrier is not closed under multiplication by `ℂ` and `su n` is only an
`ℝ`-subalgebra of the complex matrix algebra.

## Main definitions

* `LieAlgebra.SpecialUnitary.su`: the special unitary Lie algebra.

## Main statements

* `LieAlgebra.SpecialUnitary.mem_su_iff`: membership unfolds to skew-Hermitian plus traceless.

## Relation to the special unitary group

`Matrix.specialUnitaryGroup` (`Mathlib/LinearAlgebra/UnitaryGroup.lean`) is the *group* `SU(n)`:
unitary matrices of determinant one. `su n` is the corresponding Lie algebra, and the two are
different sets — the identity matrix lies in `SU(n)` but not in `su n`, since its trace is `n`.

The bridge between them is the exponential, and it is *not* proved here. Two things block it, both
worth recording for whoever adds it:

* `Matrix.exp_conjTranspose` and `exp_mem_unitary_of_mem_skewAdjoint` together give the unitary half
  immediately from `mem_skewAdjoint_of_mem_su`, but they need `ContinuousStar (Matrix n n ℂ)`, whose
  instance (`Mathlib/Topology/Instances/Matrix.lean`) is registered for the *Pi* topology;
  choosing a matrix norm in order to have `NormedSpace.exp` installs a different
  `TopologicalSpace` instance and the two do not connect by instance resolution. This is the
  norm-choice friction that `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` documents
  in its own module docstring.
* Even with that resolved, landing in `specialUnitaryGroup n ℂ` rather than `unitaryGroup n ℂ` needs
  `det (exp A) = exp (Matrix.trace A)` to get `det = 1` from `trace = 0`. No such lemma exists in
  mathlib at the time of writing.

Note that mathlib does not currently connect `LieAlgebra.SpecialLinear.sl` to
`Matrix.SpecialLinearGroup` either, so an unconnected definition would have matched precedent; the
bridge below is included because it is cheap and it justifies the name.

## Implementation notes

The physics convention writes generators `T^a` as *Hermitian* matrices with
`⁅T^a, T^b⁆ = i f^{abc} T^c`; the elements of `su n` are the *skew*-Hermitian `i T^a`.

-/

@[expose] public section

open LieAlgebra

namespace Physlib

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : Type*) [DecidableEq n] [Fintype n]

namespace LieAlgebra.SpecialUnitary

/-- The special unitary Lie algebra `𝔰𝔲(n)`: skew-Hermitian complex matrices of trace zero,
as a Lie algebra over `ℝ`. Note this is only an `ℝ`-subalgebra: `i • A` is Hermitian when
`A` is skew-Hermitian, so the set is not closed under multiplication by `ℂ`. -/
def su : LieSubalgebra ℝ (Matrix n n ℂ) where
  carrier := {A | Aᴴ = -A ∧ Matrix.trace A = 0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    rintro A B ⟨hA, hA0⟩ ⟨hB, hB0⟩
    refine ⟨?_, ?_⟩
    · rw [conjTranspose_add, hA, hB, neg_add]
    · rw [trace_add, hA0, hB0, add_zero]
  smul_mem' := by
    rintro (r : ℝ) A ⟨hA, hA0⟩
    refine ⟨?_, ?_⟩
    · rw [conjTranspose_smul, hA]
      simp
    · rw [trace_smul, hA0, smul_zero]
  lie_mem' := by
    rintro A B ⟨hA, _⟩ ⟨hB, _⟩
    refine ⟨?_, ?_⟩
    · show (A * B - B * A)ᴴ = -(A * B - B * A)
      rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hA, hB,
        neg_mul_neg, neg_mul_neg, neg_sub]
    · exact matrix_trace_commutator_zero n ℂ A B

variable {n}

lemma mem_su_iff (A : Matrix n n ℂ) : A ∈ su n ↔ Aᴴ = -A ∧ Matrix.trace A = 0 := Iff.rfl

lemma conjTranspose_of_mem {A : Matrix n n ℂ} (h : A ∈ su n) : Aᴴ = -A := h.1

lemma trace_of_mem {A : Matrix n n ℂ} (h : A ∈ su n) : Matrix.trace A = 0 := h.2

lemma mem_skewAdjoint_of_mem_su {A : Matrix n n ℂ} (h : A ∈ su n) :
    A ∈ skewAdjoint (Matrix n n ℂ) := h.1

end LieAlgebra.SpecialUnitary

end Physlib
