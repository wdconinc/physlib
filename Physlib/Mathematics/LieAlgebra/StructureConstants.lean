/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Structure constants of a Lie algebra

## Provenance

Mirror of the mathlib contribution on branch `m3-lie-structure-constants`, commit `e14396d8`
(`Mathlib/Algebra/Lie/StructureConstants.lean`). Namespaced under `Physlib` to avoid a collision
when that PR lands. When it does: delete this file, drop its import from `Physlib.lean`,
and replace `Physlib.LieAlgebra.structureConstants` with `LieAlgebra.structureConstants`.

Content is otherwise kept as close to the upstream file as possible so the two stay
diffable; the only edits are the `Physlib` namespace wrapper, the `theorem` -> `lemma`
conversion required by `AGENTS.md`, and the `open` needed to keep upstream names
reachable from inside the wrapper.

Let `L` be a Lie algebra over a commutative ring `R` and let `b : Basis ι R L` be a basis of `L`
as an `R`-module. Since the Lie bracket is `R`-bilinear it is determined by its values on pairs of
basis vectors, and those values are in turn determined by their coordinates with respect to `b`.
The resulting family of scalars `f i j k` is the family of *structure constants* of `L` relative
to `b`; it satisfies `⁅b i, b j⁆ = ∑ k, f i j k • b k`.

The defining properties of a Lie bracket translate into properties of the structure constants:
alternativity gives `f i i k = 0` and hence antisymmetry `f j i k = -f i j k`, while the Jacobi
identity gives the quadratic relation `LieAlgebra.sum_structureConstants_cyclic_eq_zero`.

Note that `Mathlib/Algebra/Lie/Basis/Basic.lean` defines a different notion, `LieAlgebra.Basis`,
which is a root-theoretic (Chevalley–Serre) datum rather than a plain module basis. The structure
constants defined here are relative to a plain `Module.Basis`.

## Main definitions

* `LieAlgebra.structureConstants`: the structure constants of a Lie algebra relative to a basis.

## Main statements

* `LieAlgebra.lie_basis_eq_sum`: the brackets of basis vectors are recovered from the structure
  constants.
* `LieAlgebra.structureConstants_self`: the structure constants vanish when their first two
  indices agree.
* `LieAlgebra.structureConstants_swap`: the structure constants are antisymmetric in their first
  two indices.
* `LieAlgebra.repr_lie_eq_sum`: the coordinates of `⁅x, b j⁆` in terms of those of `x`.
* `LieAlgebra.sum_structureConstants_cyclic_eq_zero`: the quadratic relation among the structure
  constants coming from the Jacobi identity.

-/

@[expose] public section

namespace Physlib

open Module

namespace LieAlgebra

variable {ι R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The structure constants of a Lie algebra `L` relative to a basis `b` of `L` as a module:
`structureConstants b i j k` is the `k`-th coordinate of `⁅b i, b j⁆` with respect to `b`. -/
noncomputable def structureConstants (b : Basis ι R L) (i j k : ι) : R := b.repr ⁅b i, b j⁆ k

variable (b : Basis ι R L)

/-- The structure constants are the coordinate functionals of the brackets of basis vectors. -/
@[simp]
lemma coord_lie_basis (i j k : ι) : b.coord k ⁅b i, b j⁆ = structureConstants b i j k := by
  simp [structureConstants]

/-- The structure constants vanish when their first two indices agree, since `⁅x, x⁆ = 0`. -/
@[simp]
lemma structureConstants_self (i k : ι) : structureConstants b i i k = 0 := by
  simp [structureConstants]

/-- The structure constants are antisymmetric in their first two indices. -/
lemma structureConstants_swap (i j k : ι) :
    structureConstants b j i k = -structureConstants b i j k := by
  have h : ⁅b j, b i⁆ = -⁅b i, b j⁆ := by rw [← lie_skew]
  rw [← coord_lie_basis b j i k, ← coord_lie_basis b i j k, h, map_neg]

/-- The Jacobi identity, written with all brackets nested to the left. This is the form in which
the identity yields the quadratic relation among the structure constants. -/
lemma lie_jacobi' (x y z : L) : ⁅⁅x, y⁆, z⁆ + ⁅⁅y, z⁆, x⁆ + ⁅⁅z, x⁆, y⁆ = 0 := by
  have h1 : ⁅⁅x, y⁆, z⁆ = -⁅z, ⁅x, y⁆⁆ := by rw [← lie_skew]
  have h2 : ⁅⁅y, z⁆, x⁆ = -⁅x, ⁅y, z⁆⁆ := by rw [← lie_skew]
  have h3 : ⁅⁅z, x⁆, y⁆ = -⁅y, ⁅z, x⁆⁆ := by rw [← lie_skew]
  rw [h1, h2, h3, show -⁅z, ⁅x, y⁆⁆ + -⁅x, ⁅y, z⁆⁆ + -⁅y, ⁅z, x⁆⁆ =
    -(⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆) from by abel, lie_jacobi, neg_zero]

section Fintype

variable [Fintype ι]

/-- The bracket of two basis vectors, recovered from the structure constants. -/
lemma lie_basis_eq_sum (i j : ι) : ⁅b i, b j⁆ = ∑ k, structureConstants b i j k • b k :=
  (b.sum_repr ⁅b i, b j⁆).symm

/-- The coordinates of `⁅x, b j⁆`, expressed via the coordinates of `x` and the structure
constants. Stated using `Module.Basis.coord`; see `LieAlgebra.repr_lie_eq_sum` for the same
statement in terms of `Module.Basis.repr`. -/
lemma coord_lie_eq_sum (x : L) (j k : ι) :
    b.coord k ⁅x, b j⁆ = ∑ i, b.coord i x * structureConstants b i j k := by
  conv_lhs => rw [← b.sum_repr x]
  rw [sum_lie, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_lie, map_smul, smul_eq_mul, coord_lie_basis, Basis.coord_apply]

/-- The coordinates of `⁅x, b j⁆`, expressed via the coordinates of `x` and the structure
constants. -/
lemma repr_lie_eq_sum (x : L) (j k : ι) :
    b.repr ⁅x, b j⁆ k = ∑ i, b.repr x i * structureConstants b i j k := by
  simpa using coord_lie_eq_sum b x j k

/-- The coordinates of a left-nested double bracket of basis vectors, as a contraction of two
structure constants. -/
lemma coord_lie_lie_basis (i j k l : ι) :
    b.coord l ⁅⁅b i, b j⁆, b k⁆ =
      ∑ d, structureConstants b i j d * structureConstants b d k l := by
  rw [coord_lie_eq_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [coord_lie_basis]

/-- The quadratic relation among the structure constants of a Lie algebra, expressing the Jacobi
identity. -/
lemma sum_structureConstants_cyclic_eq_zero (i j k l : ι) :
    ∑ d, (structureConstants b i j d * structureConstants b d k l +
      structureConstants b j k d * structureConstants b d i l +
      structureConstants b k i d * structureConstants b d j l) = 0 := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← coord_lie_lie_basis b i j k l,
    ← coord_lie_lie_basis b j k i l, ← coord_lie_lie_basis b k i j l, ← map_add, ← map_add,
    lie_jacobi', map_zero]

end Fintype

end LieAlgebra

end Physlib
