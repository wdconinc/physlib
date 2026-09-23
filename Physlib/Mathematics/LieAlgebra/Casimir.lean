/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Lie.TraceForm
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# The quadratic Casimir element of a Lie module

## Provenance

Mirror of the mathlib contribution on branch `m4-lie-casimir`, commit `d9bb1cc5`
(`Mathlib/Algebra/Lie/Casimir.lean`). Namespaced under `Physlib` to avoid a collision
when that PR lands. When it does: delete this file, drop its import from `Physlib.lean`,
and replace `Physlib.LieModule.casimir` with `LieModule.casimir`.

Content is otherwise kept as close to the upstream file as possible so the two stay
diffable; the only edits are the `Physlib` namespace wrapper, the `theorem` -> `lemma`
conversion required by `AGENTS.md`, and the `open` needed to keep upstream names
reachable from inside the wrapper.

Let `L` be a Lie algebra with coefficients in a commutative ring `R` and let `M` be a
representation of `L`, with associated morphism `φ = LieModule.toEnd R L M`. Given a finite
family `b` of elements of `L` together with a family `b'` dual to it with respect to an
invariant bilinear form `B` on `L`, the *quadratic Casimir element* of `M` is the endomorphism

`Ω = ∑ i, φ (b i) ∘ₗ φ (b' i) : M →ₗ[R] M`.

Its defining property is that it is central: it commutes with the action of every element of `L`.
When `M` is irreducible this forces `Ω` to be a scalar, the *Casimir eigenvalue* of `M`.

Taking traces recovers the trace form: `Tr Ω = ∑ i, traceForm R L M (b i) (b' i)`, and in the
adjoint case `M = L` this is `∑ i, killingForm R L (b i) (b' i)`. In this sense the Casimir
element is the operator of which `killingForm` is the adjoint-representation trace.

## Main definitions

* `LieModule.casimir`: the quadratic Casimir endomorphism `∑ i, φ (b i) ∘ₗ φ (b' i)` attached to a
  pair of finite families `b`, `b'` of elements of `L`.
* `LieModule.casimirOfBasis`: the quadratic Casimir attached to a single basis `b`, i.e. the case
  `b' = b`. This is the usual expression `∑ a, T a * T a`; see the implementation notes for the
  hypothesis under which it is the correct object.
* `LieModule.IsCasimirScalar`: the predicate that the Casimir element acts as a given scalar.

## Main statements

* `LieModule.commute_toEnd_casimir`: **the Casimir element is central.** If `B` is an invariant
  bilinear form on `L` and the families `b`, `b'` are dual bases for `B`, then
  `casimir R L M b b'` commutes with `toEnd R L M x` for every `x : L`.
* `LieModule.lie_toEnd_casimir`: the same statement written as a vanishing Lie bracket.
* `LieModule.commute_toEnd_casimirOfBasis`: the specialisation to a single `B`-orthonormal basis.
* `LieModule.trace_casimir`: `Tr Ω = ∑ i, traceForm R L M (b i) (b' i)`.
* `LieModule.trace_casimir_eq_sum_killingForm`: the adjoint case, in terms of `killingForm`.
* `LieModule.trace_casimir_eq_card`: for a basis dual with respect to the Killing form itself,
  the trace of the Casimir element is the rank of `L`.

## Implementation notes

The expression `∑ a, T a * T a` that one usually writes for the Casimir contracts an adjoint index
with itself, and therefore silently uses an invariant form on `L` to raise that index. That form
is invisible precisely when the generator basis is orthonormal for it, which makes it easy to
write down a definition that is only correct in such a basis.

We therefore do not build any form into `LieModule.casimir`: it takes two families `b` and `b'`
and is a perfectly well-defined endomorphism for any such pair, but it deserves the name "Casimir"
only when the two families are dual with respect to an invariant form. That hypothesis is supplied
explicitly, as `LinearMap.BilinForm.lieInvariant` together with the two expansion identities
`hb`/`hb'`, at the one place where it is actually needed, namely the centrality theorem
`LieModule.commute_toEnd_casimir`. For a basis the expansion identities are automatic and are
provided by `LieModule.sum_apply_smul_eq_self_of_dual` and
`LieModule.sum_apply_smul_eq_self_of_dual'`.

The convenience definition `LieModule.casimirOfBasis` uses `b' = b`; the centrality theorem for it
carries the orthonormality hypothesis `∀ i j, B (b i) (b j) = if i = j then 1 else 0` explicitly,
rather than hiding it in the definition.

Note that no nondegeneracy or semisimplicity hypothesis is required anywhere in this file: the
duality of `b` and `b'` is assumed rather than constructed.
-/

@[expose] public section

open LieModule

namespace Physlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable {ι : Type*} [Fintype ι]

namespace LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The quadratic Casimir endomorphism of a Lie module `M`, attached to a pair of finite families
`b`, `b'` of elements of `L`:  `Ω = ∑ i, φ (b i) ∘ₗ φ (b' i)` where `φ = LieModule.toEnd R L M`.

This is the Casimir element proper when `b` and `b'` are dual bases with respect to an invariant
bilinear form on `L`; see `LieModule.commute_toEnd_casimir`. No such hypothesis is built into the
definition — see the implementation notes of this file. -/
def casimir (b b' : ι → L) : Module.End R M :=
  ∑ i, toEnd R L M (b i) * toEnd R L M (b' i)

/-- The quadratic Casimir element written with composition of endomorphisms rather than
multiplication. -/
lemma casimir_eq_sum_comp (b b' : ι → L) :
    casimir R L M b b' = ∑ i, toEnd R L M (b i) ∘ₗ toEnd R L M (b' i) := by
  simp only [casimir, Module.End.mul_eq_comp]

@[simp]
lemma casimir_apply (b b' : ι → L) (m : M) :
    casimir R L M b b' m = ∑ i, ⁅b i, ⁅b' i, m⁆⁆ := by
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, toEnd_apply_apply]

/-- The quadratic Casimir endomorphism attached to a single basis `b`, i.e.
`∑ i, φ (b i) ∘ₗ φ (b i)`. This is the familiar expression `∑ a, T a * T a`; it computes the
Casimir element only when `b` is orthonormal for an invariant form on `L`, see
`LieModule.commute_toEnd_casimirOfBasis`. -/
noncomputable def casimirOfBasis (b : Module.Basis ι R L) : Module.End R M :=
  casimir R L M b b

lemma casimirOfBasis_eq (b : Module.Basis ι R L) : casimirOfBasis R L M b = casimir R L M b b := rfl

/-- The predicate that the quadratic Casimir element of `M` acts as the scalar `c`. For an
irreducible representation over an algebraically closed field this holds for a unique `c`, the
Casimir eigenvalue of `M`. -/
def IsCasimirScalar (b b' : ι → L) (c : R) : Prop :=
  casimir R L M b b' = c • (1 : Module.End R M)

lemma isCasimirScalar_iff (b b' : ι → L) (c : R) :
    IsCasimirScalar R L M b b' c ↔ ∀ m : M, ∑ i, ⁅b i, ⁅b' i, m⁆⁆ = c • m := by
  simp [IsCasimirScalar, LinearMap.ext_iff]

section Centrality

variable {R L M}

/-- **The quadratic Casimir element is central.**

If `B` is an invariant bilinear form on `L` and the families `b`, `b'` are dual with respect to
`B` — expressed by the two expansion identities `hb` and `hb'` — then the Casimir endomorphism
commutes with the action of every element of `L`. -/
lemma commute_toEnd_casimir {B : LinearMap.BilinForm R L} (hB : B.lieInvariant L)
    {b b' : ι → L}
    (hb : ∀ y : L, ∑ i, B y (b' i) • b i = y)
    (hb' : ∀ y : L, ∑ i, B (b i) y • b' i = y)
    (x : L) :
    Commute (toEnd R L M x) (casimir R L M b b') := by
  have hB' : ∀ y z : L, B ⁅x, y⁆ z = -B y ⁅x, z⁆ := fun y z => hB x y z
  -- the matrix of `ad x` in the family `b`
  have h1 : ∀ i, toEnd R L M ⁅x, b i⁆
      = ∑ j, B ⁅x, b i⁆ (b' j) • toEnd R L M (b j) := by
    intro i
    conv_lhs => rw [← hb ⁅x, b i⁆]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
  -- invariance of `B` forces the matrix of `ad x` in the dual family to be minus its transpose
  have h2 : ∀ i, toEnd R L M ⁅x, b' i⁆
      = -∑ j, B ⁅x, b j⁆ (b' i) • toEnd R L M (b' j) := by
    intro i
    conv_lhs => rw [← hb' ⁅x, b' i⁆]
    rw [map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hB' (b j) (b' i), neg_smul, neg_neg]
  show toEnd R L M x * casimir R L M b b' = casimir R L M b b' * toEnd R L M x
  rw [← sub_eq_zero]
  have key : toEnd R L M x * casimir R L M b b' - casimir R L M b b' * toEnd R L M x
      = ∑ i, (toEnd R L M ⁅x, b i⁆ * toEnd R L M (b' i)
            + toEnd R L M (b i) * toEnd R L M ⁅x, b' i⁆) := by
    simp only [casimir, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LieHom.map_lie, Ring.lie_def]
    noncomm_ring
  rw [key, Finset.sum_add_distrib]
  have hA : ∑ i, toEnd R L M ⁅x, b i⁆ * toEnd R L M (b' i)
      = ∑ i, ∑ j, B ⁅x, b i⁆ (b' j) • (toEnd R L M (b j) * toEnd R L M (b' i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => smul_mul_assoc _ _ _
  have hC : ∑ i, toEnd R L M (b i) * toEnd R L M ⁅x, b' i⁆
      = -∑ i, ∑ j, B ⁅x, b j⁆ (b' i) • (toEnd R L M (b i) * toEnd R L M (b' j)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2 i, mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_smul_comm _ _ _
  rw [hA, hC, ← sub_eq_add_neg, sub_eq_zero]
  exact Finset.sum_comm

/-- The quadratic Casimir element is central, stated as the vanishing of a Lie bracket in
`Module.End R M`. -/
lemma lie_toEnd_casimir {B : LinearMap.BilinForm R L} (hB : B.lieInvariant L)
    {b b' : ι → L}
    (hb : ∀ y : L, ∑ i, B y (b' i) • b i = y)
    (hb' : ∀ y : L, ∑ i, B (b i) y • b' i = y)
    (x : L) :
    ⁅toEnd R L M x, casimir R L M b b'⁆ = 0 := by
  rw [Ring.lie_def, sub_eq_zero]
  exact commute_toEnd_casimir hB hb hb' x

/-- An endomorphism acting as a scalar is central; in particular a Casimir element which is a
scalar commutes with the action of `L`. -/
lemma IsCasimirScalar.commute_toEnd {b b' : ι → L} {c : R}
    (h : IsCasimirScalar R L M b b' c) (x : L) :
    Commute (toEnd R L M x) (casimir R L M b b') := by
  show toEnd R L M x * casimir R L M b b' = casimir R L M b b' * toEnd R L M x
  rw [h, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

end Centrality

section DualBases

variable {R L} [DecidableEq ι]

/-- If `b` is a basis and `b'` is dual to it with respect to `B`, then `B · (b' i)` computes the
coordinates of a vector in the basis `b`. -/
lemma sum_apply_smul_eq_self_of_dual {B : LinearMap.BilinForm R L}
    (b : Module.Basis ι R L) (b' : ι → L)
    (h : ∀ i j, B (b i) (b' j) = if i = j then 1 else 0) (y : L) :
    ∑ i, B y (b' i) • b i = y := by
  have key : ∀ i, B y (b' i) = b.repr y i := by
    intro i
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp [h]
  simp only [key, b.sum_repr]

/-- If `b'` is a basis and `b` is dual to it with respect to `B`, then `B (b i) ·` computes the
coordinates of a vector in the basis `b'`. -/
lemma sum_apply_smul_eq_self_of_dual' {B : LinearMap.BilinForm R L}
    (b : ι → L) (b' : Module.Basis ι R L)
    (h : ∀ i j, B (b i) (b' j) = if i = j then 1 else 0) (y : L) :
    ∑ i, B (b i) y • b' i = y := by
  have key : ∀ i, B (b i) y = b'.repr y i := by
    intro i
    conv_lhs => rw [← b'.sum_repr y]
    rw [map_sum]
    simp [h]
  simp only [key, b'.sum_repr]

/-- **The quadratic Casimir element of a pair of dual bases is central.** -/
lemma commute_toEnd_casimir_of_dual {B : LinearMap.BilinForm R L} (hB : B.lieInvariant L)
    (b b' : Module.Basis ι R L) (h : ∀ i j, B (b i) (b' j) = if i = j then 1 else 0) (x : L) :
    Commute (toEnd R L M x) (casimir R L M b b') :=
  commute_toEnd_casimir hB (sum_apply_smul_eq_self_of_dual b b' h)
    (sum_apply_smul_eq_self_of_dual' b b' h) x

/-- **The quadratic Casimir element of a `B`-orthonormal basis is central.**

This is the statement that `∑ a, T a * T a` commutes with every generator; the orthonormality
hypothesis `h` is exactly the index-raising data that the notation suppresses. -/
lemma commute_toEnd_casimirOfBasis {B : LinearMap.BilinForm R L} (hB : B.lieInvariant L)
    (b : Module.Basis ι R L) (h : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) (x : L) :
    Commute (toEnd R L M x) (casimirOfBasis R L M b) :=
  commute_toEnd_casimir_of_dual M hB b b h x

end DualBases

section Trace

open LinearMap (trace)

/-- The trace of the quadratic Casimir element is the trace form evaluated on the dual bases.
This is the sense in which `LieModule.traceForm` — and hence `killingForm` — is the trace of the
Casimir element. -/
lemma trace_casimir (b b' : ι → L) :
    trace R M (casimir R L M b b') = ∑ i, traceForm R L M (b i) (b' i) := by
  simp only [casimir, map_sum, traceForm_apply_apply, Module.End.mul_eq_comp]

/-- In the adjoint representation the trace of the quadratic Casimir element is a sum of values of
the Killing form. -/
lemma trace_casimir_eq_sum_killingForm (b b' : ι → L) :
    trace R L (casimir R L L b b') = ∑ i, killingForm R L (b i) (b' i) :=
  trace_casimir R L L b b'

/-- For a pair of bases dual with respect to the Killing form itself, the trace of the quadratic
Casimir element of the adjoint representation is the rank of `L`. -/
lemma trace_casimir_eq_card [DecidableEq ι] (b b' : ι → L)
    (h : ∀ i j, killingForm R L (b i) (b' j) = if i = j then 1 else 0) :
    trace R L (casimir R L L b b') = (Fintype.card ι : R) := by
  rw [trace_casimir_eq_sum_killingForm]
  simp [h, Finset.card_univ]

end Trace

end LieModule

end Physlib
