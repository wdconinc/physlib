/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Basic
public import Physlib.Relativity.Tensors.MetricTensor
public import Physlib.Relativity.Tensors.RealTensor.Metrics.LeviCivita
/-!

## Metrics as real Lorentz tensors

-/

@[expose] public section

open Module
open Matrix
open MatrixGroups
open TensorProduct
open Equiv
open TensorSpecies Tensor

noncomputable section

namespace realLorentzTensor

open realLorentzTensor

/-!

## Definitions.

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensor. -/
abbrev coMetric (d : ℕ := 3) : ℝT[d, Color.down, Color.down] :=
  (realLorentzTensor d).metricTensor Color.down

/-- The metric `ηⁱⁱ` as a complex Lorentz tensor. -/
abbrev contrMetric (d : ℕ := 3) : ℝT[d, Color.up, Color.up] :=
  (realLorentzTensor d).metricTensor Color.up

/-- The mixed Kronecker delta (identity tensor) `δ^ρ_σ = η^{ρλ} η_{λσ}`.
This is 1 when ρ = σ and 0 otherwise. -/
def kroneckerDelta (d : ℕ := 3) : ℝT[d, Color.up, Color.down] :=
  fromConstPair ((realLorentzTensor d).unit Color.down)

/-!

## Notation

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensors. -/
scoped[realLorentzTensor] notation "η'" => @coMetric

/-- The metric `ηⁱⁱ` as a complex Lorentz tensors. -/
scoped[realLorentzTensor] notation "η" => @contrMetric

/-!

## Equivalent forms of the metrics

-/
open TensorSpecies
open Tensor

/- The covariant rank-4 Levi-Civita tensor in 3+1 dimensions. -/
/-
noncomputable def leviCivita4Co : ℝT[.down, .down, .down, .down] :=
  (Tensor.basis (S := realLorentzTensor 3)
      ![Color.down, Color.down, Color.down, Color.down]).repr.symm <|
    (Finsupp.linearEquivFunOnFinite ℝ ℝ ((j : Fin 4) → Fin 1 ⊕ Fin 3)).symm <|
      fun j => (leviCivita4Int (finSumFinEquiv (j 0)) (finSumFinEquiv (j 1))
        (finSumFinEquiv (j 2)) (finSumFinEquiv (j 3)) : ℝ)

@[simp]
lemma leviCivita4Co_basis_repr_apply
    (b : ComponentIdx (S := realLorentzTensor 3)
      ![Color.down, Color.down, Color.down, Color.down]) :
    (Tensor.basis (S := realLorentzTensor 3)
      ![Color.down, Color.down, Color.down, Color.down]).repr leviCivita4Co b =
      (leviCivita4Int (finSumFinEquiv (b 0)) (finSumFinEquiv (b 1))
        (finSumFinEquiv (b 2)) (finSumFinEquiv (b 3)) : ℝ) := by
  simp [leviCivita4Co]
-/

lemma coMetric_eq_fromConstPair {d : ℕ} :
    η' d = fromConstPair (S := realLorentzTensor d) (c1 := .down) (c2 := .down)
      (Lorentz.preCoMetric d) := by
  rfl

lemma contrMetric_eq_fromConstPair {d : ℕ} :
    η d = fromConstPair (S := realLorentzTensor d)
      (c1 := .up) (c2 := .up) (Lorentz.preContrMetric d) := by
  rfl

lemma coMetric_eq_fromPairT {d : ℕ} :
    η' d = fromPairT (S := realLorentzTensor d) (c1 := .down) (c2 := .down)
      (Lorentz.preCoMetricVal d) := by
  rw [coMetric_eq_fromConstPair, fromConstPair, Lorentz.preCoMetric_apply_one]

lemma contrMetric_eq_fromPairT {d : ℕ} :
    η d = fromPairT (S := realLorentzTensor d) (c1 := .up) (c2 := .up)
        (Lorentz.preContrMetricVal d) := by
  rw [contrMetric_eq_fromConstPair, fromConstPair, Lorentz.preContrMetric_apply_one]

/-

## Group actions

-/

/-- The tensor `coMetric` is invariant under the action of `LorentzGroup d`. -/
@[simp]
lemma actionT_coMetric {d : ℕ} (g : LorentzGroup d) :
    g • η' d = η' d:= by
  erw [TensorSpecies.metricTensor_invariant]

/-- The tensor `contrMetric` is invariant under the action of `LorentzGroup d`. -/
@[simp]
lemma actionT_contrMetric {d} (g : LorentzGroup d) : g • η d = η d := by
  erw [TensorSpecies.metricTensor_invariant]

/-

## There value with respect to a basis

-/

lemma coMetric_repr_apply_eq_minkowskiMatrix {d : ℕ}
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.down, Color.down]) :
    (Tensor.basis _).repr (coMetric d) b =
    minkowskiMatrix (b 0) (b 1) := by
  rw [coMetric_eq_fromPairT, fromPairT_basis_repr,
    Lorentz.preCoMetricVal_expand_tmul_minkowskiMatrix]
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single (b 0)] <;>
    simp +contextual [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply]

lemma contrMetric_repr_apply_eq_minkowskiMatrix {d : ℕ}
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.up, Color.up]) :
    (Tensor.basis _).repr (contrMetric d) b =
    minkowskiMatrix (b 0) (b 1) := by
  rw [contrMetric_eq_fromPairT, fromPairT_basis_repr,
    Lorentz.preContrMetricVal_expand_tmul_minkowskiMatrix]
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single (b 0)] <;>
    simp +contextual [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply]

end realLorentzTensor
