/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Inference.Basic
public import Physlib.QFT.Factorization.Evolution.QCDCore
/-!

# Unfolding Analysis Interfaces

This module provides theorem-design contracts for detector unfolding in DIS measurements.

Unfolding (or deconvolution) corrects a measured distribution for detector acceptance,
efficiency, and smearing effects to recover the true particle- or parton-level distribution.

## Key concepts

- **Response matrix** `R`: encodes the probability that a true event in bin `j` is
  reconstructed in measured bin `i`. The forward map is `μ_i = Σ_j R_i_j · σ_j + b_i`.
- **Fold-forward**: applying `R` to a true distribution to predict measured counts.
- **Unfolding**: inverting the fold-forward map under regularity constraints.
- **Bin-by-bin correction**: a diagonal approximation `c_i = μ_true_i / μ_reco_i` applied
  pointwise; appropriate when off-diagonal migration is small.
- **Bias control**: the unfolded result should not systematically deviate from the truth
  by more than a stated residual bound.

## Design notes

- Response matrices are encoded as `Fin m → Fin n → ℝ` (row = reco bin, col = true bin).
- True and measured distributions are `Fin n → ℝ` and `Fin m → ℝ` respectively.
- Background contributions are explicit.
- All lemmas are stated as interface contracts; where full analytic proof would require
  unbounded linear-algebra machinery, explicit assumption fields encode the needed facts.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Inference
namespace Unfolding

open Physlib.QFT.Factorization.Evolution

/-! ## Response matrix and fold-forward -/

/-- A response (migration) matrix for detector unfolding.
    Entry `R i j` is the probability that a true event in bin `j` is reconstructed in bin `i`. -/
def ResponseMatrix (m n : ℕ) : Type := Fin m → Fin n → ℝ

/-- Row sum (reconstruction efficiency for true bin `j`). -/
def rowSum {m n : ℕ} (R : ResponseMatrix m n) (j : Fin n) : ℝ :=
  ∑ i : Fin m, R i j

/-- Fold-forward: apply response matrix to a true distribution to predict measured counts. -/
def foldForward {m n : ℕ} (R : ResponseMatrix m n)
    (σTrue : Fin n → ℝ) (background : Fin m → ℝ) : Fin m → ℝ :=
  fun i => (∑ j : Fin n, R i j * σTrue j) + background i

/-- Linearity of fold-forward in the true distribution. -/
lemma foldForward_linear {m n : ℕ} (R : ResponseMatrix m n)
    (σ₁ σ₂ : Fin n → ℝ) (background : Fin m → ℝ) (a b : ℝ) :
    foldForward R (fun j => a * σ₁ j + b * σ₂ j) background
      = fun i => a * (foldForward R σ₁ 0) i + b * (foldForward R σ₂ 0) i
                  + background i := by
  funext i
  simp [foldForward, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have h1 :
      (∑ x : Fin n, R i x * (a * σ₁ x)) = (∑ x : Fin n, a * (R i x * σ₁ x)) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  have h2 :
      (∑ x : Fin n, R i x * (b * σ₂ x)) = (∑ x : Fin n, b * (R i x * σ₂ x)) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  rw [h1, h2]

/-- Zero background specialization: fold-forward is purely linear. -/
lemma foldForward_zero_background {m n : ℕ} (R : ResponseMatrix m n)
    (σTrue : Fin n → ℝ) :
    foldForward R σTrue 0 = fun i => ∑ j : Fin n, R i j * σTrue j := by
  funext i
  simp [foldForward]

/-! ## Identity response -/

/-- An identity-like response matrix (square, diagonal dominant). -/
structure IdentityResponseAssumptions {n : ℕ} (R : ResponseMatrix n n) : Prop where
  /-- Diagonal entries equal 1. -/
  diagonal_one : ∀ i, R i i = 1
  /-- Off-diagonal entries equal 0. -/
  offdiag_zero : ∀ i j, i ≠ j → R i j = 0

/-- Under an identity response, fold-forward recovers the true distribution exactly. -/
lemma foldForward_identity {n : ℕ} (R : ResponseMatrix n n)
    (σTrue : Fin n → ℝ)
    (hId : IdentityResponseAssumptions R) :
    foldForward R σTrue 0 = σTrue := by
  funext i
  simp [foldForward]
  calc ∑ j : Fin n, R i j * σTrue j
      = ∑ j : Fin n, if i = j then σTrue j else 0 := by
        congr 1; funext j
        by_cases hij : i = j
        · simp [hij, hId.diagonal_one]
        · have hR : R i j = 0 := hId.offdiag_zero i j hij
          rw [hR, if_neg hij]
          simp
    _ = σTrue i := by
      classical
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hij
        have hne : ¬ i = j := by
          intro hEq
          exact hij hEq.symm
        simp [hne]
      · simp

/-! ## Bin-by-bin correction -/

/-- Bin-by-bin correction factors: pointwise ratio of truth to reco expectation. -/
structure BinByBinCorrection (m : ℕ) : Type where
  /-- Correction factor for each measured bin. -/
  factor : Fin m → ℝ
  /-- Factors are positive (avoids division by zero or sign flip). -/
  factor_pos : ∀ i, 0 < factor i

/-- Apply bin-by-bin correction to a measured distribution. -/
def applyBinByBin {m : ℕ} (C : BinByBinCorrection m) (μMeas : Fin m → ℝ) : Fin m → ℝ :=
  fun i => C.factor i * μMeas i

/-- Bin-by-bin correction preserves nonnegativity of nonneg measured distributions. -/
lemma applyBinByBin_nonneg {m : ℕ} (C : BinByBinCorrection m)
    (μMeas : Fin m → ℝ) (hMeas : ∀ i, 0 ≤ μMeas i) :
    ∀ i, 0 ≤ applyBinByBin C μMeas i := by
  intro i
  exact mul_nonneg (le_of_lt (C.factor_pos i)) (hMeas i)

/-- A bin-by-bin correction scheme is consistent if it exactly inverts fold-forward
    when the correction factors equal the per-bin truth/reco ratio. -/
structure BinByBinConsistencyAssumptions {n : ℕ}
    (R : ResponseMatrix n n)
    (σTrue : Fin n → ℝ)
    (C : BinByBinCorrection n) : Prop where
  /-- Each correction factor equals the ratio of the true distribution to the
      response-weighted (reconstructed) distribution. -/
  factor_eq : ∀ i,
    (∑ j : Fin n, R i j * σTrue j) ≠ 0 →
    C.factor i * (∑ j : Fin n, R i j * σTrue j) = σTrue i

/-- Under bin-by-bin consistency, applying the correction to the folded-forward
    distribution recovers the true distribution. -/
lemma applyBinByBin_recovers {n : ℕ}
    (R : ResponseMatrix n n)
    (σTrue : Fin n → ℝ)
    (C : BinByBinCorrection n)
    (hCons : BinByBinConsistencyAssumptions R σTrue C)
    (hFoldNonzero : ∀ i, (∑ j : Fin n, R i j * σTrue j) ≠ 0) :
    applyBinByBin C (foldForward R σTrue 0) = σTrue := by
  funext i
  simp [applyBinByBin, foldForward]
  exact hCons.factor_eq i (hFoldNonzero i)

/-! ## Unfolding bias control -/

/-- An unfolding result with explicit bias bound. -/
structure UnfoldingResult (n : ℕ) : Type where
  /-- The unfolded (corrected) distribution. -/
  unfolded : Fin n → ℝ
  /-- The declared pointwise bias bound. -/
  biasBound : ℝ
  /-- The bound is nonneg. -/
  bound_nonneg : 0 ≤ biasBound

/-- Bias control contract: the unfolded result stays within `biasBound` of the truth. -/
structure BiasControlAssumptions {n : ℕ}
    (res : UnfoldingResult n)
    (σTrue : Fin n → ℝ) : Prop where
  /-- Pointwise deviation from truth is bounded. -/
  pointwise_bias : ∀ i, |res.unfolded i - σTrue i| ≤ res.biasBound

/-- Bias propagates to any linear functional of the unfolded distribution. -/
lemma bias_propagates_to_linear_functional {n : ℕ}
    (res : UnfoldingResult n)
    (σTrue : Fin n → ℝ)
    (hBias : BiasControlAssumptions res σTrue)
    (weight : Fin n → ℝ) :
    |∑ i, weight i * res.unfolded i - ∑ i, weight i * σTrue i|
      ≤ (∑ i, |weight i|) * res.biasBound := by
  have hSum : ∑ i, weight i * res.unfolded i - ∑ i, weight i * σTrue i
      = ∑ i, weight i * (res.unfolded i - σTrue i) := by
    simp [Finset.sum_sub_distrib, mul_sub]
  rw [hSum]
  calc |∑ i, weight i * (res.unfolded i - σTrue i)|
      ≤ ∑ i, |weight i * (res.unfolded i - σTrue i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |weight i| * |res.unfolded i - σTrue i| := by
        congr 1; funext i; rw [abs_mul]
    _ ≤ ∑ i, |weight i| * res.biasBound := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hBias.pointwise_bias i) (abs_nonneg _)
    _ = (∑ i, |weight i|) * res.biasBound := by
        rw [← Finset.sum_mul]

/-! ## Consistency check: fold-forward of unfolded result -/

/-- Fold-forward consistency: the unfolded distribution folds back close to observations. -/
structure FoldBackConsistencyAssumptions {m n : ℕ}
    (R : ResponseMatrix m n)
    (background : Fin m → ℝ)
    (res : UnfoldingResult n)
    (μMeas : Fin m → ℝ) : Prop where
  /-- Each measured bin is reproduced to within residual tolerance after fold-back. -/
  residual : ∀ i,
    |foldForward R res.unfolded background i - μMeas i| ≤ res.biasBound

/-- If fold-back is consistent and bias bound is zero, the unfolded solution is exact. -/
lemma foldBack_exact_of_zero_bound {m n : ℕ}
    (R : ResponseMatrix m n)
    (background : Fin m → ℝ)
    (res : UnfoldingResult n)
    (μMeas : Fin m → ℝ)
    (hCons : FoldBackConsistencyAssumptions R background res μMeas)
    (hZero : res.biasBound = 0) :
    foldForward R res.unfolded background = μMeas := by
  funext i
  have h := hCons.residual i
  rw [hZero] at h
  have habs : |foldForward R res.unfolded background i - μMeas i| = 0 :=
    le_antisymm h (abs_nonneg _)
  linarith [abs_eq_zero.mp habs]

/-! ## SU(N) evolution bridge for inference-facing APIs -/

/-- Inference-facing corollary: the DGLAP rhs under representation-derived
`SU(Nc)` running coupling is identical to the rhs under the direct
`suNColorFactors` coupling.

This theorem re-exports the evolution-layer bridge at the DIS inference surface.
-/
lemma dglapRhs_suN_representation_bridge
    {Flavor : Type} [Fintype Flavor]
    (nC nF lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ : ℝ) :
    dglapRhsLogScale P
        (qcdRunningCouplingFromRepresentation (Physlib.QFT.QCD.SUN nC) nF lambdaQCD2) f i x τ
      = dglapRhsLogScale P
          (qcdRunningCoupling (Physlib.QFT.QCD.suNColorFactors nC nF) lambdaQCD2) f i x τ := by
  simpa using qcdDglap_rhs_suN_fromRepresentation_eq
    (Flavor := Flavor) nC nF lambdaQCD2 P f i x τ

/-- Inference-facing proposition transport: an rhs-equality observable statement at
fixed phase-space point is equivalent between representation-derived and direct
`SU(Nc)` couplings. -/
lemma dglapRhs_suN_representation_eq_target_iff
    {Flavor : Type} [Fintype Flavor]
    (nC nF lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ target : ℝ) :
    dglapRhsLogScale P
        (qcdRunningCouplingFromRepresentation (Physlib.QFT.QCD.SUN nC) nF lambdaQCD2) f i x τ
      = target
      ↔
      dglapRhsLogScale P
        (qcdRunningCoupling (Physlib.QFT.QCD.suNColorFactors nC nF) lambdaQCD2) f i x τ
      = target := by
  constructor
  · intro h
    rw [← dglapRhs_suN_representation_bridge
      (Flavor := Flavor) (nC := nC) (nF := nF) (lambdaQCD2 := lambdaQCD2)
      (P := P) (f := f) (i := i) (x := x) (τ := τ)]
    exact h
  · intro h
    rw [dglapRhs_suN_representation_bridge
      (Flavor := Flavor) (nC := nC) (nF := nF) (lambdaQCD2 := lambdaQCD2)
      (P := P) (f := f) (i := i) (x := x) (τ := τ)]
    exact h

/-- Inference-facing transport for residual bounds: absolute-deviation constraints
on the rhs are equivalent between representation-derived and direct
`SU(Nc)` couplings. -/
lemma dglapRhs_suN_representation_residual_iff
    {Flavor : Type} [Fintype Flavor]
    (nC nF lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ target eps : ℝ) :
    |dglapRhsLogScale P
        (qcdRunningCouplingFromRepresentation (Physlib.QFT.QCD.SUN nC) nF lambdaQCD2) f i x τ
      - target| ≤ eps
      ↔
      |dglapRhsLogScale P
        (qcdRunningCoupling (Physlib.QFT.QCD.suNColorFactors nC nF) lambdaQCD2) f i x τ
      - target| ≤ eps := by
  constructor
  · intro h
    rw [← dglapRhs_suN_representation_bridge
      (Flavor := Flavor) (nC := nC) (nF := nF) (lambdaQCD2 := lambdaQCD2)
      (P := P) (f := f) (i := i) (x := x) (τ := τ)]
    exact h
  · intro h
    rw [dglapRhs_suN_representation_bridge
      (Flavor := Flavor) (nC := nC) (nF := nF) (lambdaQCD2 := lambdaQCD2)
      (P := P) (f := f) (i := i) (x := x) (τ := τ)]
    exact h

/-- Fit-level bridge: the pointwise chi-square contribution built from the
representation-derived `SU(Nc)` rhs equals the one built from the direct
`suNColorFactors` rhs. -/
lemma chiSq_suN_dglapRhs_representation_eq
    {Flavor : Type} [Fintype Flavor]
    (nC nF lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ observed sigma : ℝ) :
    chiSq
      (dglapRhsLogScale P
        (qcdRunningCouplingFromRepresentation (Physlib.QFT.QCD.SUN nC) nF lambdaQCD2) f i x τ)
      observed sigma
      =
      chiSq
        (dglapRhsLogScale P
          (qcdRunningCoupling (Physlib.QFT.QCD.suNColorFactors nC nF) lambdaQCD2) f i x τ)
        observed sigma := by
  rw [dglapRhs_suN_representation_bridge
    (Flavor := Flavor) (nC := nC) (nF := nF) (lambdaQCD2 := lambdaQCD2)
    (P := P) (f := f) (i := i) (x := x) (τ := τ)]

/-- Bundled assumptions for pointwise SU(N) rhs consistency checks in
inference-facing analyses. -/
structure SURhsConsistencyInputs : Type where
  target : ℝ
  eps : ℝ
  observed : ℝ
  sigma : ℝ

/-- Packaged SU(N) bridge: from one input bundle, derive both the residual-bound
transport and chi-square transport between representation-derived and direct
coupling paths. -/
lemma suRhsConsistencyBridgeBundle
    {Flavor : Type} [Fintype Flavor]
    (nC nF lambdaQCD2 : ℝ)
    (P : SplittingKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x τ : ℝ)
    (inp : SURhsConsistencyInputs) :
    (|dglapRhsLogScale P
        (qcdRunningCouplingFromRepresentation (Physlib.QFT.QCD.SUN nC) nF lambdaQCD2) f i x τ
      - inp.target| ≤ inp.eps
      ↔
      |dglapRhsLogScale P
        (qcdRunningCoupling (Physlib.QFT.QCD.suNColorFactors nC nF) lambdaQCD2) f i x τ
      - inp.target| ≤ inp.eps)
    ∧
    (chiSq
      (dglapRhsLogScale P
        (qcdRunningCouplingFromRepresentation (Physlib.QFT.QCD.SUN nC) nF lambdaQCD2) f i x τ)
      inp.observed inp.sigma
      =
      chiSq
        (dglapRhsLogScale P
          (qcdRunningCoupling (Physlib.QFT.QCD.suNColorFactors nC nF) lambdaQCD2) f i x τ)
        inp.observed inp.sigma) := by
  refine ⟨?_, ?_⟩
  · simpa using dglapRhs_suN_representation_residual_iff
      (Flavor := Flavor) (nC := nC) (nF := nF) (lambdaQCD2 := lambdaQCD2)
      (P := P) (f := f) (i := i) (x := x) (τ := τ) (target := inp.target) (eps := inp.eps)
  · simpa using chiSq_suN_dglapRhs_representation_eq
      (Flavor := Flavor) (nC := nC) (nF := nF) (lambdaQCD2 := lambdaQCD2)
      (P := P) (f := f) (i := i) (x := x) (τ := τ) (observed := inp.observed)
      (sigma := inp.sigma)

end Unfolding
end Inference
end DIS
end Scattering
end QFT
end Physlib
