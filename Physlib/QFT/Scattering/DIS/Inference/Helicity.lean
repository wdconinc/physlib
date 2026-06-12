/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Polarized.Basic
public import Physlib.QFT.Factorization.HigherOrder.Basic
/-!

# DeltaSigma Access Interfaces

This module provides theorem-design targets for polarized first-moment
observables used to access DeltaSigma.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Inference
namespace Helicity

/-- First moment of `g1` over the physical `xBj` interval. -/
def g1FirstMoment
    (G : Polarized.StructureFunctions)
    (Q2 : ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, G.g1 x Q2

/-- Truncated first moment on the experimentally covered interval `[xmin, xmax]`. -/
def g1FirstMomentTruncated
    (G : Polarized.StructureFunctions)
    (xmin xmax Q2 : ℝ) : ℝ :=
  ∫ x in Set.Icc xmin xmax, G.g1 x Q2

/-- Finite-coverage assumptions for extrapolating truncated moments to full moments. -/
structure FiniteCoverageAssumptions
    (G : Polarized.StructureFunctions)
    (xmin xmax : ℝ) : Prop where
  xmin_nonneg : 0 ≤ xmin
  xmax_le_one : xmax ≤ 1
  lowX_tail : ∀ Q2, |∫ x in Set.Icc (0 : ℝ) xmin, G.g1 x Q2| ≤ 1
  highX_tail : ∀ Q2, |∫ x in Set.Icc xmax (1 : ℝ), G.g1 x Q2| ≤ 1
  truncation_error_le_tail_sum :
    ∀ Q2,
      |g1FirstMoment G Q2 - g1FirstMomentTruncated G xmin xmax Q2|
        ≤ |∫ x in Set.Icc (0 : ℝ) xmin, G.g1 x Q2|
          + |∫ x in Set.Icc xmax (1 : ℝ), G.g1 x Q2|

/-- DeltaSigma extraction contract at fixed scale with explicit scheme ingredients. -/
structure DeltaSigmaSchemeAssumptions
    (G : Polarized.StructureFunctions)
    (deltaSigma : ℝ → ℝ)
    (wilsonSinglet nonSingletShift : ℝ → ℝ) : Prop where
  extraction : ∀ Q2,
    g1FirstMoment G Q2 = wilsonSinglet Q2 * deltaSigma Q2 + nonSingletShift Q2

/-- Theoretical reconstruction formula for DeltaSigma from a measured first moment. -/
lemma deltaSigma_eq_of_scheme
    (G : Polarized.StructureFunctions)
    (deltaSigma : ℝ → ℝ)
    (wilsonSinglet nonSingletShift : ℝ → ℝ)
    (hSch : DeltaSigmaSchemeAssumptions G deltaSigma wilsonSinglet nonSingletShift)
    (Q2 : ℝ)
    (hWilson : wilsonSinglet Q2 ≠ 0) :
    deltaSigma Q2
      = (g1FirstMoment G Q2 - nonSingletShift Q2) / wilsonSinglet Q2 := by
  have hEq := hSch.extraction Q2
  have hLin : g1FirstMoment G Q2 - nonSingletShift Q2 = wilsonSinglet Q2 * deltaSigma Q2 := by
    linarith
  have hMul : deltaSigma Q2 * wilsonSinglet Q2 = g1FirstMoment G Q2 - nonSingletShift Q2 := by
    simpa [mul_comm] using hLin.symm
  exact (eq_div_iff hWilson).2 hMul

/-- Bounded finite-coverage correction interface. -/
lemma firstMoment_minus_truncated_bound
    (G : Polarized.StructureFunctions)
    (xmin xmax Q2 : ℝ)
    (hCov : FiniteCoverageAssumptions G xmin xmax) :
    |g1FirstMoment G Q2 - g1FirstMomentTruncated G xmin xmax Q2| ≤ 2 := by
  have hLow := hCov.lowX_tail Q2
  have hHigh := hCov.highX_tail Q2
  have hTriangle := hCov.truncation_error_le_tail_sum Q2
  linarith

/-- Identity-scheme specialization placeholder for DeltaSigma extraction. -/
lemma deltaSigma_scheme_id_stability
    (G : Polarized.StructureFunctions)
    (deltaSigma : ℝ → ℝ)
    (wilsonSinglet nonSingletShift : ℝ → ℝ)
    (hSch : DeltaSigmaSchemeAssumptions G deltaSigma wilsonSinglet nonSingletShift)
    (Q2 : ℝ) :
    g1FirstMoment G Q2 = wilsonSinglet Q2 * deltaSigma Q2 + nonSingletShift Q2 :=
  hSch.extraction Q2

end Helicity
end Inference
end DIS
end Scattering
end QFT
end Physlib
