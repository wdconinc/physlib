/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# Inference Interfaces (Stage 14)

This module introduces statistical-inference contracts for DIS observables.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Inference

/-- Abstract data point for inference interfaces. -/
structure DataPoint : Type where
  xBj : ℝ
  Q2 : ℝ
  observed : ℝ

/-- Covariance-model placeholder interface. -/
structure CovarianceModel : Type where
  variance : DataPoint → ℝ

/-- Chi-square contribution interface. -/
def chiSq (prediction observed sigma : ℝ) : ℝ :=
  (prediction - observed) ^ 2 / (|sigma| + 1)

/-- Chi-square nonnegativity theorem under the default denominator contract. -/
lemma chiSq_nonneg (prediction observed sigma : ℝ) :
    0 ≤ chiSq prediction observed sigma := by
  have hnum : 0 ≤ (prediction - observed) ^ 2 := sq_nonneg (prediction - observed)
  have hden : 0 ≤ |sigma| + 1 := by
    exact add_nonneg (abs_nonneg sigma) (by norm_num)
  exact div_nonneg hnum hden

/-- Nuisance-shifted prediction interface. -/
def shiftedPrediction (prediction nuisanceShift : ℝ) : ℝ :=
  prediction + nuisanceShift

/-- Stability theorem under bounded nuisance shifts. -/
lemma shiftedPrediction_stability
    (prediction nuisanceShift eps : ℝ)
    (hBound : |nuisanceShift| ≤ eps) :
    |shiftedPrediction prediction nuisanceShift - prediction| ≤ eps := by
  simpa [shiftedPrediction] using hBound

end Inference
end DIS
end Scattering
end QFT
end Physlib
