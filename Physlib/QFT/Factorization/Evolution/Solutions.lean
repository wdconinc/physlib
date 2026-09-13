/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.Evolution.Basic
/-!

# DGLAP Evolution Toy Solutions

This module contains restricted solved examples.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Factorization
namespace Evolution

variable {Flavor : Type}

/-- A toy solved case: zero kernels and zero coupling solve the log-scale equation
for any PDF that is pointwise zero. -/
lemma toySolution_zeroKernel_zeroCoupling [Fintype Flavor]
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (hzero : ∀ i x Q2, f i x Q2 = 0) :
    IsDGLAPLogScaleEquation (fun _ _ _ _ => 0) (fun _ => 0) f := by
  intro i x τ
  rw [hzero i x (Real.exp τ)]
  simp [dglapRhsLogScale, dglapOperator_zero_kernel]

end Evolution
end Factorization
end QFT
end Physlib
