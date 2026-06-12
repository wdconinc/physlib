/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.Convolution.Properties
public import Physlib.QFT.Factorization.DIS.HardKernel
public import Physlib.QFT.Scattering.DIS.Tensors.Basic
public import Physlib.Particles.Parton.PDF.Basic
/-!

# DIS LO Factorization

This module provides leading-order factorized representations of DIS structure
functions using tensor, PDF, and convolution kernels.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace QFT
namespace Factorization
namespace DIS

variable {Flavor : Type}

/-- The flavor-channel LO contribution represented as a convolution. -/
def loChannel
    (C : HardKernel Flavor) (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (i : Flavor) (x Q2 : ℝ) : ℝ :=
  Convolution.convolveAt (fun x' z => C i x' z Q2) (fun z => f i z Q2) x

/-- The full LO structure function as a flavor sum of channel convolutions. -/
def loStructureFunction [Fintype Flavor]
    (C : HardKernel Flavor) (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (x Q2 : ℝ) : ℝ :=
  ∑ i, loChannel C f i x Q2

/-- Abstract statement that `F` is represented by an LO factorization formula. -/
def IsLOFactorized [Fintype Flavor]
    (F : ℝ → ℝ → ℝ)
    (C : HardKernel Flavor) (f : Physlib.Particles.Parton.PDF.Pdf Flavor) : Prop :=
  ∀ x Q2, F x Q2 = loStructureFunction C f x Q2

/-- Canonical LO representation theorem. -/
lemma loStructureFunction_isFactorized [Fintype Flavor]
    (C : HardKernel Flavor) (f : Physlib.Particles.Parton.PDF.Pdf Flavor) :
    IsLOFactorized (loStructureFunction C f) C f := by
  intro x Q2
  rfl

/-- A concrete corollary for a flavor-local kernel family. -/
lemma loStructureFunction_singleFlavor_kernel [Fintype Flavor]
    (C0 : ℝ → ℝ → ℝ → ℝ)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (x Q2 : ℝ) :
    loStructureFunction (fun _ x' z q2 => C0 x' z q2) f x Q2
      = ∑ i, Convolution.convolveAt (fun x' z => C0 x' z Q2) (fun z => f i z Q2) x := by
  simp [loStructureFunction, loChannel]

/-- Physics-facing factorization assumptions, separated from structural assumptions. -/
structure LOPhysicsAssumptions : Type where
  /-- Placeholder proposition for perturbative-regime validity. -/
  perturbativeRegime : Prop
  /-- Witness that perturbative-regime assumptions hold. -/
  hPerturbativeRegime : perturbativeRegime

/-- Theorem schema separating analytic and physics assumptions in the signature. -/
lemma loFactorized_of_assumptions [Fintype Flavor]
    (F : ℝ → ℝ → ℝ)
    (C : HardKernel Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (_hKernel : HardKernelAssumptions C)
    (_hPdf : Physlib.Particles.Parton.PDF.Assumptions f)
    (_hPhys : LOPhysicsAssumptions)
    (hRep : IsLOFactorized F C f) :
    ∀ x Q2, F x Q2 = loStructureFunction C f x Q2 :=
  hRep

end DIS
end Factorization
end QFT
end Physlib
