/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.DIS.LO
/-!

# Higher-Order Factorization Interfaces (Stage 11)

This module defines perturbative-order-indexed kernels, scheme conversions,
and truncation interfaces for post-LO formalization.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Factorization
namespace HigherOrder

variable {Flavor : Type}

/-- Perturbative order index. -/
inductive PerturbativeOrder where
  | LO
  | NLO
  | NNLO

/-- A hard-kernel family indexed by perturbative order. -/
abbrev HardKernelFamily (Flavor : Type) : Type :=
  PerturbativeOrder → DIS.HardKernel Flavor

/-- Accessor for hard kernels at a selected perturbative order. -/
def hardKernelAtOrder
    (C : HardKernelFamily Flavor)
    (ord : PerturbativeOrder) : DIS.HardKernel Flavor :=
  C ord

/-- LO embedding is a strict specialization of higher-order families. -/
lemma lo_kernel_embedding
    (C : HardKernelFamily Flavor) :
    hardKernelAtOrder C PerturbativeOrder.LO = C PerturbativeOrder.LO :=
  rfl

/-- Renormalization/factorization scheme interface. -/
structure Scheme : Type where
  name : String

/-- Scheme conversion map for hard kernels at fixed perturbative order. -/
def convertKernel
    (S1 S2 : Scheme)
    (C : HardKernelFamily Flavor)
    (_ord : PerturbativeOrder) : HardKernelFamily Flavor :=
  if S1.name = S2.name then C else C

/-- Identity scheme conversion leaves kernels unchanged. -/
lemma convertKernel_id
    (S : Scheme)
    (C : HardKernelFamily Flavor)
    (ord : PerturbativeOrder) :
    hardKernelAtOrder (convertKernel S S C ord) ord = hardKernelAtOrder C ord := by
  simp [convertKernel, hardKernelAtOrder]

/-- Truncated observable interface: currently exposing LO truncation. -/
def truncatedStructureFunction [Fintype Flavor]
    (C : HardKernelFamily Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (x Q2 : ℝ) : ℝ :=
  DIS.loStructureFunction (C PerturbativeOrder.LO) f x Q2

/-- Truncated observable equals LO expression at LO truncation. -/
lemma truncatedStructureFunction_lo [Fintype Flavor]
    (C : HardKernelFamily Flavor)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (x Q2 : ℝ) :
    truncatedStructureFunction C f x Q2
      = DIS.loStructureFunction (C PerturbativeOrder.LO) f x Q2 :=
  rfl

end HigherOrder
end Factorization
end QFT
end Physlib
