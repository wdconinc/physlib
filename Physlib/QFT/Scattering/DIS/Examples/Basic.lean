/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.DIS.LO
public import Physlib.Particles.Parton.TMD.Reduction
public import Physlib.Particles.Parton.GPD.Basic
/-!

# DIS Validation Examples

This module provides worked examples that connect earlier APIs
into end-to-end theorem pipelines.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Examples

variable {Flavor : Type}

/-- Worked example: from assumptions to LO factorized observable equality. -/
lemma lo_factorized_pipeline [Fintype Flavor]
    (F : ℝ → ℝ → ℝ)
    (C : Factorization.DIS.HardKernel Flavor)
    (f : Particles.Parton.PDF.Pdf Flavor)
    (hKernel : Factorization.DIS.HardKernelAssumptions C)
    (hPdf : Particles.Parton.PDF.Assumptions f)
    (hPhys : Factorization.DIS.LOPhysicsAssumptions)
    (hRep : Factorization.DIS.IsLOFactorized F C f)
    (x Q2 : ℝ) :
    F x Q2 = Factorization.DIS.loStructureFunction C f x Q2 :=
  Factorization.DIS.loFactorized_of_assumptions F C f hKernel hPdf hPhys hRep x Q2

/-- Worked example: integrated-TMD and collinear LO observables agree. -/
lemma tmd_integration_example [Fintype Flavor]
    (C : Factorization.DIS.HardKernel Flavor)
    (fTmd : Particles.Parton.TMD.Tmd Flavor)
    (fPdf : Particles.Parton.PDF.Pdf Flavor)
    (ktMax ζ x Q2 : ℝ)
    (hRed : Particles.Parton.TMD.IntegratesToPdf fTmd fPdf ktMax ζ) :
    Factorization.DIS.loStructureFunction C
        (Particles.Parton.TMD.collinearFromTmd fTmd ktMax ζ) x Q2
      = Factorization.DIS.loStructureFunction C fPdf x Q2 :=
  Particles.Parton.TMD.loStructureFunction_tmdCrossCheck C fTmd fPdf ktMax ζ x Q2 hRed

/-- Worked example: GPD forward limit reproduces the collinear PDF. -/
lemma gpd_forward_limit_example
    (M : Particles.Parton.GPD.Model Flavor)
    (fPdf : Particles.Parton.PDF.Pdf Flavor)
    (Q2 : ℝ)
    (hFwd : Particles.Parton.GPD.ForwardLimitToPdfAtScale M fPdf Q2)
    (i : Flavor) (x : ℝ) :
    M.H i x 0 0 = fPdf i x Q2 :=
  Particles.Parton.GPD.forwardLimit_bridge M fPdf Q2 hFwd i x

end Examples
end DIS
end Scattering
end QFT
end Physlib
