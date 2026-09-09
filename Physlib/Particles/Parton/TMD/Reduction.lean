/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.TMD.Basic
public import Physlib.QFT.Factorization.DIS.LO
/-!

# TMD Reduction and Cross-Checks

This module formalizes TMD-to-PDF reduction interfaces and a factorization
cross-check theorem.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace Particles
namespace Parton
namespace TMD

variable {Flavor : Type}

/-- Collinear proxy obtained from truncated `kT` integration. -/
def collinearFromTmd
    (fTmd : Tmd Flavor)
    (ktMax ζ : ℝ) : PDF.Pdf Flavor :=
  fun i x Q2 => integrateKT fTmd i x Q2 ζ ktMax

/-- Reduction interface stating that integrated TMD recovers a collinear PDF. -/
def IntegratesToPdf
    (fTmd : Tmd Flavor)
    (fPdf : PDF.Pdf Flavor)
    (ktMax ζ : ℝ) : Prop :=
  ∀ i x Q2, integrateKT fTmd i x Q2 ζ ktMax = fPdf i x Q2

/-- Canonical reduction theorem wrapper. -/
lemma tmd_to_pdf_reduction
    (fTmd : Tmd Flavor)
    (fPdf : PDF.Pdf Flavor)
    (ktMax ζ : ℝ)
    (hRed : IntegratesToPdf fTmd fPdf ktMax ζ) :
    ∀ i x Q2, collinearFromTmd fTmd ktMax ζ i x Q2 = fPdf i x Q2 :=
  hRed

/-- Observable cross-check: replacing a PDF by its integrated TMD proxy
preserves the LO structure function under the reduction hypothesis. -/
lemma loStructureFunction_tmdCrossCheck [Fintype Flavor]
    (C : QFT.Factorization.DIS.HardKernel Flavor)
    (fTmd : Tmd Flavor)
    (fPdf : PDF.Pdf Flavor)
    (ktMax ζ x Q2 : ℝ)
    (hRed : IntegratesToPdf fTmd fPdf ktMax ζ) :
    QFT.Factorization.DIS.loStructureFunction C (collinearFromTmd fTmd ktMax ζ) x Q2
      = QFT.Factorization.DIS.loStructureFunction C fPdf x Q2 := by
  refine Finset.sum_congr rfl ?_
  intro i _
  unfold QFT.Factorization.DIS.loChannel
  apply QFT.Factorization.Convolution.convolveAt_congr
      (fun x' z => C i x' z Q2)
      (fun x' z => C i x' z Q2)
      (fun z => collinearFromTmd fTmd ktMax ζ i z Q2)
      (fun z => fPdf i z Q2)
      x
  intro z
  simp [QFT.Factorization.Convolution.integrand, collinearFromTmd, hRed i z Q2]

end TMD
end Parton
end Particles
end Physlib
