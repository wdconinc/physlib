/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.PDF.Basic
public import Physlib.Particles.Parton.TMD.Reduction
public import Physlib.Particles.Parton.GPD.Basic
/-!

# Unified Parton Interface

This module defines a shared API wrapper over PDF, TMD, and GPD objects.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace Particles
namespace Parton
namespace Unified

variable {Flavor : Type}

/-- Unified container for collinear, TMD, and GPD objects. -/
structure Model (Flavor : Type) : Type where
  pdf : PDF.Pdf Flavor
  tmd : TMD.Tmd Flavor
  gpd : GPD.Model Flavor
  ktMax : ℝ
  ζ : ℝ

/-- Structural assumptions and bridge assumptions for a unified model. -/
structure Assumptions (U : Model Flavor) : Prop where
  pdfStruct : PDF.Assumptions U.pdf
  tmdStruct : TMD.Assumptions U.tmd
  gpdStruct : GPD.Assumptions U.gpd
  tmdToPdf : TMD.IntegratesToPdf U.tmd U.pdf U.ktMax U.ζ
  gpdForward : ∀ Q2, GPD.ForwardLimitToPdfAtScale U.gpd U.pdf Q2

/-- Uniform API accessor for collinear distributions. -/
def pdfAt (U : Model Flavor) (i : Flavor) (x Q2 : ℝ) : ℝ :=
  U.pdf i x Q2

/-- Uniform API accessor for TMD distributions. -/
def tmdAt (U : Model Flavor) (i : Flavor) (x kT Q2 ζ : ℝ) : ℝ :=
  U.tmd i x kT Q2 ζ

/-- Uniform API accessor for GPD `H`. -/
def gpdHAt (U : Model Flavor) (i : Flavor) (x xi t : ℝ) : ℝ :=
  U.gpd.H i x xi t

/-- Uniform API accessor for GPD `E`. -/
def gpdEAt (U : Model Flavor) (i : Flavor) (x xi t : ℝ) : ℝ :=
  U.gpd.E i x xi t

/-- Uniform moment wrapper using the PDF Mellin interface. -/
def moment (U : Model Flavor) (n : ℕ) (i : Flavor) (Q2 : ℝ) : ℝ :=
  PDF.mellinMoment U.pdf n i Q2

/-- Uniform collinear reduction wrapper for TMDs. -/
def tmdCollinear (U : Model Flavor) : PDF.Pdf Flavor :=
  TMD.collinearFromTmd U.tmd U.ktMax U.ζ

/-- Sum-rule API shape reusing the PDF moment interface. -/
structure SumRuleInterface [Fintype Flavor] (U : Model Flavor) : Type where
  momentum : ∀ Q2, (∑ i, moment U 1 i Q2) = 1
  valenceTarget : Flavor → ℝ
  valence : ∀ i Q2, moment U 0 i Q2 = valenceTarget i

end Unified
end Parton
end Particles
end Physlib
