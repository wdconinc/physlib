/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.Renormalization
public import Physlib.QFT.QCD.SUNDerivation
/-!

# One-Loop QCD Beta Infrastructure

This module records one-loop diagram-class pole contributions and assembles them
into the one-loop QCD beta coefficient.

The theorem layer is interface-first: coefficients are supplied via explicit
contracts, allowing later replacement by full Feynman-integral proofs.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace QCD
namespace OneLoopBeta

open Renormalization

/-- Primitive one-loop pole contributions grouped by diagram class. -/
structure PrimitivePoles : Type where
  /-- Gluon-loop contribution to the coupling pole. -/
  gluon : ℝ
  /-- Ghost-loop contribution to the coupling pole. -/
  ghost : ℝ
  /-- Quark-loop contribution to the coupling pole. -/
  quark : ℝ

/-- Gauge-sector (gluon + ghost) pole contribution. -/
def PrimitivePoles.gaugeSector (p : PrimitivePoles) : ℝ :=
  p.gluon + p.ghost

/-- Total one-loop coupling pole contribution. -/
def PrimitivePoles.total (p : PrimitivePoles) : ℝ :=
  p.gluon + p.ghost + p.quark

/-- One-loop coefficient contracts in a color-factor basis. -/
structure PrimitivePoleAssumptions (cf : ColorFactors) (p : PrimitivePoles) : Prop where
  /-- Gluon contribution coefficient contract. -/
  gluon_eq : p.gluon = (5 / 3) * cf.cA
  /-- Ghost contribution coefficient contract. -/
  ghost_eq : p.ghost = 2 * cf.cA
  /-- Quark contribution coefficient contract. -/
  quark_eq : p.quark = -(4 / 3) * cf.tF * cf.nF

/-- Gauge-sector coefficient assembly from primitive contributions. -/
lemma gaugeSector_eq
    (cf : ColorFactors)
    (p : PrimitivePoles)
    (h : PrimitivePoleAssumptions cf p) :
    p.gaugeSector = (11 / 3) * cf.cA := by
  unfold PrimitivePoles.gaugeSector
  rw [h.gluon_eq, h.ghost_eq]
  ring

/-- Total one-loop assembly reproduces the `beta0` color-factor expression. -/
lemma totalPole_eq_beta0
    (cf : ColorFactors)
    (p : PrimitivePoles)
    (h : PrimitivePoleAssumptions cf p) :
    p.total = beta0 cf := by
  unfold PrimitivePoles.total beta0
  rw [h.gluon_eq, h.ghost_eq, h.quark_eq]
  ring

/-- Link between assembled one-loop pole total and renormalization coupling pole. -/
structure OneLoopRenormalizationLink
    (ms : MSLikeRenormalizationData)
    (p : PrimitivePoles) : Prop where
  /-- Coupling pole equals minus one half of the assembled one-loop pole total. -/
  couplingPole_eq_neg_half_total : ms.couplingPole = -p.total / 2

/-- First beta-function theorem from one-loop poles through renormalization input. -/
lemma beta0_from_oneLoopPoles
    (cf : ColorFactors)
    (ms : MSLikeRenormalizationData)
    (p : PrimitivePoles)
    (hPole : PrimitivePoleAssumptions cf p)
    (hLink : OneLoopRenormalizationLink ms p) :
    beta0 cf = beta0FromCouplingPole ms.couplingPole := by
  have hTotal : p.total = beta0 cf := totalPole_eq_beta0 cf p hPole
  unfold beta0FromCouplingPole
  rw [hLink.couplingPole_eq_neg_half_total, hTotal]
  ring

/-- Group-parameterized corollary of `beta0_from_oneLoopPoles`. -/
lemma beta0Of_from_oneLoopPoles
    (G : Type) [HasColorInvariants G]
    (nF : ℝ)
    (ms : MSLikeRenormalizationData)
    (p : PrimitivePoles)
    (hPole : PrimitivePoleAssumptions (colorFactorsOf G nF) p)
    (hLink : OneLoopRenormalizationLink ms p) :
    beta0Of G nF = beta0FromCouplingPole ms.couplingPole := by
  simpa [beta0Of] using
    beta0_from_oneLoopPoles (cf := colorFactorsOf G nF) (ms := ms) (p := p) hPole hLink

/-- Step-4 canonical one-loop theorem in the `SU(Nc)` color basis.

Given one-loop primitive-pole contracts and a coupling-pole link, the
renormalization-reconstructed coefficient equals the standard `SU(Nc)`
`beta0` expression. -/
lemma beta0_suN_from_oneLoopPoles
    (nC nF : ℝ)
    (ms : MSLikeRenormalizationData)
    (p : PrimitivePoles)
    (hPole : PrimitivePoleAssumptions (suNColorFactors nC nF) p)
    (hLink : OneLoopRenormalizationLink ms p) :
    beta0 (suNColorFactors nC nF) = beta0FromCouplingPole ms.couplingPole := by
  simpa using beta0_from_oneLoopPoles
    (cf := suNColorFactors nC nF) (ms := ms) (p := p) hPole hLink

/-- Group-level `SU(Nc)` corollary of `beta0_suN_from_oneLoopPoles` through the
representation-derived `beta0Of` interface. -/
lemma beta0Of_suN_from_oneLoopPoles
    (nC nF : ℝ)
    (ms : MSLikeRenormalizationData)
    (p : PrimitivePoles)
    (hPole : PrimitivePoleAssumptions (suNColorFactors nC nF) p)
    (hLink : OneLoopRenormalizationLink ms p) :
    beta0Of (SUN nC) nF = beta0FromCouplingPole ms.couplingPole := by
  calc
    beta0Of (SUN nC) nF
        = beta0 (suNColorFactors nC nF) :=
          RepresentationColor.beta0Of_suN_eq_from_representation nC nF
    _ = beta0FromCouplingPole ms.couplingPole :=
          beta0_suN_from_oneLoopPoles nC nF ms p hPole hLink

end OneLoopBeta
end QCD
end QFT
end Physlib
