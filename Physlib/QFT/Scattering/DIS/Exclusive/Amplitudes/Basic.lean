/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Exclusive.Kinematics.Basic
/-!

# Exclusive Amplitude Interfaces

This module introduces abstract amplitude interfaces for DVCS and DVMP channels
with explicit gauge/helicity assumption bundles.

-/

@[expose] public section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Exclusive
namespace Amplitudes

/-- Helicity-amplitude interface indexed by incoming/outgoing helicities. -/
structure HelicityAmplitude where
  amp : ℤ → ℤ → ℝ → ℝ → ℝ

/-- Scalar DVCS amplitude interface over `(xi, t, Q2)`. -/
structure DVCSAmplitude where
  scalar : ℝ → ℝ → ℝ → ℝ

/-- Scalar DVMP amplitude interface over meson channel and `(xi, t, Q2)`. -/
structure DVMPAmplitude (Meson : Type) where
  scalar : Meson → ℝ → ℝ → ℝ → ℝ

-- A `GaugeAssumptions` bundle used to sit here, with fields `conserved : Prop` and
-- `hConserved : conserved`. That pair asserts nothing (instantiate `conserved := True`),
-- it had no dependent declaration anywhere in the repository, and the statement it stood
-- in for — current conservation, `q_μ M^μ = 0` — cannot be written against
-- `HelicityAmplitude`, whose `amp` field carries helicity labels and kinematics but no
-- Lorentz index. The bundle has been removed rather than restated.

/-- Helicity/parity assumption bundle. -/
structure HelicityAssumptions (A : HelicityAmplitude) : Prop where
  parityRelation : ∀ lamIn lamOut xi t,
    A.amp lamIn lamOut xi t = A.amp (-lamIn) (-lamOut) xi t

/-- The parity relation, read as an invariance of the amplitude under the simultaneous
helicity flip. -/
lemma HelicityAssumptions.amp_neg_neg (A : HelicityAmplitude) (h : HelicityAssumptions A) :
    (fun lamIn lamOut => A.amp (-lamIn) (-lamOut)) = A.amp := by
  funext lamIn lamOut xi t
  exact (h.parityRelation lamIn lamOut xi t).symm

/-- A concrete model of the parity bundle: any amplitude that depends on the helicities
only through their product satisfies the parity relation. This exhibits a witness, so the
bundle is satisfiable, and the dependence on `lamIn * lamOut` shows it is not satisfied
only by helicity-independent amplitudes. -/
lemma helicityAssumptions_of_product (g : ℤ → ℝ → ℝ → ℝ) :
    HelicityAssumptions ⟨fun lamIn lamOut xi t => g (lamIn * lamOut) xi t⟩ := by
  refine ⟨fun lamIn lamOut xi t => ?_⟩
  show g (lamIn * lamOut) xi t = g (-lamIn * -lamOut) xi t
  rw [neg_mul_neg]

/-- Rescaling interface for amplitude-model bookkeeping. -/
def rescale (a : ℝ) (A : DVCSAmplitude) : DVCSAmplitude where
  scalar := fun xi t Q2 => a * A.scalar xi t Q2

lemma rescale_apply (a : ℝ) (A : DVCSAmplitude) (xi t Q2 : ℝ) :
    (rescale a A).scalar xi t Q2 = a * A.scalar xi t Q2 :=
  rfl

/-- Crossing-even interface for DVCS amplitudes. -/
def IsCrossingEven (A : DVCSAmplitude) : Prop :=
  ∀ xi t Q2, A.scalar (-xi) t Q2 = A.scalar xi t Q2

lemma crossingEven_eval
    (A : DVCSAmplitude)
    (hEven : IsCrossingEven A)
    (xi t Q2 : ℝ) :
    A.scalar (-xi) t Q2 = A.scalar xi t Q2 :=
  hEven xi t Q2

end Amplitudes
end Exclusive
end DIS
end Scattering
end QFT
end Physlib
