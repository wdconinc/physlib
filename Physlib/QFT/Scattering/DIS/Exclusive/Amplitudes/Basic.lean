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

/-- Gauge/current-conservation assumption bundle for helicity amplitudes. -/
structure GaugeAssumptions (A : HelicityAmplitude) : Type where
  conserved : Prop
  hConserved : conserved

/-- Helicity/parity assumption bundle. -/
structure HelicityAssumptions (A : HelicityAmplitude) : Prop where
  parityRelation : ∀ lamIn lamOut xi t,
    A.amp lamIn lamOut xi t = A.amp (-lamIn) (-lamOut) xi t

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
