/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Exclusive.DVMP.Basic
/-!

# DVMP Channel Interfaces

This module defines channel-weighted observable interfaces and helicity
consistency assumption schemas.

-/

@[expose] public section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Exclusive
namespace DVMP

/-- Channel weight convention by meson kind. -/
def kindWeight : MesonKind → ℝ
  | MesonKind.vector => 1
  | MesonKind.pseudoscalar => -1

/-- Channel-weighted DVMP observable template. -/
def channelObservable
    {Meson : Type}
    (ch : Channel Meson)
    (T : TFF)
    (xi t Q2 : ℝ) : ℝ :=
  kindWeight ch.kind * dvmpObservable T xi t Q2

lemma channelObservable_vector
    {Meson : Type}
    (ch : Channel Meson)
    (T : TFF)
    (xi t Q2 : ℝ)
    (hKind : ch.kind = MesonKind.vector) :
    channelObservable ch T xi t Q2 = dvmpObservable T xi t Q2 := by
  simp [channelObservable, kindWeight, hKind]

lemma channelObservable_pseudoscalar
    {Meson : Type}
    (ch : Channel Meson)
    (T : TFF)
    (xi t Q2 : ℝ)
    (hKind : ch.kind = MesonKind.pseudoscalar) :
    channelObservable ch T xi t Q2 = -dvmpObservable T xi t Q2 := by
  simp [channelObservable, kindWeight, hKind]

/-- Helicity-consistency assumption bundle for channel interfaces. -/
structure HelicityConsistencyAssumptions (T : TFF) : Prop where
  bounded : ∀ xi t, |T.transverse xi t| ≤ |T.longitudinal xi t| + 1

lemma helicityConsistency_eval
    (T : TFF)
    (h : HelicityConsistencyAssumptions T)
    (xi t : ℝ) :
    |T.transverse xi t| ≤ |T.longitudinal xi t| + 1 :=
  h.bounded xi t

end DVMP
end Exclusive
end DIS
end Scattering
end QFT
end Physlib
