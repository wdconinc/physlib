/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.DIS.LO
/-!

# Power Corrections Interfaces (Stage 12)

This module defines target-mass and higher-twist correction interfaces and
reduction lemmas to baseline LO observables.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Corrections

/-- Target-mass correction term interface. -/
abbrev TargetMassCorrection : Type := ℝ → ℝ → ℝ

/-- Higher-twist correction term interface. -/
abbrev HigherTwistCorrection : Type := ℝ → ℝ → ℝ

/-- Corrected observable decomposition into baseline + corrections. -/
def correctedObservable
    (F : ℝ → ℝ → ℝ)
    (δTM : TargetMassCorrection)
    (δHT : HigherTwistCorrection)
    (x Q2 : ℝ) : ℝ :=
  F x Q2 + δTM x Q2 + δHT x Q2

/-- Decomposition identity for corrected observables. -/
lemma correctedObservable_decompose
    (F : ℝ → ℝ → ℝ)
    (δTM : TargetMassCorrection)
    (δHT : HigherTwistCorrection)
    (x Q2 : ℝ) :
    correctedObservable F δTM δHT x Q2
      = F x Q2 + δTM x Q2 + δHT x Q2 :=
  rfl

/-- Zero-correction recovery theorem to baseline observable. -/
lemma correctedObservable_eq_baseline_of_zero
    (F : ℝ → ℝ → ℝ)
  (δTM : TargetMassCorrection)
  (δHT : HigherTwistCorrection)
    (x Q2 : ℝ)
    (hTM : δTM x Q2 = 0)
  (hHT : δHT x Q2 = 0) :
    correctedObservable F δTM δHT x Q2 = F x Q2 := by
  simp [correctedObservable, hTM, hHT]

/-- Bounded-corrections assumption bundle for stability interfaces. -/
structure BoundedCorrections
    (δTM : TargetMassCorrection)
    (δHT : HigherTwistCorrection) : Prop where
  tmBound : ∀ x Q2, |δTM x Q2| ≤ 1
  htBound : ∀ x Q2, |δHT x Q2| ≤ 1

end Corrections
end DIS
end Scattering
end QFT
end Physlib
