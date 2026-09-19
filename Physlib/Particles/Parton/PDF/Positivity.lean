/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.DataStructures.Matrix.PosSemidef
public import Physlib.Particles.Parton.PDF.Basic
/-!

# Leading-twist positivity and the Soffer bound

The three leading-twist quark distributions of a spin-1/2 hadron are entries of the forward
quark-hadron helicity-amplitude matrix. Positive semidefiniteness of that matrix is what the
probability interpretation of the amplitudes buys, and the positivity constraints the field
uses as hard bounds are its principal minors. This module derives them, rather than assuming
them: `f₁ ≥ 0`, `|g₁| ≤ f₁` and the Soffer bound `2 |h₁| ≤ f₁ + g₁` are theorems whose only
input is `Matrix.PosSemidef`.

## The helicity basis

At fixed flavour, momentum fraction `x` and scale `Q²`, the forward quark-hadron helicity
amplitudes assemble into a `4 × 4` real matrix indexed by the pair `(Λ, λ)` of nucleon and
quark helicity, in the order

| index   | `Λ` (nucleon) | `λ` (quark) |
| ------- | ------------- | ----------- |
| `idxPP` | `+1/2`        | `+1/2`      |
| `idxPM` | `+1/2`        | `-1/2`      |
| `idxMP` | `-1/2`        | `+1/2`      |
| `idxMM` | `-1/2`        | `-1/2`      |

The diagonal entry at `(Λ, λ)` is the number density of quarks of helicity `λ` in a nucleon of
helicity `Λ`, conventionally written `q_{λ/Λ}(x, Q²)`. Conservation of angular momentum along
the collision axis allows exactly one independent off-diagonal entry in this basis, the
double-helicity-flip amplitude connecting `(+1/2, +1/2)` with `(-1/2, -1/2)`, in which both the
quark and the nucleon helicity are reversed; that entry is the transversity distribution `h₁`.
Reading the matrix in the transversity basis instead turns the corresponding `2 × 2` minor into
the Soffer inequality, which is why Soffer's bound involves `h₁` and the *aligned* diagonal
entries.

Convention source: J. Soffer, Phys. Rev. Lett. **74** (1995) 1292 (arXiv:hep-ph/9409254); the
same basis with modern names for the distributions is used in the review of
Barone, Drago and Ratcliffe, Phys. Rept. **359** (2002) 1 (arXiv:hep-ph/0104283) and in the
TMD Handbook, arXiv:2304.03302, §2.

## Normalisation

`f1` and `g1` are the helicity averages over the nucleon spin state,

`f₁ = (1/2) ∑_{Λ, λ} q_{λ/Λ}`,  `g₁ = (1/2) ∑_{Λ, λ} (2Λ)(2λ) q_{λ/Λ}`,

so that no discrete-symmetry input is needed to state them. Parity invariance of the strong
interaction makes the two aligned diagonal entries equal and the two anti-aligned ones equal;
under that hypothesis, which is `IsParityInvariant` below, `f1` and `g1` collapse to the
familiar single-nucleon-helicity expressions `q_{+/+} ± q_{−/+}` (`f1_eq_of_parityInvariant`,
`g1_eq_of_parityInvariant`). The Soffer bound below does *not* use parity.

## Caveats

* Every statement here is at **fixed** `(x, Q²)`. Positivity is not an evolution invariant
  beyond leading order, and nothing in this module should be read as a claim that the bounds
  survive evolution to another scale.
* The matrix is **per flavour**. Positivity of a flavour-mixing combination (a singlet, say)
  is a statement about the corresponding block matrix and does not follow from these lemmas.

## Implementation notes

The matrix is taken over `ℝ`. The leading-twist unpolarized, helicity and transversity block
is real: hermiticity plus time-reversal invariance make the double-flip entry real. A
description that keeps the T-odd entries (Sivers and Boer-Mulders type, or the twist-3
structure that the Wandzura-Wilczek relation concerns) needs `Matrix _ _ ℂ`; the general
inequality this module rests on, `Matrix.PosSemidef.two_mul_abs_apply_le`, would then have to
be restated with `‖·‖` in place of `|·|`. That is deliberately deferred.

## Main results

- `Physlib.Particles.Parton.PDF.f1_nonneg`
- `Physlib.Particles.Parton.PDF.abs_g1_le_f1`
- `Physlib.Particles.Parton.PDF.soffer_bound`
- `Physlib.Particles.Parton.PDF.pdfOfSpinDensity_nonneg`
- `Physlib.Particles.Parton.PDF.assumptions_pdfOfSpinDensity`

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace Particles
namespace Parton
namespace PDF

variable {Flavor : Type}

/-- Basis index with nucleon helicity `+1/2` and quark helicity `+1/2`. -/
def idxPP : Fin 4 := 0

/-- Basis index with nucleon helicity `+1/2` and quark helicity `-1/2`. -/
def idxPM : Fin 4 := 1

/-- Basis index with nucleon helicity `-1/2` and quark helicity `+1/2`. -/
def idxMP : Fin 4 := 2

/-- Basis index with nucleon helicity `-1/2` and quark helicity `-1/2`. -/
def idxMM : Fin 4 := 3

/-- The leading-twist quark-nucleon spin-density matrix at one flavour, one momentum fraction
`x` and one scale `Q²`, in the helicity basis fixed in the module docstring.

The only field beyond the matrix itself is positive semidefiniteness, which is what the
probability interpretation of the forward helicity amplitudes provides. No further physics
hypothesis is bundled here: the positivity constraints below are consequences of this one
field. -/
structure SpinDensity where
  /-- The matrix of forward quark-nucleon helicity amplitudes, in the basis
  `idxPP, idxPM, idxMP, idxMM`. -/
  mat : Matrix (Fin 4) (Fin 4) ℝ
  /-- Positive semidefiniteness, i.e. the probability interpretation of the amplitudes. -/
  posSemidef : mat.PosSemidef

/-- The unpolarized leading-twist distribution `f₁`, the helicity average of the diagonal
number densities. At fixed `(x, Q²)`. -/
def f1 (ρ : SpinDensity) : ℝ :=
  (ρ.mat idxPP idxPP + ρ.mat idxPM idxPM + ρ.mat idxMP idxMP + ρ.mat idxMM idxMM) / 2

/-- The helicity distribution `g₁`, the helicity-weighted average of the diagonal number
densities. At fixed `(x, Q²)`. -/
def g1 (ρ : SpinDensity) : ℝ :=
  (ρ.mat idxPP idxPP - ρ.mat idxPM idxPM - ρ.mat idxMP idxMP + ρ.mat idxMM idxMM) / 2

/-- The transversity distribution `h₁`, the double-helicity-flip entry of the spin-density
matrix. At fixed `(x, Q²)`. -/
def h1 (ρ : SpinDensity) : ℝ := ρ.mat idxPP idxMM

/-- Defining expression for `f1`. -/
lemma f1_def (ρ : SpinDensity) :
    f1 ρ = (ρ.mat idxPP idxPP + ρ.mat idxPM idxPM + ρ.mat idxMP idxMP
      + ρ.mat idxMM idxMM) / 2 := rfl

/-- Defining expression for `g1`. -/
lemma g1_def (ρ : SpinDensity) :
    g1 ρ = (ρ.mat idxPP idxPP - ρ.mat idxPM idxPM - ρ.mat idxMP idxMP
      + ρ.mat idxMM idxMM) / 2 := rfl

/-- Defining expression for `h1`. -/
lemma h1_def (ρ : SpinDensity) : h1 ρ = ρ.mat idxPP idxMM := rfl

/-- `f₁ + g₁` is twice the aligned diagonal entry of the spin-density matrix. This is the
combination the Soffer bound constrains. -/
lemma f1_add_g1 (ρ : SpinDensity) :
    f1 ρ + g1 ρ = ρ.mat idxPP idxPP + ρ.mat idxMM idxMM := by
  rw [f1_def, g1_def]; ring

/-- `f₁ - g₁` is twice the anti-aligned diagonal entry of the spin-density matrix. -/
lemma f1_sub_g1 (ρ : SpinDensity) :
    f1 ρ - g1 ρ = ρ.mat idxPM idxPM + ρ.mat idxMP idxMP := by
  rw [f1_def, g1_def]; ring

/-- **Unpolarized positivity.** The unpolarized distribution is nonnegative, at fixed
`(x, Q²)`, as a consequence of positive semidefiniteness alone. -/
theorem f1_nonneg (ρ : SpinDensity) : 0 ≤ f1 ρ := by
  have hPP := ρ.posSemidef.apply_self_nonneg idxPP
  have hPM := ρ.posSemidef.apply_self_nonneg idxPM
  have hMP := ρ.posSemidef.apply_self_nonneg idxMP
  have hMM := ρ.posSemidef.apply_self_nonneg idxMM
  rw [f1_def]
  linarith

/-- **Helicity dominance.** The helicity distribution is bounded by the unpolarized one, at
fixed `(x, Q²)`. Equivalently, both `f₁ + g₁` and `f₁ - g₁` are nonnegative, since they are
sums of diagonal entries of a positive-semidefinite matrix. -/
theorem abs_g1_le_f1 (ρ : SpinDensity) : |g1 ρ| ≤ f1 ρ := by
  have hsum : 0 ≤ f1 ρ + g1 ρ := by
    have hPP := ρ.posSemidef.apply_self_nonneg idxPP
    have hMM := ρ.posSemidef.apply_self_nonneg idxMM
    rw [f1_add_g1]
    linarith
  have hdiff : 0 ≤ f1 ρ - g1 ρ := by
    have hPM := ρ.posSemidef.apply_self_nonneg idxPM
    have hMP := ρ.posSemidef.apply_self_nonneg idxMP
    rw [f1_sub_g1]
    linarith
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The positive-semidefiniteness content of the Soffer bound, before any discrete symmetry is
used: twice the double-helicity-flip entry is bounded by the sum of the two aligned diagonal
entries. This is `Matrix.PosSemidef.two_mul_abs_apply_le` at the indices `idxPP`, `idxMM`. -/
theorem two_mul_abs_h1_le_diag (ρ : SpinDensity) :
    2 * |h1 ρ| ≤ ρ.mat idxPP idxPP + ρ.mat idxMM idxMM :=
  ρ.posSemidef.two_mul_abs_apply_le idxPP idxMM

/-- **The Soffer bound.** `2 |h₁| ≤ f₁ + g₁` at fixed `(x, Q²)`, from positive
semidefiniteness of the spin-density matrix alone.

J. Soffer, *Positivity constraints for spin-dependent parton distributions*,
Phys. Rev. Lett. **74** (1995) 1292 (arXiv:hep-ph/9409254).

Stated multiplied out rather than as `|h₁| ≤ (f₁ + g₁) / 2`, so that it applies without field
side conditions. It is strictly stronger than `|h₁| ≤ f₁`, which is recovered in
`abs_h1_le_f1`. It is a statement at a fixed scale: preservation under evolution is a separate
question and is not addressed here. -/
theorem soffer_bound (ρ : SpinDensity) : 2 * |h1 ρ| ≤ f1 ρ + g1 ρ := by
  rw [f1_add_g1]
  exact two_mul_abs_h1_le_diag ρ

/-- The weaker transversity bound `|h₁| ≤ f₁`, obtained by combining the Soffer bound with
helicity dominance. Kept to record that Soffer implies it, and that the implication is
strict. -/
theorem abs_h1_le_f1 (ρ : SpinDensity) : |h1 ρ| ≤ f1 ρ := by
  have hs := soffer_bound ρ
  have hg := abs_g1_le_f1 ρ
  have hle : g1 ρ ≤ |g1 ρ| := le_abs_self _
  linarith

/-- Parity invariance of the spin-density matrix: reversing both helicities leaves a diagonal
entry unchanged. This is a property of the strong interaction, stated here as a hypothesis to
be supplied rather than a field of `SpinDensity`, because none of the positivity bounds above
need it. -/
def IsParityInvariant (ρ : SpinDensity) : Prop :=
  ρ.mat idxMM idxMM = ρ.mat idxPP idxPP ∧ ρ.mat idxMP idxMP = ρ.mat idxPM idxPM

/-- Under parity invariance the helicity-averaged `f₁` reduces to the familiar
single-nucleon-helicity expression `q_{+/+} + q_{−/+}`. -/
lemma f1_eq_of_parityInvariant (ρ : SpinDensity) (h : IsParityInvariant ρ) :
    f1 ρ = ρ.mat idxPP idxPP + ρ.mat idxPM idxPM := by
  rw [f1_def, h.1, h.2]; ring

/-- Under parity invariance the helicity-averaged `g₁` reduces to the familiar
single-nucleon-helicity expression `q_{+/+} - q_{−/+}`. -/
lemma g1_eq_of_parityInvariant (ρ : SpinDensity) (h : IsParityInvariant ρ) :
    g1 ρ = ρ.mat idxPP idxPP - ρ.mat idxPM idxPM := by
  rw [g1_def, h.1, h.2]; ring

/-! ### Bridge to the collinear PDF object model

A family of spin-density matrices, one per flavour, momentum fraction and scale, induces a
`Pdf`. For such an induced density the `nonneg` field of `PDF.Assumptions` is a theorem rather
than a hypothesis; `assumptions_pdfOfSpinDensity` assembles the full bundle from the three
remaining, purely structural, fields.
-/

/-- The unpolarized collinear PDF induced by a family of spin-density matrices. -/
def pdfOfSpinDensity (ρ : Flavor → ℝ → ℝ → SpinDensity) : Pdf Flavor :=
  fun i x Q2 => f1 (ρ i x Q2)

/-- The helicity distribution `g₁` induced by a family of spin-density matrices, as a
collinear distribution with the same index conventions as `Pdf`. It is not itself a `Pdf`
in the probabilistic sense: it is not nonnegative. -/
def helicityPdfOfSpinDensity (ρ : Flavor → ℝ → ℝ → SpinDensity) : Pdf Flavor :=
  fun i x Q2 => g1 (ρ i x Q2)

/-- The transversity distribution `h₁` induced by a family of spin-density matrices, as a
collinear distribution with the same index conventions as `Pdf`. -/
def transversityPdfOfSpinDensity (ρ : Flavor → ℝ → ℝ → SpinDensity) : Pdf Flavor :=
  fun i x Q2 => h1 (ρ i x Q2)

/-- **Positivity of an induced PDF is a theorem, not an assumption.** Compare the `nonneg`
field of `PDF.Assumptions`, which posits it. Note that no restriction to `x ∈ [0, 1]` is
needed: the bound holds wherever the density matrix is defined. -/
theorem pdfOfSpinDensity_nonneg (ρ : Flavor → ℝ → ℝ → SpinDensity) (i : Flavor) (x Q2 : ℝ) :
    0 ≤ pdfOfSpinDensity ρ i x Q2 :=
  f1_nonneg (ρ i x Q2)

/-- Helicity dominance for an induced pair of distributions, pointwise in `(x, Q²)`. -/
theorem abs_helicityPdf_le_pdf (ρ : Flavor → ℝ → ℝ → SpinDensity) (i : Flavor) (x Q2 : ℝ) :
    |helicityPdfOfSpinDensity ρ i x Q2| ≤ pdfOfSpinDensity ρ i x Q2 :=
  abs_g1_le_f1 (ρ i x Q2)

/-- The Soffer bound for an induced triple of distributions, pointwise in `(x, Q²)`. -/
theorem soffer_bound_pdf (ρ : Flavor → ℝ → ℝ → SpinDensity) (i : Flavor) (x Q2 : ℝ) :
    2 * |transversityPdfOfSpinDensity ρ i x Q2| ≤
      pdfOfSpinDensity ρ i x Q2 + helicityPdfOfSpinDensity ρ i x Q2 :=
  soffer_bound (ρ i x Q2)

/-- The structural assumptions on a family of spin-density matrices that remain once
positivity has been derived: support, measurability and integrability of the induced
unpolarized density. Compare `PDF.Assumptions`, which has a fourth field `nonneg`. -/
structure SpinDensityAssumptions (ρ : Flavor → ℝ → ℝ → SpinDensity) : Prop where
  /-- The induced density vanishes outside the physical support domain. -/
  support : ∀ i x Q2, x < 0 ∨ 1 < x → f1 (ρ i x Q2) = 0
  /-- The induced density is almost-everywhere strongly measurable in `x`. -/
  measurable : ∀ i Q2, MeasureTheory.AEStronglyMeasurable (fun x : ℝ => f1 (ρ i x Q2))
  /-- The Mellin-moment integrands of the induced density are integrable. -/
  momentIntegrable : ∀ n i Q2,
    MeasureTheory.Integrable (fun x : ℝ => x ^ n * f1 (ρ i x Q2))

/-- A family of spin-density matrices satisfying the structural assumptions induces a
collinear PDF satisfying the full `PDF.Assumptions` bundle, with the `nonneg` field
**discharged** by `pdfOfSpinDensity_nonneg` rather than assumed. -/
theorem assumptions_pdfOfSpinDensity (ρ : Flavor → ℝ → ℝ → SpinDensity)
    (h : SpinDensityAssumptions ρ) : Assumptions (pdfOfSpinDensity ρ) :=
  { support := fun i x Q2 hx => h.support i x Q2 hx
    nonneg := fun i x Q2 _ _ => pdfOfSpinDensity_nonneg ρ i x Q2
    measurable := fun i Q2 => h.measurable i Q2
    momentIntegrable := fun n i Q2 => h.momentIntegrable n i Q2 }

end PDF
end Parton
end Particles
end Physlib
