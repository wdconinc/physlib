/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.Polarized.Basic
/-!

# Polarized Sum Rules

This module states the polarized DIS sum rules as what they are: identities for the first
moments `Γ₁(Q²) = ∫₀¹ dx g₁(x, Q²)` and `Γ₂(Q²) = ∫₀¹ dx g₂(x, Q²)`.

- `BjorkenSumRule` — the proton-neutron non-singlet identity, with the nucleon axial
  charge ratio `g_A/g_V` and the perturbative correction series as explicit inputs rather
  than hard-coded numbers.
- `EllisJaffeSumRule` — the proton-only statement. It is *conditional* on a vanishing
  strange-quark polarization, and that hypothesis is an explicit field, because the sum
  rule is violated experimentally: stating it unconditionally would formalize a falsehood
  about the physical proton.
- `BurkhardtCottingham` — `Γ₂(Q²) = 0`.

**Moment convention.** `firstMomentG1` and `firstMomentG2` carry weight `x⁰`: they are
plain integrals over `[0, 1]`. In terms of `Physlib.Particles.Parton.PDF.mellinMoment`,
where `mellinMoment f n = ∫₀¹ dx xⁿ f`, that is `n = 0`. In terms of the literature's
`n`-th moment `∫₀¹ dx xⁿ⁻¹ g`, it is `n = 1`. Every statement below uses the weight-`x⁰`
convention and no other.

## References

- J. D. Bjorken, Phys. Rev. **148** (1966) 1467.
- J. Ellis and R. L. Jaffe, Phys. Rev. D **9** (1974) 1444.
- H. Burkhardt and W. N. Cottingham, Ann. Phys. **56** (1970) 453.
- S. Wandzura and F. Wilczek, Phys. Lett. B **72** (1977) 195.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace Polarized

/-! ## Bjorken sum rule -/

/-- The Bjorken sum rule for a proton/neutron pair of polarized structure functions.

`Γ₁ᵖ(Q²) − Γ₁ⁿ(Q²) = (1/6) |g_A/g_V| (1 + Δ(Q²))`, an identity for the non-singlet
combination of first moments, tied to the nucleon axial charge.

Both `gAOverGV` and the perturbative correction `correction` are inputs rather than
derived quantities. `gAOverGV` is a nucleon matrix element that this repository does not
yet formalize (see the note at the end of the module); `correction` is the QCD radiative
series, which is scheme- and order-dependent, so it is kept an abstract function of `Q²`
rather than a hard-coded expansion. -/
structure BjorkenSumRule (Gp Gn : StructureFunctions) (gAOverGV : ℝ)
    (correction : ℝ → ℝ) : Prop where
  /-- The non-singlet first-moment identity, at every scale. -/
  bjorken : ∀ Q2, firstMomentG1 Gp Q2 - firstMomentG1 Gn Q2
    = (1 / 6) * |gAOverGV| * (1 + correction Q2)

/-- The experimental use of the Bjorken sum rule: it determines `|g_A/g_V|` from the
measured non-singlet first moment, once the perturbative correction is known.

This is an inversion of the sum rule, not a restatement of it. -/
lemma abs_gAOverGV_eq_of_bjorken
    (Gp Gn : StructureFunctions) (gAOverGV : ℝ) (correction : ℝ → ℝ)
    (hB : BjorkenSumRule Gp Gn gAOverGV correction)
    (Q2 : ℝ) (hCorr : 1 + correction Q2 ≠ 0) :
    |gAOverGV|
      = 6 * (firstMomentG1 Gp Q2 - firstMomentG1 Gn Q2) / (1 + correction Q2) := by
  have h := hB.bjorken Q2
  rw [eq_div_iff hCorr, h]
  ring

/-! ## Ellis-Jaffe sum rule -/

/-- The Ellis-Jaffe sum rule for the proton.

Unlike the Bjorken sum rule this is *not* a consequence of current algebra alone: it needs
the extra hypothesis that the strange-quark polarization vanishes. That hypothesis is the
field `strange_unpolarized`, and it is what the measurement of `Γ₁ᵖ` falsified — the
"proton spin problem". Formalizing the conclusion without carrying the hypothesis would
state something false about the physical proton.

The structure therefore carries the leading-twist flavour decomposition of the first
moment as a separate field, so that `strange_unpolarized` is a hypothesis that does real
work on it, rather than a free-floating equation about an unconstrained function.

`deltaU`, `deltaD`, `deltaS` are the scale-dependent quark helicity charges
`Δq(Q²) = ∫₀¹ dx [Δq(x, Q²) + Δq̄(x, Q²)]`, and the quark charge weights are
`e_u² = 4/9`, `e_d² = e_s² = 1/9`. -/
structure EllisJaffeSumRule (Gp : StructureFunctions)
    (deltaU deltaD deltaS : ℝ → ℝ) (correction : ℝ → ℝ) : Prop where
  /-- Leading-twist quark-parton decomposition of the proton first moment,
  `Γ₁ᵖ = ½ Σ_q e_q² Δq`, dressed by the perturbative correction. -/
  moment_decomposition : ∀ Q2,
    firstMomentG1 Gp Q2
      = (1 / 2) * ((4 / 9) * deltaU Q2 + (1 / 9) * deltaD Q2 + (1 / 9) * deltaS Q2)
        * (1 + correction Q2)
  /-- The SU(3)-symmetric hypothesis of a vanishing strange-quark polarization. This is
  the assumption that experiment rejects. -/
  strange_unpolarized : ∀ Q2, deltaS Q2 = 0

/-- The Ellis-Jaffe prediction: under a vanishing strange polarization, the proton first
moment is fixed by the up and down helicity charges alone.

`Γ₁ᵖ(Q²) = (1/18) (4 Δu(Q²) + Δd(Q²)) (1 + Δ(Q²))`. -/
lemma ellisJaffe_prediction
    (Gp : StructureFunctions) (deltaU deltaD deltaS correction : ℝ → ℝ)
    (hEJ : EllisJaffeSumRule Gp deltaU deltaD deltaS correction)
    (Q2 : ℝ) :
    firstMomentG1 Gp Q2
      = (1 / 18) * (4 * deltaU Q2 + deltaD Q2) * (1 + correction Q2) := by
  rw [hEJ.moment_decomposition Q2, hEJ.strange_unpolarized Q2]
  ring

/-! ## Burkhardt-Cottingham sum rule -/

/-- The Burkhardt-Cottingham sum rule, `∫₀¹ dx g₂(x, Q²) = 0` at every scale.

It follows from the analytic structure of the forward virtual Compton amplitude rather
than from the parton model, so at this level it is a hypothesis; `g2WW` below gives a
family of structure functions that provably satisfies it. -/
structure BurkhardtCottingham (G : StructureFunctions) : Prop where
  /-- The vanishing of the first moment of `g₂`, at every scale. -/
  bc : ∀ Q2, firstMomentG2 G Q2 = 0

/-! ## Remaining targets

Two statements in this family are deliberately absent.

- **Sum-rule conservation under evolution.** That the momentum and valence sum rules hold
  at every scale, given that they hold at one and that the DGLAP kernels satisfy
  `Σ_i ∫₀¹ dx x P_ij(x) = 0`, requires the evolution equation to be stated correctly
  first. The current `dglapRhsLogScale` applies `alphaS` without the conventional
  `1/(2π)`; fixing that is the subject of the `task/e2-dglap-wellposedness` branch, and
  this theorem should be added on top of it, not before it.
- **Derivation of the Bjorken sum rule.** `gAOverGV` is a nucleon axial-current matrix
  element. Once the repository formalizes that matrix element, `BjorkenSumRule` becomes
  derivable rather than assumed; until then it stays an input and is documented as
  external.
-/

end Polarized
end DIS
end Scattering
end QFT
end Physlib
