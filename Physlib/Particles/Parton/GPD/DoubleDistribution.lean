/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.GPD.Basic
/-!

# Double Distributions and the D-term

This module introduces the double-distribution representation of a generalized parton
distribution, together with the D-term, and the GPD it induces.

## The representation

Lorentz covariance forces the `x`-moments of a GPD to be form factors of local twist-2
operators, hence polynomials in the momentum transfer. The constructive statement of
that fact is the double-distribution representation (Müller *et al.*, Fortschr. Phys.
**42** (1994) 101; Radyushkin, Phys. Rev. D **56** (1997) 5524):

```text
H(x, ξ, t) = ∫∫ dβ dα δ(x - β - αξ) [ F(β, α, t) + ξ δ(β) D(α, t) ]
```

with `F` supported on the rhombus `|β| + |α| ≤ 1`.

Two features of that formula are load-bearing and are recorded as *fields* of the
structures below rather than derived:

* `DoubleDistribution.alphaSymm`, the symmetry `F(β, α, t) = F(β, -α, t)`. Without it the
  moments of `H` are general polynomials in `ξ` rather than *even* polynomials, and the
  identification of the top coefficient with the D-term collapses (Radyushkin, §3).
* `DTerm.odd`, the oddness `D(-u, t) = -D(u, t)`. The D-term is expanded in odd
  Gegenbauer polynomials `C_{2k+1}^{3/2}`; its oddness is what confines it to the
  even-power slots of the moment polynomial (Polyakov and Weiss, Phys. Rev. D **60**
  (1999) 114017).

## The one-dimensional form used here

Delta functions are awkward in Lean, so the `α`-integral is done by hand. For `ξ ≠ 0`,
solving `x = β + αξ` for `α` gives `α = (x - β)/ξ` with Jacobian `1/|ξ|`, and the
D-term piece `ξ δ(β) D(α, t)` collapses to `sign ξ · D(x/ξ, t)`:

```text
H(x, ξ, t) = (1/|ξ|) ∫ dβ F(β, (x - β)/ξ, t) + (ξ/|ξ|) D(x/ξ, t)     (ξ ≠ 0)
H(x, 0, t) = ∫ dα F(x, α, t)                                          (ξ = 0)
```

The `ξ = 0` branch is separate because of the `1/|ξ|`; it is the forward limit, and
`forwardLimit_ofDoubleDistribution` below discharges the GPD forward-limit relation for
it. Note that the D-term carries `ξ/|ξ|` and *not* `1/|ξ|`: the explicit factor `ξ`
multiplying `δ(β) D(α, t)` in the representation is what puts the D-term in the
`ξ^(n+1)` slot of the moment polynomial rather than the `ξ^n` slot.

## Skewness range

The induced GPD vanishes outside `|x| ≤ 1` only for physical skewness `|ξ| ≤ 1`; for
`|ξ| > 1` the rhombus is stretched past the unit interval. The hypothesis is therefore
carried explicitly in `gpdOfDoubleDistribution_eq_zero_of_one_lt_abs`.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace Particles
namespace Parton
namespace GPD

variable {Flavor : Type}

/-- A double distribution `F(β, α, t)` supported on the rhombus `|β| + |α| ≤ 1`. -/
structure DoubleDistribution (Flavor : Type) : Type where
  /-- The double distribution itself, indexed by flavor and `(β, α, t)`. -/
  F : Flavor → ℝ → ℝ → ℝ → ℝ
  /-- Support on the rhombus `|β| + |α| ≤ 1`. -/
  support : ∀ i β α t, 1 < |β| + |α| → F i β α t = 0
  /-- Symmetry in `α`, the source of the evenness of GPD moments in `ξ`. -/
  alphaSymm : ∀ i β α t, F i β (-α) t = F i β α t
  /-- Joint integrability on the `(β, α)` plane, used for the Fubini exchange. -/
  integrable : ∀ i t, MeasureTheory.Integrable (fun p : ℝ × ℝ => F i p.1 p.2 t)
  /-- Joint integrability of every `(β, α)` monomial moment of `F`. -/
  momentIntegrable : ∀ i (m k : ℕ) t,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => p.1 ^ m * p.2 ^ k * F i p.1 p.2 t)

/-- A D-term `D(u, t)`, a function of `u = x/ξ` supported on `|u| ≤ 1`. -/
structure DTerm (Flavor : Type) : Type where
  /-- The D-term itself, indexed by flavor and `(u, t)`. -/
  D : Flavor → ℝ → ℝ → ℝ
  /-- Support on `|u| ≤ 1`, i.e. the ERBL region `|x| ≤ |ξ|`. -/
  support : ∀ i u t, 1 < |u| → D i u t = 0
  /-- Oddness in `u`, the expansion in odd Gegenbauer polynomials. -/
  odd : ∀ i u t, D i (-u) t = -D i u t
  /-- Integrability of every monomial moment of the D-term. -/
  momentIntegrable : ∀ i (m : ℕ) t, MeasureTheory.Integrable (fun u : ℝ => u ^ m * D i u t)

/-- The GPD induced by a double distribution together with a D-term.

For `ξ ≠ 0` this is the `α`-integrated form of the delta-function representation; for
`ξ = 0` it is the forward limit. See the module docstring for the derivation. -/
def gpdOfDoubleDistribution (dd : DoubleDistribution Flavor) (dt : DTerm Flavor) :
    Gpd Flavor :=
  fun i x xi t =>
    if xi = 0 then
      ∫ α : ℝ, dd.F i x α t
    else
      (|xi|)⁻¹ * (∫ β : ℝ, dd.F i β ((x - β) / xi) t) + (xi / |xi|) * dt.D i (x / xi) t

/-- A GPD model whose `H` and `E` are both built from double distributions. -/
def Model.ofDoubleDistribution
    (ddH : DoubleDistribution Flavor) (dtH : DTerm Flavor)
    (ddE : DoubleDistribution Flavor) (dtE : DTerm Flavor) : Model Flavor where
  H := gpdOfDoubleDistribution ddH dtH
  E := gpdOfDoubleDistribution ddE dtE

/-- The forward parton density carried by a double distribution, `f(x) = ∫ dα F(x, α, 0)`. -/
def pdfOfDoubleDistribution (dd : DoubleDistribution Flavor) : PDF.Pdf Flavor :=
  fun i x _Q2 => ∫ α : ℝ, dd.F i x α 0

/-- At zero skewness the induced GPD is the `α`-integral of the double distribution. -/
lemma gpdOfDoubleDistribution_zero_skewness
    (dd : DoubleDistribution Flavor) (dt : DTerm Flavor) (i : Flavor) (x t : ℝ) :
    gpdOfDoubleDistribution dd dt i x 0 t = ∫ α : ℝ, dd.F i x α t := by
  simp [gpdOfDoubleDistribution]

/-- The GPD forward-limit relation is *discharged*, not assumed, for a model built from
double distributions: `H(x, 0, 0)` is by construction the induced parton density. -/
lemma forwardLimit_ofDoubleDistribution
    (ddH ddE : DoubleDistribution Flavor) (dtH dtE : DTerm Flavor) (Q2 : ℝ) :
    ForwardLimitToPdfAtScale (Model.ofDoubleDistribution ddH dtH ddE dtE)
      (pdfOfDoubleDistribution ddH) Q2 := by
  intro i x
  simp [Model.ofDoubleDistribution, gpdOfDoubleDistribution, pdfOfDoubleDistribution]

/-- The induced GPD has the physical support `|x| ≤ 1`, for physical skewness `|ξ| ≤ 1`.

Both contributions vanish pointwise: the D-term because `|x/ξ| ≥ |x| > 1` leaves its
support, and the double-distribution integrand because `|x| ≤ |β| + |ξ| |α| ≤ |β| + |α|`
would force the rhombus condition `|β| + |α| ≤ 1`. -/
lemma gpdOfDoubleDistribution_eq_zero_of_one_lt_abs
    (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (i : Flavor) (x xi t : ℝ) (hxi : |xi| ≤ 1) (hx : 1 < |x|) :
    gpdOfDoubleDistribution dd dt i x xi t = 0 := by
  by_cases hxi0 : xi = 0
  · subst hxi0
    have hzero : ∀ α : ℝ, dd.F i x α t = 0 := by
      intro α
      refine dd.support i x α t ?_
      have hα : (0 : ℝ) ≤ |α| := abs_nonneg α
      linarith
    simp [gpdOfDoubleDistribution, hzero]
  · have hne : xi ≠ 0 := hxi0
    -- The D-term argument `x/ξ` is outside the D-term support.
    have hcancel : x / xi * xi = x := by field_simp
    have hmul : |x / xi| * |xi| = |x| := by rw [← abs_mul, hcancel]
    have hstep : |x / xi| * (1 - |xi|) = |x / xi| - |x| := by
      rw [mul_sub, mul_one, hmul]
    have hnn : 0 ≤ |x / xi| * (1 - |xi|) := mul_nonneg (abs_nonneg _) (by linarith)
    have hD : dt.D i (x / xi) t = 0 := dt.support i (x / xi) t (by linarith)
    -- The double-distribution integrand vanishes identically in `β`.
    have hF : ∀ β : ℝ, dd.F i β ((x - β) / xi) t = 0 := by
      intro β
      by_contra hnz
      have hle : |β| + |(x - β) / xi| ≤ 1 := by
        by_contra hgt
        exact hnz (dd.support i β ((x - β) / xi) t (not_le.mp hgt))
      have hcancel2 : (x - β) / xi * xi = x - β := by field_simp
      have hmul2 : |(x - β) / xi| * |xi| = |x - β| := by rw [← abs_mul, hcancel2]
      have hstep2 : |(x - β) / xi| * (1 - |xi|) = |(x - β) / xi| - |x - β| := by
        rw [mul_sub, mul_one, hmul2]
      have hnn2 : 0 ≤ |(x - β) / xi| * (1 - |xi|) := mul_nonneg (abs_nonneg _) (by linarith)
      have htri : |x| ≤ |β| + |x - β| := by
        have h0 : |β + (x - β)| ≤ |β| + |x - β| := abs_add _ _
        have hxe : β + (x - β) = x := by ring
        rw [hxe] at h0
        exact h0
      linarith
    simp [gpdOfDoubleDistribution, hxi0, hF, hD]

end GPD
end Parton
end Particles
end Physlib
