/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.Parton.TMD.Basic
/-!

# The Two-Scale Renormalization Group of a TMD and the Collins-Soper Kernel

A transverse-momentum-dependent distribution depends on a renormalization scale `μ` and a
rapidity scale `ζ` and obeys one evolution equation in each. This module states that
pair of equations with real derivatives, states the consistency condition relating their
anomalous dimensions, and draws the one conclusion that follows from the consistency
condition alone.

## A correction to the framing this module was written from

The task documentation for this target asserts that equality of the mixed second
derivatives "forces the Collins-Soper kernel to be independent of the distribution it
acts on". That is not what integrability gives. Clairaut's theorem relates the `ζ`
derivative of the `μ` anomalous dimension to the `μ` derivative of the Collins-Soper
kernel; both are the cusp anomalous dimension. What that yields is

  `∂K_f/∂μ = ∂K_g/∂μ` whenever `f` and `g` share a cusp anomalous dimension,

so the two kernels differ by a *`μ`-independent* function, and a boundary condition at
one scale is needed to conclude they are equal. Distribution-independence of the
Collins-Soper kernel is an input — it comes from the kernel being a property of the soft
function and the rapidity regulator rather than of the collinear dynamics — not a
corollary of integrability. `csKernel_eq_of_cuspConsistent` states the version that does
follow, with the boundary condition visible in its hypotheses.

A second point where the statement has to be made carefully: that the Collins-Soper
kernel does not depend on `ζ` is encoded here in the *type* of the `csKernel` field,
which takes `μ` but not `ζ`. That is a real assumption about the RG system and not a
notational convenience, and it is what makes the consistency condition below have the
form it does.

## Status

The RG system, the two equations and the consistency condition are stated;
`csKernel_sub_hasDerivAt_zero` and `csKernel_eq_of_cuspConsistent` are proved. What is
*not* done is the derivation of the consistency condition from Clairaut's theorem, which
would need `μ ↦ ζ ↦ log f` to be twice continuously differentiable jointly and an
application of mathlib's symmetry-of-second-derivatives result; the condition is
therefore carried as a hypothesis bundle with its two clauses written out, not asserted.

This module compiles. The sentence previously here, "Nothing in this module has been
compiled", was written before the module was first built and was left behind when it was;
it is corrected rather than deleted because a status line that outlives its truth is the
failure mode this file's own framing note was written to warn about.

A further leading-power caveat, recorded when
`Physlib.Particles.Parton.TMD.PowerCorrections` was added: the multiplicative two-scale
structure stated here is the leading-power structure. arXiv:2603.19833 finds that once
kinematic power corrections are included the TMD evolution factor enters as a convolution
with the nonperturbative distribution rather than multiplicatively, so `SatisfiesZetaRg`
should not be read as holding beyond leading power.

## References

* J. C. Collins, D. E. Soper and G. Sterman, *Transverse momentum distribution in
  Drell-Yan pair and W and Z boson production*, Nucl. Phys. B **250** (1985) 199.
* J. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011).
* R. Boussarie *et al.*, *TMD Handbook*, arXiv:2304.03302, for the modern statement of
  the two-scale structure.
* arXiv:2306.06488, for a lattice determination of the Collins-Soper kernel.

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace Particles
namespace Parton
namespace TMD

variable {Flavor : Type}

/-- The logarithm of a TMD, indexed by flavour, momentum fraction, transverse separation
`b_T`, renormalization scale `μ` and rapidity scale `ζ`.

The logarithm rather than the distribution itself, because both evolution equations are
statements about `d log f`; taking the logarithm as the primitive object avoids carrying
a positivity hypothesis into every derivative. Note the transverse argument is `b_T`, the
conjugate of the transverse momentum: the Collins-Soper kernel is a function of `b_T`, not
of `k_T`, and is an ordinary function there rather than a distribution. -/
abbrev LogTmd (Flavor : Type) : Type := Flavor → ℝ → ℝ → ℝ → ℝ → ℝ

/-- The anomalous dimensions of the two-scale renormalization group of a TMD.

The Collins-Soper kernel is allowed to depend on the flavour and momentum fraction here,
so that its independence of them can be a conclusion rather than a convention. It is
*not* allowed to depend on `ζ`: that is the defining property of the rapidity anomalous
dimension and is imposed by the type. -/
structure TmdRgSystem (Flavor : Type) : Type where
  /-- The `μ` anomalous dimension `γ_μ(i, x, b_T, μ, ζ)`. -/
  gammaMu : Flavor → ℝ → ℝ → ℝ → ℝ → ℝ
  /-- The Collins-Soper kernel `K(i, x, b_T, μ)`, independent of `ζ` by construction. -/
  csKernel : Flavor → ℝ → ℝ → ℝ → ℝ

/-- The renormalization-group equation in `μ`, as a logarithmic derivative:
`∂(log f)/∂ log μ = γ_μ`, written as `∂(log f)/∂μ = γ_μ/μ`.

**This was previously stated as `∂(log f)/∂μ = γ_μ`, and that is not the equation the rest of
this module uses.** `CuspConsistent` below renders the two literature statements
`∂K/∂ log μ = -γ_cusp` and `∂γ_μ/∂ log √ζ = -γ_cusp` as derivatives in `μ` and in `ζ`. With a
plain-`μ` equation here, the mixed-derivative (Clairaut) condition that `CuspConsistent` is
advertised to be would read `∂γ_μ/∂ζ = -γ_cusp/(2 μ ζ)`, which is not what `CuspConsistent`
asserts: the two differed by a factor `1/μ`. The logarithmic form is also the dimensionally
consistent one, `γ_μ` being a pure number while `∂(log f)/∂μ` carries an inverse mass.

With the correction the two equations have a common solution, which is the content of
`satisfiesMuRg_sudakovLogTmd` and `satisfiesZetaRg_sudakovLogTmd` below. The hypothesis
`0 < mu` is new and unavoidable: a logarithmic derivative in `μ` has no meaning at `μ = 0`.
Nothing in the repository referenced `SatisfiesMuRg`, so the change breaks no dependent. -/
def SatisfiesMuRg (L : LogTmd Flavor) (S : TmdRgSystem Flavor) : Prop :=
  ∀ i x bT mu zeta, 0 < mu →
    HasDerivAt (fun m => L i x bT m zeta) (S.gammaMu i x bT mu zeta / mu) mu

/-- The Collins-Soper equation in `ζ`: `∂(log f)/∂ζ = K / (2ζ)`, i.e.
`∂(log f)/∂ log √ζ = K`. -/
def SatisfiesZetaRg (L : LogTmd Flavor) (S : TmdRgSystem Flavor) : Prop :=
  ∀ i x bT mu zeta, 0 < zeta →
    HasDerivAt (fun z => L i x bT mu z) (S.csKernel i x bT mu / (2 * zeta)) zeta

/-- The consistency condition on the two anomalous dimensions: both mixed derivatives of
`log f` are minus the cusp anomalous dimension.

`∂K/∂ log μ = -γ_cusp(μ)` and `∂γ_μ/∂ log √ζ = -γ_cusp(μ)`, written as derivatives in
`μ` and `ζ` respectively. This is the content Clairaut's theorem would supply for a
jointly `C²` logarithm; it is carried here as a hypothesis with both clauses spelled out
rather than derived. -/
structure CuspConsistent (S : TmdRgSystem Flavor) (gammaCusp : ℝ → ℝ) : Prop where
  /-- `∂K/∂μ = -γ_cusp(μ)/μ`. -/
  csKernel_muDeriv : ∀ i x bT mu, 0 < mu →
    HasDerivAt (fun m => S.csKernel i x bT m) (-gammaCusp mu / mu) mu
  /-- `∂γ_μ/∂ζ = -γ_cusp(μ)/(2ζ)`. -/
  gammaMu_zetaDeriv : ∀ i x bT mu zeta, 0 < zeta →
    HasDerivAt (fun z => S.gammaMu i x bT mu z) (-gammaCusp mu / (2 * zeta)) zeta

/-- **Integrability fixes the scale dependence of the Collins-Soper kernel.** Two RG
systems sharing a cusp anomalous dimension have Collins-Soper kernels whose difference
has vanishing `μ` derivative at every positive scale.

This is the whole of what the consistency condition gives: the kernels agree in their
scale dependence, not in their value. -/
theorem csKernel_sub_hasDerivAt_zero (S T : TmdRgSystem Flavor) (gammaCusp : ℝ → ℝ)
    (hS : CuspConsistent S gammaCusp) (hT : CuspConsistent T gammaCusp)
    (i : Flavor) (x bT mu : ℝ) (hmu : 0 < mu) :
    HasDerivAt (fun m => S.csKernel i x bT m - T.csKernel i x bT m) 0 mu := by
  have h := (hS.csKernel_muDeriv i x bT mu hmu).sub (hT.csKernel_muDeriv i x bT mu hmu)
  -- `simpa` normalises the derivative to `0` but then closes only at reducible
  -- transparency, which cannot bridge two things here: `HasDerivAt.sub` yields the
  -- pointwise function `f - g` rather than `fun m => f m - g m`, and it routes the
  -- module instance through `RCLike.toInnerProductSpaceReal` where the goal uses
  -- `Semiring.toModule`. Both differences are definitional, so normalise the
  -- derivative first and let `exact` unfold at default transparency.
  simp only [sub_self] at h
  exact h

/-- **Universality of the Collins-Soper kernel, with its boundary condition explicit.**
Two RG systems sharing a cusp anomalous dimension and agreeing at one positive scale
`μ₀` have equal Collins-Soper kernels throughout `[μ₀, μ₁]`.

The boundary hypothesis `hbdry` is not removable: integrability constrains only the
scale derivative, so without it the two kernels may differ by any `μ`-independent
function. In the physical argument that boundary condition is supplied by the structure
of the soft function, not by the renormalization group. -/
theorem csKernel_eq_of_cuspConsistent (S T : TmdRgSystem Flavor) (gammaCusp : ℝ → ℝ)
    (hS : CuspConsistent S gammaCusp) (hT : CuspConsistent T gammaCusp)
    (i : Flavor) (x bT mu0 mu1 : ℝ) (hmu0 : 0 < mu0)
    (hbdry : S.csKernel i x bT mu0 = T.csKernel i x bT mu0) :
    ∀ mu ∈ Set.Icc mu0 mu1, S.csKernel i x bT mu = T.csKernel i x bT mu := by
  have hderiv : ∀ m : ℝ, m ∈ Set.Ico mu0 mu1 →
      HasDerivWithinAt (fun m' => S.csKernel i x bT m' - T.csKernel i x bT m') 0
        (Set.Ici m) m := by
    intro m hm
    have hmpos : 0 < m := lt_of_lt_of_le hmu0 hm.1
    exact (csKernel_sub_hasDerivAt_zero S T gammaCusp hS hT i x bT m hmpos).hasDerivWithinAt
  have hcont : ContinuousOn
      (fun m' => S.csKernel i x bT m' - T.csKernel i x bT m') (Set.Icc mu0 mu1) := by
    intro m hm
    have hmpos : 0 < m := lt_of_lt_of_le hmu0 hm.1
    exact ((csKernel_sub_hasDerivAt_zero S T gammaCusp hS hT i x bT m
      hmpos).continuousAt).continuousWithinAt
  have key := constant_of_has_deriv_right_zero
      (f := fun m' => S.csKernel i x bT m' - T.csKernel i x bT m')
      (a := mu0) (b := mu1) hcont hderiv
  intro mu hmu
  have h := key mu hmu
  have h0 : S.csKernel i x bT mu0 - T.csKernel i x bT mu0 = 0 := sub_eq_zero.mpr hbdry
  rw [h0] at h
  exact sub_eq_zero.mp h

/-! ### An explicit solution of the two-scale renormalization group

Everything above is conditional on `CuspConsistent`, and nothing in the repository
instantiated it; a hypothesis bundle with no model is not known to be satisfiable at all.
The leading-logarithmic system below is a model. All three predicates of this module —
`CuspConsistent`, `SatisfiesMuRg`, `SatisfiesZetaRg` — hold for it, with no `sorry` and no
residual hypothesis.

The construction is the familiar one-loop structure with the Sudakov double logarithm,

  `K(b_T, μ) = K₀(b_T) - Γ₀ log μ`,
  `γ_μ(b_T, ζ) = γ_V(b_T) - (Γ₀/2) log ζ`,
  `log f = γ_V(b_T) log μ + (K₀(b_T)/2) log ζ - (Γ₀/2) log μ log ζ`,

with a constant cusp anomalous dimension `Γ₀`. The boundary kernel `K₀` and the vector
anomalous dimension `γ_V` are left arbitrary, which is what makes `csKernel_sub_logRgSystem`
available: it exhibits the `μ`-independent freedom that the boundary hypothesis of
`csKernel_eq_of_cuspConsistent` removes, so that hypothesis is now witnessed to be necessary
rather than merely not removed.
-/

/-- The leading-logarithmic two-scale RG system: constant cusp anomalous dimension
`gammaCusp0`, boundary kernel `K0`, vector anomalous dimension `gammaV`. Neither anomalous
dimension depends on the flavour or on the momentum fraction. -/
def logRgSystem (Flavor : Type) (gammaCusp0 : ℝ) (K0 gammaV : ℝ → ℝ) :
    TmdRgSystem Flavor where
  gammaMu := fun _ _ bT _ zeta => gammaV bT - gammaCusp0 / 2 * Real.log zeta
  csKernel := fun _ _ bT mu => K0 bT - gammaCusp0 * Real.log mu

/-- The Sudakov logarithm, an explicit `LogTmd` solving both renormalization-group equations
of `logRgSystem`. The `log μ log ζ` term is the double logarithm; its coefficient is fixed by
the cusp anomalous dimension, which is the whole content of the two-scale structure. -/
def sudakovLogTmd (Flavor : Type) (gammaCusp0 : ℝ) (K0 gammaV : ℝ → ℝ) : LogTmd Flavor :=
  fun _ _ bT mu zeta =>
    gammaV bT * Real.log mu + K0 bT / 2 * Real.log zeta
      - gammaCusp0 / 2 * Real.log mu * Real.log zeta

/-- **`CuspConsistent` is satisfiable.** The leading-logarithmic system satisfies it with the
constant cusp anomalous dimension `Γ₀`; each clause is the derivative of a single
logarithm. -/
lemma cuspConsistent_logRgSystem (gammaCusp0 : ℝ) (K0 gammaV : ℝ → ℝ) :
    CuspConsistent (logRgSystem Flavor gammaCusp0 K0 gammaV) (fun _ => gammaCusp0) := by
  constructor
  · intro i x bT mu hmu
    have hmu' : mu ≠ 0 := hmu.ne'
    have h : HasDerivAt (fun m : ℝ => K0 bT - gammaCusp0 * Real.log m)
        (0 - gammaCusp0 * mu⁻¹) mu :=
      (hasDerivAt_const mu (K0 bT)).sub
        ((Real.hasDerivAt_log hmu').const_mul gammaCusp0)
    have hval : (0 : ℝ) - gammaCusp0 * mu⁻¹ = -gammaCusp0 / mu := by
      field_simp
    rw [hval] at h
    exact h
  · intro i x bT mu zeta hzeta
    have hz : zeta ≠ 0 := hzeta.ne'
    have h : HasDerivAt (fun z : ℝ => gammaV bT - gammaCusp0 / 2 * Real.log z)
        (0 - gammaCusp0 / 2 * zeta⁻¹) zeta :=
      (hasDerivAt_const zeta (gammaV bT)).sub
        ((Real.hasDerivAt_log hz).const_mul (gammaCusp0 / 2))
    have hval : (0 : ℝ) - gammaCusp0 / 2 * zeta⁻¹ = -gammaCusp0 / (2 * zeta) := by
      field_simp
    rw [hval] at h
    exact h

/-- **`SatisfiesMuRg` is satisfiable.** The Sudakov logarithm obeys the `μ` equation of the
leading-logarithmic system. -/
lemma satisfiesMuRg_sudakovLogTmd (gammaCusp0 : ℝ) (K0 gammaV : ℝ → ℝ) :
    SatisfiesMuRg (sudakovLogTmd Flavor gammaCusp0 K0 gammaV)
      (logRgSystem Flavor gammaCusp0 K0 gammaV) := by
  intro i x bT mu zeta hmu
  have hmu' : mu ≠ 0 := hmu.ne'
  have hlog := Real.hasDerivAt_log hmu'
  have h : HasDerivAt (fun m : ℝ => gammaV bT * Real.log m + K0 bT / 2 * Real.log zeta
        - gammaCusp0 / 2 * Real.log m * Real.log zeta)
      (gammaV bT * mu⁻¹ + 0 - gammaCusp0 / 2 * mu⁻¹ * Real.log zeta) mu :=
    ((hlog.const_mul (gammaV bT)).add
        (hasDerivAt_const mu (K0 bT / 2 * Real.log zeta))).sub
      ((hlog.const_mul (gammaCusp0 / 2)).mul_const (Real.log zeta))
  have hval : gammaV bT * mu⁻¹ + 0 - gammaCusp0 / 2 * mu⁻¹ * Real.log zeta
      = (gammaV bT - gammaCusp0 / 2 * Real.log zeta) / mu := by
    field_simp
  rw [hval] at h
  exact h

/-- **`SatisfiesZetaRg` is satisfiable.** The Sudakov logarithm obeys the Collins-Soper
equation of the leading-logarithmic system, with the same double-logarithm coefficient that
the `μ` equation fixes. -/
lemma satisfiesZetaRg_sudakovLogTmd (gammaCusp0 : ℝ) (K0 gammaV : ℝ → ℝ) :
    SatisfiesZetaRg (sudakovLogTmd Flavor gammaCusp0 K0 gammaV)
      (logRgSystem Flavor gammaCusp0 K0 gammaV) := by
  intro i x bT mu zeta hzeta
  have hz : zeta ≠ 0 := hzeta.ne'
  have hlog := Real.hasDerivAt_log hz
  have h : HasDerivAt (fun z : ℝ => gammaV bT * Real.log mu + K0 bT / 2 * Real.log z
        - gammaCusp0 / 2 * Real.log mu * Real.log z)
      (0 + K0 bT / 2 * zeta⁻¹ - gammaCusp0 / 2 * Real.log mu * zeta⁻¹) zeta :=
    ((hasDerivAt_const zeta (gammaV bT * Real.log mu)).add
        (hlog.const_mul (K0 bT / 2))).sub
      (hlog.const_mul (gammaCusp0 / 2 * Real.log mu))
  have hval : 0 + K0 bT / 2 * zeta⁻¹ - gammaCusp0 / 2 * Real.log mu * zeta⁻¹
      = (K0 bT - gammaCusp0 * Real.log mu) / (2 * zeta) := by
    field_simp
    ring
  rw [hval] at h
  exact h

/-- **The boundary hypothesis of `csKernel_eq_of_cuspConsistent` is not an artifact of its
proof.** Two leading-logarithmic systems with the same cusp anomalous dimension are both
`CuspConsistent`, yet their Collins-Soper kernels differ at every scale by the constant
`K₀(b_T) - K₀'(b_T)`. So universality of the Collins-Soper kernel cannot follow from
integrability alone; it needs the boundary condition, which is the correction recorded in the
module docstring, here witnessed by an explicit pair rather than argued. -/
lemma csKernel_sub_logRgSystem (gammaCusp0 : ℝ) (K0 K0' gammaV gammaV' : ℝ → ℝ)
    (i : Flavor) (x bT mu : ℝ) :
    (logRgSystem Flavor gammaCusp0 K0 gammaV).csKernel i x bT mu
        - (logRgSystem Flavor gammaCusp0 K0' gammaV').csKernel i x bT mu
      = K0 bT - K0' bT := by
  show K0 bT - gammaCusp0 * Real.log mu - (K0' bT - gammaCusp0 * Real.log mu)
      = K0 bT - K0' bT
  ring

end TMD
end Parton
end Particles
end Physlib
