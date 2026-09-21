/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.DIS.LO
public import Physlib.QFT.Factorization.Evolution.Basic
/-!

# Independent factorization and renormalization scales

## i. Overview

A collinear factorization formula for a deep-inelastic structure function involves three
scales: the hard scale `Q²` of the process, the factorization scale `μ_F` at which the
parton densities are defined, and the renormalization scale `μ_R` of the coupling in which
the coefficient function is expanded.

The factorization development in `Physlib/QFT/Factorization` carries **one** scale argument.
`Physlib.Particles.Parton.PDF.Pdf` is `Flavor → ℝ → ℝ → ℝ` with the last argument `Q2`;
`Physlib.QFT.Factorization.DIS.HardKernel` has a single `Q2` slot; and
`Physlib.QFT.Factorization.DIS.loStructureFunction` passes *the same* `Q2` to the
coefficient function and to the density. The same holds in evolution:
`Physlib.QFT.Factorization.Evolution.dglapRhsLogScale` evaluates the coupling and the
densities at one and the same `exp τ`. So `μ_F` and `μ_R` are not separately represented
anywhere; there is a single scale slot playing all three roles.

This module introduces the three scales as independent arguments, records exactly how the
existing single-scale development sits inside the three-scale one (it is the diagonal
`μ_F² = μ_R² = Q²`), and proves the scale-invariance statement that the separation makes
available: a factorized observable is independent of the factorization scale **if and only
if** the coefficient function's explicit scale derivative cancels the DGLAP running of the
densities, after the flavor sum.

## ii. Key results

- `twoScaleStructureFunction` is the factorized observable with the three scales separated;
  `twoScaleStructureFunction_ofSingleScale_diagonal` identifies the existing
  `DIS.loStructureFunction` with its diagonal, and `dglapOperatorTwoScale_diagonal` does the
  same for the DGLAP operator.
- `ScaleDerivatives` packages the two partial `log μ_F²` derivatives of a channel — the
  coefficient function's explicit dependence and the density's running — together with the
  chain rule relating them to the total derivative.
- `isFactorizationScaleIndependent_iff_compensation` is the invariance theorem, in both
  directions: invariance holds exactly when the two derivatives cancel after the flavor sum.
- `isFactorizationScaleIndependent_iff_dglap_compensation` writes the density term out as
  the coefficient function convolved with the DGLAP right-hand side, so that the
  compensation reads as an equation between the two pieces rather than as an abstract
  cancellation.
- `scaledScaleDerivatives` is a witness with both terms non-zero: the hypotheses are not
  contradictory, and the theorem is not about a cancellation of two zeros.

## iii. What is *not* claimed here

The anchor paper for this development, arXiv:2608.01489, "What are the consequences of
independent factorization and renormalization scales?", argues the *opposite* of what a
reader might expect from the name of this module: that requiring renormalization-group
invariance, Ward identities and the parton-density sum rules simultaneously, in generalized
pole-subtraction schemes in dimensional regularization, **forces the two scales to be
equal**. On that reading the single scale slot in the existing development is a defensible
choice and not a defect; what was missing is that nothing in the code said so.

Nothing in this module establishes or refutes that claim. Doing so needs the operator
definitions of the parton densities in dimensional regularization, the subtraction scheme,
and the Ward identities, none of which exist in this library; an "assumptions" structure
standing in for them would contain the conclusion. What is proved here is the weaker and
scheme-independent statement — the `μ_F` compensation — which holds whether or not the two
scales are ultimately forced together.

Two further limitations. The chain-rule field of `ScaleDerivatives` and the `underIntegral`
field of `DensityDerivativeIsDGLAP` are *analytic* inputs: both amount to differentiating a
Bochner integral over the momentum fraction under the integral sign, which is not available
for arbitrary coefficient functions and densities. They are hypotheses, not theorems, and
are named for what they say. And the compensation here is exact, not order by order: a
statement of `μ_F` independence "to the order at which the pieces are known" needs a notion
of truncation error that `Physlib.QFT.Factorization.HigherOrder.PerturbativeOrder` does not
carry.

## iv. Table of contents

- A. Two-scale coefficient functions and observables
- B. The diagonal: what the existing single-scale development says
- C. Constant factors through the convolution
- D. The logarithmic factorization scale and its two partial derivatives
- E. The compensation and the invariance theorem
- F. The density term is DGLAP evolution
- G. A witness with both terms non-zero

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace QFT
namespace Factorization
namespace Scales

open Physlib.Particles.Parton

variable {Flavor : Type}

/-! ## A. Two-scale coefficient functions and observables -/

/-- A coefficient function carrying the hard scale, the factorization scale and the
renormalization scale as three independent arguments, `C i x z Q2 μF2 μR2`.

The name records that the two *unphysical* scales are separated; the hard scale `Q2` was
already present in `Physlib.QFT.Factorization.DIS.HardKernel`. -/
abbrev TwoScaleHardKernel (Flavor : Type) : Type :=
  Flavor → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ

/-- The flavor-`i` channel of the factorized observable: the coefficient function is
evaluated at `(Q2, μF2, μR2)` and the parton density at `μF2`, which is what makes `μF2` the
factorization scale rather than an inert extra argument. -/
def twoScaleChannel
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor)
    (i : Flavor) (x Q2 μF2 μR2 : ℝ) : ℝ :=
  Convolution.convolveAt (fun x' z => C i x' z Q2 μF2 μR2) (fun z => f i z μF2) x

/-- The factorized observable at independent factorization and renormalization scales. -/
def twoScaleStructureFunction [Fintype Flavor]
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor)
    (x Q2 μF2 μR2 : ℝ) : ℝ :=
  ∑ i, twoScaleChannel C f i x Q2 μF2 μR2

/-! ## B. The diagonal: what the existing single-scale development says

The two lemmas of this section are the precise statement of the situation described in the
overview. They are `rfl`, and that is the point: the existing development is not a
three-scale formula with an error in it, it is the diagonal restriction of one. -/

/-- A single-scale coefficient function read as a two-scale one that ignores both unphysical
scales. -/
def ofSingleScale (C : DIS.HardKernel Flavor) : TwoScaleHardKernel Flavor :=
  fun i x z Q2 _μF2 _μR2 => C i x z Q2

/-- On the diagonal `μF² = μR² = Q²` the two-scale channel is the existing LO channel. -/
lemma twoScaleChannel_ofSingleScale_diagonal
    (C : DIS.HardKernel Flavor) (f : PDF.Pdf Flavor) (i : Flavor) (x Q2 : ℝ) :
    twoScaleChannel (ofSingleScale C) f i x Q2 Q2 Q2 = DIS.loChannel C f i x Q2 :=
  rfl

/-- **The existing LO structure function is the diagonal of the two-scale one.**

`Physlib.QFT.Factorization.DIS.loStructureFunction C f x Q2` is
`twoScaleStructureFunction (ofSingleScale C) f x Q2 Q2 Q2`: the factorization and
renormalization scales are both set to the hard scale. -/
lemma twoScaleStructureFunction_ofSingleScale_diagonal [Fintype Flavor]
    (C : DIS.HardKernel Flavor) (f : PDF.Pdf Flavor) (x Q2 : ℝ) :
    twoScaleStructureFunction (ofSingleScale C) f x Q2 Q2 Q2
      = DIS.loStructureFunction C f x Q2 :=
  rfl

/-- At leading order the coefficient function has no renormalization-scale dependence, and
then the observable has none either. This is the honest content of the `μ_R` slot at the
order the library currently reaches: it is present but unused, and `μ_R` first enters at
next-to-leading order. -/
lemma twoScaleStructureFunction_congr_renormalizationScale [Fintype Flavor]
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor)
    (x Q2 μF2 μR2 μR2' : ℝ)
    (hC : ∀ i x' z, C i x' z Q2 μF2 μR2 = C i x' z Q2 μF2 μR2') :
    twoScaleStructureFunction C f x Q2 μF2 μR2
      = twoScaleStructureFunction C f x Q2 μF2 μR2' := by
  refine Finset.sum_congr rfl ?_
  intro i _
  exact Convolution.convolveAt_eq_of_kernel_eq _ _ _ _ (fun x' z => hC i x' z)

/-! ## C. Constant factors through the convolution

`Convolution.Properties` has the pointwise statements `integrand_smul_kernel` and
`integrand_smul_right`; the integrated forms below are what the scale-factor computations in
section G need, and they are stated here rather than added to the convolution API so that
this module owns them. -/

/-- A constant factor in the coefficient function comes out of the convolution. -/
lemma convolveAt_const_mul_kernel (a : ℝ) (K : Convolution.Kernel) (g : ℝ → ℝ) (x : ℝ) :
    Convolution.convolveAt (fun x' z => a * K x' z) g x
      = a * Convolution.convolveAt K g x := by
  have h : ∀ z, Convolution.integrand (fun x' z' => a * K x' z') g x z
      = a * Convolution.integrand K g x z := by
    intro z
    simp only [Convolution.integrand]
    ring
  simp only [Convolution.convolveAt, h]
  exact MeasureTheory.integral_const_mul a fun z => Convolution.integrand K g x z

/-- A constant factor in the parton density comes out of the convolution. -/
lemma convolveAt_const_mul_density (a : ℝ) (K : Convolution.Kernel) (g : ℝ → ℝ) (x : ℝ) :
    Convolution.convolveAt K (fun z => a * g z) x
      = a * Convolution.convolveAt K g x := by
  have h : ∀ z, Convolution.integrand K (fun z' => a * g z') x z
      = a * Convolution.integrand K g x z := by
    intro z
    simp only [Convolution.integrand]
    ring
  simp only [Convolution.convolveAt, h]
  exact MeasureTheory.integral_const_mul a fun z => Convolution.integrand K g x z

/-! ## D. The logarithmic factorization scale and its two partial derivatives

The factorization scale enters a channel in two places — the coefficient function and the
density — and the physics of scale invariance is the cancellation *between* those two
places. The three definitions below are the channel as a function of `L = log μ_F²` and the
two families obtained by freezing one of the two occurrences, so that "the coefficient
function's scale derivative" and "the density's scale derivative" are statements about named
objects rather than informal readings of a formula. -/

/-- The channel as a function of the logarithmic factorization scale `L = log μF²`. -/
def channelLog
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor)
    (i : Flavor) (x Q2 μR2 L : ℝ) : ℝ :=
  twoScaleChannel C f i x Q2 (Real.exp L) μR2

/-- The channel with the coefficient function's factorization-scale argument varying and the
density's frozen at `exp L₀`: the coefficient function's *explicit* scale dependence. -/
def channelCoefficientSlot
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor)
    (i : Flavor) (x Q2 μR2 L₀ L : ℝ) : ℝ :=
  Convolution.convolveAt (fun x' z => C i x' z Q2 (Real.exp L) μR2)
    (fun z => f i z (Real.exp L₀)) x

/-- The channel with the density's factorization-scale argument varying and the coefficient
function's frozen at `exp L₀`: the density's DGLAP running. -/
def channelDensitySlot
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor)
    (i : Flavor) (x Q2 μR2 L₀ L : ℝ) : ℝ :=
  Convolution.convolveAt (fun x' z => C i x' z Q2 (Real.exp L₀) μR2)
    (fun z => f i z (Real.exp L)) x

/-- On the diagonal the frozen-density family is the channel: this is what makes its
derivative a *partial* derivative of `channelLog`. -/
lemma channelCoefficientSlot_self
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor)
    (i : Flavor) (x Q2 μR2 L : ℝ) :
    channelCoefficientSlot C f i x Q2 μR2 L L = channelLog C f i x Q2 μR2 L :=
  rfl

/-- On the diagonal the frozen-coefficient family is the channel. -/
lemma channelDensitySlot_self
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor)
    (i : Flavor) (x Q2 μR2 L : ℝ) :
    channelDensitySlot C f i x Q2 μR2 L L = channelLog C f i x Q2 μR2 L :=
  rfl

/-- The observable, as a function of `L = log μF²`, is the flavor sum of the channels. -/
lemma twoScaleStructureFunction_eq_sum_channelLog [Fintype Flavor]
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor) (x Q2 μR2 L : ℝ) :
    twoScaleStructureFunction C f x Q2 (Real.exp L) μR2
      = ∑ i, channelLog C f i x Q2 μR2 L :=
  rfl

/-- Independence of the factorized observable from the factorization scale, at a fixed
renormalization scale. Scales are written `exp L`, so the statement quantifies over positive
factorization scales, which is the physical range. -/
def IsFactorizationScaleIndependent [Fintype Flavor]
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor) (x Q2 μR2 : ℝ) : Prop :=
  ∀ L₁ L₂ : ℝ, twoScaleStructureFunction C f x Q2 (Real.exp L₁) μR2
    = twoScaleStructureFunction C f x Q2 (Real.exp L₂) μR2

/-! ## E. The compensation and the invariance theorem -/

/-- The two factorization-scale derivatives of a factorized observable, with the chain rule
that ties them to its total derivative.

`DC i L` is the derivative of channel `i` in the coefficient function's explicit
factorization scale, at frozen density; `DF i L` is the derivative in the density's scale, at
frozen coefficient function. **No compensation is asserted here.** This structure only fixes
what `DC` and `DF` are; the compensation is the separate hypothesis
`∀ L, ∑ i, (DC i L + DF i L) = 0` of the theorems below, and that is where the physics is. -/
structure ScaleDerivatives [Fintype Flavor]
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor)
    (x Q2 μR2 : ℝ) (DC DF : Flavor → ℝ → ℝ) : Prop where
  /-- `DC i L` is the `log μF²`-derivative of the coefficient function's explicit scale
  dependence, the density being held at the same scale `exp L`. -/
  coefficientDeriv : ∀ i L, HasDerivAt (channelCoefficientSlot C f i x Q2 μR2 L) (DC i L) L
  /-- `DF i L` is the `log μF²`-derivative of the density's scale dependence, the coefficient
  function being held at the same scale `exp L`. -/
  densityDeriv : ∀ i L, HasDerivAt (channelDensitySlot C f i x Q2 μR2 L) (DF i L) L
  /-- Chain rule for the channel in `log μF²`.

  This field is an **analytic** input, not a physics assumption. A channel is a Bochner
  integral over the momentum fraction, so its derivative in `L` is the sum of the two partial
  derivatives above only when differentiation may be taken under the integral sign, which
  needs a dominating function that an arbitrary coefficient function and density do not
  supply. It is a hypothesis for that reason and not because the product rule is in
  doubt. -/
  chainRule : ∀ i L, HasDerivAt (channelLog C f i x Q2 μR2) (DC i L + DF i L) L

/-- The total `log μF²`-derivative of the observable is the flavor sum of the channel
derivatives. -/
lemma hasDerivAt_twoScaleStructureFunction [Fintype Flavor]
    {C : TwoScaleHardKernel Flavor} {f : PDF.Pdf Flavor} {x Q2 μR2 : ℝ}
    {DC DF : Flavor → ℝ → ℝ}
    (h : ScaleDerivatives C f x Q2 μR2 DC DF) (L : ℝ) :
    HasDerivAt (fun l => twoScaleStructureFunction C f x Q2 (Real.exp l) μR2)
      (∑ i, (DC i L + DF i L)) L := by
  have hsum : HasDerivAt (fun l => ∑ i, channelLog C f i x Q2 μR2 l)
      (∑ i, (DC i L + DF i L)) L :=
    HasDerivAt.fun_sum fun i _ => h.chainRule i L
  exact hsum

/-- **Factorization-scale invariance is exactly the compensation.**

A factorized observable, assembled from a coefficient function and parton densities each
carrying factorization-scale dependence, is independent of the factorization scale if and
only if the coefficient function's explicit scale derivative cancels the densities' running,
*summed over flavors*.

The flavor sum is essential and is not a convenience: the cancellation is not required
channel by channel, because DGLAP evolution mixes the singlet channels into one another, so
the running that the gluon density feeds into the quark channel is compensated in a
different channel from the one it came out of. -/
lemma isFactorizationScaleIndependent_iff_compensation [Fintype Flavor]
    {C : TwoScaleHardKernel Flavor} {f : PDF.Pdf Flavor} {x Q2 μR2 : ℝ}
    {DC DF : Flavor → ℝ → ℝ}
    (h : ScaleDerivatives C f x Q2 μR2 DC DF) :
    IsFactorizationScaleIndependent C f x Q2 μR2
      ↔ ∀ L, ∑ i, (DC i L + DF i L) = 0 := by
  constructor
  · intro hInv L
    have hconst : (fun l => twoScaleStructureFunction C f x Q2 (Real.exp l) μR2)
        = fun _ => twoScaleStructureFunction C f x Q2 (Real.exp L) μR2 := by
      funext l
      exact hInv l L
    have hzero : HasDerivAt
        (fun l => twoScaleStructureFunction C f x Q2 (Real.exp l) μR2) 0 L := by
      rw [hconst]
      exact hasDerivAt_const L _
    exact (hasDerivAt_twoScaleStructureFunction h L).unique hzero
  · intro hcomp L₁ L₂
    have hd : ∀ L, HasDerivAt
        (fun l => twoScaleStructureFunction C f x Q2 (Real.exp l) μR2) 0 L := by
      intro L
      have hsum := hasDerivAt_twoScaleStructureFunction h L
      rwa [hcomp L] at hsum
    exact Evolution.eq_of_hasDerivAt_zero hd L₁ L₂

/-! ## F. The density term is DGLAP evolution -/

/-- The DGLAP operator with the splitting kernels at the renormalization scale and the parton
densities at the factorization scale.

`Physlib.QFT.Factorization.Evolution.dglapOperator` passes one scale to both. That is the
second place the two scales are identified in the existing development, and
`dglapOperatorTwoScale_diagonal` is the precise statement of it. -/
def dglapOperatorTwoScale [Fintype Flavor]
    (P : Evolution.SplittingKernel Flavor) (f : PDF.Pdf Flavor)
    (i : Flavor) (x μF2 μR2 : ℝ) : ℝ :=
  ∑ j, Convolution.convolveAt (Convolution.collinearKernel (fun y => P i j y μR2))
    (fun z => f j z μF2) x

/-- The existing DGLAP operator is the diagonal `μF² = μR²` of the two-scale one. -/
lemma dglapOperatorTwoScale_diagonal [Fintype Flavor]
    (P : Evolution.SplittingKernel Flavor) (f : PDF.Pdf Flavor)
    (i : Flavor) (x Q2 : ℝ) :
    dglapOperatorTwoScale P f i x Q2 Q2 = Evolution.dglapOperator P f i x Q2 :=
  rfl

/-- Identification of the density-slot derivative of a channel with DGLAP evolution of the
densities, at a fixed renormalization scale. -/
structure DensityDerivativeIsDGLAP [Fintype Flavor]
    (C : TwoScaleHardKernel Flavor) (f : PDF.Pdf Flavor)
    (P : Evolution.SplittingKernel Flavor) (αs : Evolution.RunningCoupling)
    (x Q2 μR2 : ℝ) (DF : Flavor → ℝ → ℝ) : Prop where
  /-- The parton densities obey the DGLAP equation in `log μF²`, with the coupling and the
  splitting kernels taken at the fixed renormalization scale `μR²` rather than at the
  factorization scale. -/
  dglap : ∀ i z L, HasDerivAt (fun l => f i z (Real.exp l))
    (αs μR2 / (2 * Real.pi) * dglapOperatorTwoScale P f i z (Real.exp L) μR2) L
  /-- Analytic input: the density-slot derivative of the channel may be taken under the
  momentum-fraction integral, so that it is the coefficient function convolved with the DGLAP
  right-hand side supplied by `dglap`. As with `ScaleDerivatives.chainRule` this is a
  dominated-convergence hypothesis, stated because arbitrary coefficient functions and
  densities do not license the interchange. -/
  underIntegral : ∀ i L, DF i L
    = Convolution.convolveAt (fun x' z => C i x' z Q2 (Real.exp L) μR2)
      (fun z => αs μR2 / (2 * Real.pi)
        * dglapOperatorTwoScale P f i z (Real.exp L) μR2) x

/-- The compensation with the density term written out: the coefficient function's explicit
scale derivative equals minus the coupling times the coefficient function convolved with the
DGLAP operator, summed over flavors. -/
lemma compensation_iff_dglap_form [Fintype Flavor]
    {C : TwoScaleHardKernel Flavor} {f : PDF.Pdf Flavor}
    {P : Evolution.SplittingKernel Flavor} {αs : Evolution.RunningCoupling}
    {x Q2 μR2 : ℝ} {DC DF : Flavor → ℝ → ℝ}
    (hD : DensityDerivativeIsDGLAP C f P αs x Q2 μR2 DF) (L : ℝ) :
    (∑ i, (DC i L + DF i L) = 0)
      ↔ ∑ i, DC i L
        = -(αs μR2 / (2 * Real.pi)
          * ∑ i, Convolution.convolveAt (fun x' z => C i x' z Q2 (Real.exp L) μR2)
            (fun z => dglapOperatorTwoScale P f i z (Real.exp L) μR2) x) := by
  have hDF : ∀ i, DF i L
      = αs μR2 / (2 * Real.pi)
        * Convolution.convolveAt (fun x' z => C i x' z Q2 (Real.exp L) μR2)
          (fun z => dglapOperatorTwoScale P f i z (Real.exp L) μR2) x := by
    intro i
    rw [hD.underIntegral i L]
    exact convolveAt_const_mul_density _ _ _ _
  have hsum : ∑ i, DF i L
      = αs μR2 / (2 * Real.pi)
        * ∑ i, Convolution.convolveAt (fun x' z => C i x' z Q2 (Real.exp L) μR2)
          (fun z => dglapOperatorTwoScale P f i z (Real.exp L) μR2) x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hDF i
  rw [Finset.sum_add_distrib, hsum]
  constructor <;> intro hh <;> linarith

/-- **The DGLAP form of factorization-scale invariance.**

The observable is independent of the factorization scale exactly when the flavor sum of the
coefficient functions' explicit `log μF²` derivatives cancels the flavor sum of the
coefficient functions convolved with the DGLAP right-hand side. This is the compensation
stated as an equation between the two pieces rather than assumed. -/
lemma isFactorizationScaleIndependent_iff_dglap_compensation [Fintype Flavor]
    {C : TwoScaleHardKernel Flavor} {f : PDF.Pdf Flavor}
    {P : Evolution.SplittingKernel Flavor} {αs : Evolution.RunningCoupling}
    {x Q2 μR2 : ℝ} {DC DF : Flavor → ℝ → ℝ}
    (h : ScaleDerivatives C f x Q2 μR2 DC DF)
    (hD : DensityDerivativeIsDGLAP C f P αs x Q2 μR2 DF) :
    IsFactorizationScaleIndependent C f x Q2 μR2
      ↔ ∀ L, ∑ i, DC i L
        = -(αs μR2 / (2 * Real.pi)
          * ∑ i, Convolution.convolveAt (fun x' z => C i x' z Q2 (Real.exp L) μR2)
            (fun z => dglapOperatorTwoScale P f i z (Real.exp L) μR2) x) := by
  rw [isFactorizationScaleIndependent_iff_compensation h]
  exact forall_congr' fun L => compensation_iff_dglap_form hD L

/-! ## G. A witness with both terms non-zero

A compensation theorem whose hypotheses can only be met by two vanishing derivatives would be
worthless. The witness below has an overall factor `μF²` in the coefficient function and the
reciprocal factor in the density: the two derivatives are `+J` and `-J` with `J` the channel
value, so they are non-zero whenever `J` is, and they cancel. It is a toy — the scale
dependence of a real coefficient function is logarithmic, not a power — but it establishes
that `ScaleDerivatives` together with the compensation is consistent and that the theorem is
not about a cancellation of zeros. -/

/-- A coefficient function whose explicit factorization-scale dependence is an overall factor
`μF²`. -/
def scaledKernel (K : Flavor → ℝ → ℝ → ℝ) : TwoScaleHardKernel Flavor :=
  fun i x' z _Q2 μF2 _μR2 => μF2 * K i x' z

/-- A parton density whose factorization-scale dependence is the reciprocal factor. -/
def scaledDensity (f₀ : Flavor → ℝ → ℝ) : PDF.Pdf Flavor :=
  fun i z μF2 => μF2⁻¹ * f₀ i z

/-- The scale-independent value of a channel of the witness. -/
def scaledChannelValue (K : Flavor → ℝ → ℝ → ℝ) (f₀ : Flavor → ℝ → ℝ)
    (i : Flavor) (x : ℝ) : ℝ :=
  Convolution.convolveAt (K i) (f₀ i) x

/-- Cancellation of the two scale factors of the witness. -/
lemma exp_mul_exp_neg (L : ℝ) : Real.exp L * Real.exp (-L) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- The coefficient-function slot of the witness, in closed form. -/
lemma scaledChannelCoefficientSlot_eq
    (K : Flavor → ℝ → ℝ → ℝ) (f₀ : Flavor → ℝ → ℝ)
    (i : Flavor) (x Q2 μR2 L₀ L : ℝ) :
    channelCoefficientSlot (scaledKernel K) (scaledDensity f₀) i x Q2 μR2 L₀ L
      = Real.exp L * (Real.exp (-L₀) * scaledChannelValue K f₀ i x) := by
  simp only [channelCoefficientSlot, scaledKernel, scaledDensity]
  rw [convolveAt_const_mul_kernel, convolveAt_const_mul_density, Real.exp_neg]
  rfl

/-- The density slot of the witness, in closed form. -/
lemma scaledChannelDensitySlot_eq
    (K : Flavor → ℝ → ℝ → ℝ) (f₀ : Flavor → ℝ → ℝ)
    (i : Flavor) (x Q2 μR2 L₀ L : ℝ) :
    channelDensitySlot (scaledKernel K) (scaledDensity f₀) i x Q2 μR2 L₀ L
      = Real.exp L₀ * (Real.exp (-L) * scaledChannelValue K f₀ i x) := by
  simp only [channelDensitySlot, scaledKernel, scaledDensity]
  rw [convolveAt_const_mul_kernel, convolveAt_const_mul_density, Real.exp_neg]
  rfl

/-- The witness channel is factorization-scale independent. -/
lemma scaledChannelLog_eq
    (K : Flavor → ℝ → ℝ → ℝ) (f₀ : Flavor → ℝ → ℝ)
    (i : Flavor) (x Q2 μR2 L : ℝ) :
    channelLog (scaledKernel K) (scaledDensity f₀) i x Q2 μR2 L
      = scaledChannelValue K f₀ i x := by
  have h : channelLog (scaledKernel K) (scaledDensity f₀) i x Q2 μR2 L
      = Real.exp L * (Real.exp (-L) * scaledChannelValue K f₀ i x) :=
    scaledChannelDensitySlot_eq K f₀ i x Q2 μR2 L L
  rw [h, ← mul_assoc, exp_mul_exp_neg, one_mul]

/-- The coefficient function's scale derivative of the witness is the channel value. -/
lemma scaledCoefficientDeriv
    (K : Flavor → ℝ → ℝ → ℝ) (f₀ : Flavor → ℝ → ℝ)
    (i : Flavor) (x Q2 μR2 L : ℝ) :
    HasDerivAt (channelCoefficientSlot (scaledKernel K) (scaledDensity f₀) i x Q2 μR2 L)
      (scaledChannelValue K f₀ i x) L := by
  have hfun : channelCoefficientSlot (scaledKernel K) (scaledDensity f₀) i x Q2 μR2 L
      = fun l => Real.exp l * (Real.exp (-L) * scaledChannelValue K f₀ i x) := by
    funext l
    exact scaledChannelCoefficientSlot_eq K f₀ i x Q2 μR2 L l
  have hval : Real.exp L * (Real.exp (-L) * scaledChannelValue K f₀ i x)
      = scaledChannelValue K f₀ i x := by
    rw [← mul_assoc, exp_mul_exp_neg, one_mul]
  rw [hfun]
  have hd := (Real.hasDerivAt_exp L).mul_const
    (Real.exp (-L) * scaledChannelValue K f₀ i x)
  rwa [hval] at hd

/-- The density's scale derivative of the witness is minus the channel value. -/
lemma scaledDensityDeriv
    (K : Flavor → ℝ → ℝ → ℝ) (f₀ : Flavor → ℝ → ℝ)
    (i : Flavor) (x Q2 μR2 L : ℝ) :
    HasDerivAt (channelDensitySlot (scaledKernel K) (scaledDensity f₀) i x Q2 μR2 L)
      (-scaledChannelValue K f₀ i x) L := by
  have hfun : channelDensitySlot (scaledKernel K) (scaledDensity f₀) i x Q2 μR2 L
      = fun l => Real.exp L * (Real.exp (-l) * scaledChannelValue K f₀ i x) := by
    funext l
    exact scaledChannelDensitySlot_eq K f₀ i x Q2 μR2 L l
  have hexp : HasDerivAt (fun l : ℝ => Real.exp (-l)) (Real.exp (-L) * (-1)) L :=
    (hasDerivAt_neg' L).exp
  have hd := (hexp.mul_const (scaledChannelValue K f₀ i x)).const_mul (Real.exp L)
  have hval : Real.exp L * (Real.exp (-L) * (-1) * scaledChannelValue K f₀ i x)
      = -scaledChannelValue K f₀ i x := by
    calc Real.exp L * (Real.exp (-L) * (-1) * scaledChannelValue K f₀ i x)
        = Real.exp L * Real.exp (-L) * (-1 * scaledChannelValue K f₀ i x) := by
          ring
      _ = -scaledChannelValue K f₀ i x := by
          rw [exp_mul_exp_neg]
          ring
  rw [hfun, ← hval]
  exact hd

/-- **The witness.** The hypotheses of `ScaleDerivatives` hold for the scaled coefficient
function and density, with the two derivatives `+scaledChannelValue` and
`-scaledChannelValue`. They are non-zero whenever the channel value is, and they satisfy the
compensation. -/
lemma scaledScaleDerivatives [Fintype Flavor]
    (K : Flavor → ℝ → ℝ → ℝ) (f₀ : Flavor → ℝ → ℝ)
    (x Q2 μR2 : ℝ) :
    ScaleDerivatives (scaledKernel K) (scaledDensity f₀) x Q2 μR2
      (fun i _ => scaledChannelValue K f₀ i x)
      (fun i _ => -scaledChannelValue K f₀ i x) where
  coefficientDeriv i L := scaledCoefficientDeriv K f₀ i x Q2 μR2 L
  densityDeriv i L := scaledDensityDeriv K f₀ i x Q2 μR2 L
  chainRule i L := by
    have hfun : channelLog (scaledKernel K) (scaledDensity f₀) i x Q2 μR2
        = fun _ : ℝ => scaledChannelValue K f₀ i x := by
      funext l
      exact scaledChannelLog_eq K f₀ i x Q2 μR2 l
    have hval : scaledChannelValue K f₀ i x + -scaledChannelValue K f₀ i x = 0 := by
      ring
    rw [hfun, hval]
    exact hasDerivAt_const L _

/-- The witness satisfies the compensation. -/
lemma scaledCompensation [Fintype Flavor]
    (K : Flavor → ℝ → ℝ → ℝ) (f₀ : Flavor → ℝ → ℝ) (x : ℝ) (L : ℝ) :
    ∑ i, ((fun i _ => scaledChannelValue K f₀ i x) i L
      + (fun i _ => -scaledChannelValue K f₀ i x) i L) = 0 := by
  simp

/-- The witness observable is factorization-scale independent. -/
lemma scaled_isFactorizationScaleIndependent [Fintype Flavor]
    (K : Flavor → ℝ → ℝ → ℝ) (f₀ : Flavor → ℝ → ℝ) (x Q2 μR2 : ℝ) :
    IsFactorizationScaleIndependent (scaledKernel K) (scaledDensity f₀) x Q2 μR2 :=
  (isFactorizationScaleIndependent_iff_compensation
    (scaledScaleDerivatives K f₀ x Q2 μR2)).mpr (scaledCompensation K f₀ x)

end Scales
end Factorization
end QFT
end Physlib
