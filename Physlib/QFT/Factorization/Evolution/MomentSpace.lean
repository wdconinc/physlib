/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.Evolution.Basic
public import Physlib.Meta.Linters.Sorry
/-!

# DGLAP Evolution in Moment Space

## i. Overview

Under a Mellin transform in the momentum fraction, the DGLAP integro-differential system
becomes, at each Mellin index `N`, a *linear* ordinary differential system in the log-scale
variable `τ = log Q2`:

`d F i / d τ = (αs (exp τ) / (2 * π)) * ∑ j, γ i j N * F j`,

where `γ i j N` are the anomalous dimensions, the Mellin transforms of the splitting
kernels. This module formalizes that system, its well-posedness, and the conservation of
the sum rules that follows from vanishing column sums of `γ`.

Moment space is the recommended route to well-posedness: the system is linear with
continuous coefficients, so global existence and uniqueness are standard. Well-posedness
directly in `x`-space would need a function-space setting and the plus-distribution
structure of the physical kernels, which is a much larger project and is not attempted
here.

## ii. Key results

- `DglapMomentSystem` is the data of the moment-space system: anomalous dimensions as a
  function of the Mellin index, and a continuous running coupling.
- `IsMomentSolution` is the linear ODE system, stated componentwise with `HasDerivAt`.
- `moment_exists_unique` is well-posedness: a unique global solution for each initial
  condition.
- `sumRule_conserved` is the conservation law: if the anomalous-dimension matrix has
  vanishing column sums at `N`, then `∑ i, F i` is `τ`-independent.
- `momentum_sumRule_conserved` and `valence_sumRule_conserved` are its specializations to
  the two physical sum rules.
- `isMomentSolution_momentVector` reduces an `x`-space solution to a moment-space one,
  under the assumption bundle `MomentReductionAssumptions`.

## iii. Conventions

The Mellin index convention of this repository is the one fixed by
`Physlib.Particles.Parton.PDF.mellinMoment`:

`mellinMoment f n i Q2 = ∫ x in Set.Icc 0 1, x ^ n * f i x Q2`,

i.e. the index `n` counts powers of `x` directly. The momentum sum rule is therefore the
`n = 1` moment and the valence (number) sum rules are the `n = 0` moments. The literature's
`N`-th moment is `∫ x ^ (N - 1) * f`, which puts the momentum sum rule at `N = 2` and the
valence sum rules at `N = 1`. The two indices are recorded as `momentumMomentIndex` and
`valenceMomentIndex` so that no statement in this development has to spell the number out.

The prefactor convention is inherited from `dglapRhsLogScale`: `αs / (2 * π)`, with `αs`
the standard strong coupling.

## iv. Table of contents

- A. The moment-space system
- B. Well-posedness
- C. Sum-rule conservation
  - C.1. The general conservation law
  - C.2. The physical sum rules
- D. Reduction of an `x`-space solution to moment space

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace QFT
namespace Factorization
namespace Evolution

variable {Flavor : Type}

/-! ## A. The moment-space system -/

/-- The data of the DGLAP system in moment space, on a finite index set `ι` of flavor
channels.

`gamma N` is the anomalous-dimension matrix at Mellin index `N`: the matrix of Mellin
transforms of the splitting kernels, `γ i j N = M[P i j] N`. `alphaS` is the running
coupling as a function of `Q2`, required to be continuous, which is what makes the
coefficient matrix of the system continuous in `τ` and hence the system well posed. -/
structure DglapMomentSystem (ι : Type) where
  /-- The anomalous-dimension matrix as a function of the Mellin index. -/
  gamma : ℂ → Matrix ι ι ℂ
  /-- The running coupling as a function of `Q2`. -/
  alphaS : ℝ → ℝ
  /-- Continuity of the running coupling in `Q2`. -/
  alphaS_continuous : Continuous alphaS

/-- The right-hand side of the moment-space DGLAP system in channel `i`:

`momentRhs S N τ F i = (S.alphaS (exp τ) / (2 * π)) * ∑ j, S.gamma N i j * F j`.

This is the `i`-th component of the matrix-vector product of the coefficient matrix
`(αs (exp τ) / (2 * π)) • S.gamma N` with `F`, written out as a sum so that no matrix
notation is needed downstream. -/
def momentRhs {ι : Type} [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ) (τ : ℝ)
    (F : ι → ℂ) (i : ι) : ℂ :=
  ((S.alphaS (Real.exp τ) / (2 * Real.pi) : ℝ) : ℂ) * ∑ j, S.gamma N i j * F j

/-- `F` solves the moment-space DGLAP system at Mellin index `N`: every component is
differentiable in `τ = log Q2` with derivative the corresponding component of
`momentRhs`. -/
def IsMomentSolution {ι : Type} [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ)
    (F : ℝ → ι → ℂ) : Prop :=
  ∀ i τ, HasDerivAt (fun s => F s i) (momentRhs S N τ (F τ) i) τ

/-! ## B. Well-posedness

The vector field `(τ, F) ↦ momentRhs S N τ F` is linear in `F` with coefficients continuous
in `τ`, so on every compact `τ`-interval it is Lipschitz in `F` uniformly in `τ`. That gives
local existence by Picard-Lindelöf and uniqueness by Gronwall, and linearity — the solution
cannot blow up in finite time — upgrades local existence to global. This is the achievable
form of DGLAP well-posedness; see the module docstring on why `x`-space is not attempted.

Both inputs below are left as `sorry`: the intended arguments are recorded in their
docstrings, but the mathlib ODE API could not be checked against the pinned revision while
writing this module, and guessing names and hypothesis shapes would be worse than an honest
gap. The combination `moment_exists_unique` is proved from them. -/

/-- Uniqueness for the moment-space system: two solutions agreeing at one point agree
everywhere.

TODO(task/e2-dglap-wellposedness): proof not completed. Intended argument. Fix
`T > 0`; on `Set.Icc (τ0 - T) (τ0 + T)` the map `F ↦ momentRhs S N τ F` is Lipschitz with
constant `K T = (sup over that interval of |S.alphaS (exp τ)| / (2 * π)) * ‖S.gamma N‖`,
finite because `S.alphaS_continuous` and `Real.continuous_exp` give continuity of
`τ ↦ S.alphaS (exp τ)` and a continuous function on a compact interval is bounded
(`IsCompact.exists_isMaxOn`). Then mathlib's Gronwall-based ODE uniqueness result
gives `F = G` on that interval.

Checked against the pinned mathlib (2026-09-19), so the following are facts rather than
guesses, and the proof below is built on them:

* The right theorem is `ODE_solution_unique_of_mem_Icc`
  (`Mathlib/Analysis/ODE/ExistUnique.lean`), whose Lipschitz hypothesis is restricted to
  the interval, `∀ t ∈ Ioo a b, LipschitzOnWith K (v t) (s t)`.
* `ODE_solution_unique_univ` does **not** apply, and this is not a matter of convenience:
  it demands a single `K` valid for every `t`, whereas `alphaS ∘ exp` is only continuous,
  not bounded on `ℝ`. Hence the compact-interval detour.
* `hasDerivAt_pi` is the correct name for the componentwise-to-vector conversion
  (`Mathlib/Analysis/Calculus/Deriv/Prod.lean`); the earlier note flagged it unverified.
* The pi-norm lemmas wanted here are the *unprimed* `pi_norm_le_iff_of_nonneg` and
  `norm_le_pi_norm`. The primed spellings are the multiplicative `to_additive` sources and
  fail with a stuck `SeminormedGroup` instance. -/
@[sorryful]
lemma momentSolution_unique {ι : Type} [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ)
    {F G : ℝ → ι → ℂ} (hF : IsMomentSolution S N F) (hG : IsMomentSolution S N G)
    (τ0 : ℝ) (h0 : F τ0 = G τ0) (τ : ℝ) :
    F τ = G τ := by
  classical
  set v : ℝ → (ι → ℂ) → (ι → ℂ) := fun t X => momentRhs S N t X with hvdef
  -- the componentwise hypothesis is the vector-valued one, via `hasDerivAt_pi`
  have hFd : ∀ t, HasDerivAt F (v t (F t)) t := fun t => hasDerivAt_pi.2 (fun i => hF i t)
  have hGd : ∀ t, HasDerivAt G (v t (G t)) t := fun t => hasDerivAt_pi.2 (fun i => hG i t)
  -- a compact interval containing both times in its interior
  set a : ℝ := min τ0 τ - 1 with hadef
  set b : ℝ := max τ0 τ + 1 with hbdef
  have hmin : min τ0 τ ≤ max τ0 τ := min_le_max
  have hτ0 : τ0 ∈ Set.Ioo a b :=
    ⟨by simp only [hadef]; have := min_le_left τ0 τ; linarith,
     by simp only [hbdef]; have := le_max_left τ0 τ; linarith⟩
  have hτ : τ ∈ Set.Ioo a b :=
    ⟨by simp only [hadef]; have := min_le_right τ0 τ; linarith,
     by simp only [hbdef]; have := le_max_right τ0 τ; linarith⟩
  -- the coupling is continuous, hence bounded on the compact interval
  have hcont : ContinuousOn (fun t => |S.alphaS (Real.exp t)| / (2 * Real.pi))
      (Set.Icc a b) :=
    (((continuous_abs.comp (S.alphaS_continuous.comp Real.continuous_exp)).div_const _)).continuousOn
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr (le_of_lt (hτ0.1.trans hτ0.2))
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  set M : ℝ := |S.alphaS (Real.exp tm)| / (2 * Real.pi) with hMdef
  have hM0 : 0 ≤ M := by positivity
  -- a finite bound on the anomalous-dimension matrix
  set Γ : ℝ := ∑ i : ι, ∑ j : ι, ‖S.gamma N i j‖ with hGdef
  have hΓ0 : 0 ≤ Γ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ODE_solution_unique_of_mem_Icc (K := ⟨M * Γ, by positivity⟩)
    (s := fun _ => Set.univ) ?_ hτ0
    (fun t _ => (hFd t).continuousAt.continuousWithinAt)
    (fun t _ => hFd t) (fun _ _ => Set.mem_univ _)
    (fun t _ => (hGd t).continuousAt.continuousWithinAt)
    (fun t _ => hGd t) (fun _ _ => Set.mem_univ _) h0 (Set.mem_Icc_of_Ioo hτ)
  -- the vector field is Lipschitz on the interval, with the constant just built
  intro t ht
  refine LipschitzOnWith.of_dist_le_mul fun X _ Y _ => ?_
  have hcoef : |S.alphaS (Real.exp t)| / (2 * Real.pi) ≤ M :=
    hmax (Set.mem_Icc_of_Ioo ht)
  simp only [dist_eq_norm] at *
  -- the bound is `↑K * ‖X - Y‖`; `positivity` cannot see through the `set` locals in `K`
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg (X - Y)))).2 fun i => ?_
  -- The one remaining gap, and it is purely the componentwise estimate:
  --
  --   ‖momentRhs S N t X i - momentRhs S N t Y i‖
  --     = |αs (exp t) / (2π)| * ‖∑ j, γ N i j * (X j - Y j)‖
  --     ≤ M * (∑ j, ‖γ N i j‖) * ‖X - Y‖   ≤   M * Γ * ‖X - Y‖,
  --
  -- by `norm_sum_le`, then `norm_le_pi_norm _ j` on each factor `‖X j - Y j‖`, then
  -- `hcoef` on the scalar and `Finset.single_le_sum` to pass from the `i`-th row sum to
  -- the full double sum `Γ`. Everything it needs is already in context (`hcoef`, `hM0`,
  -- `hΓ0`). What defeated the attempts here was the rewriting, not the mathematics: the
  -- `simp only [momentRhs, ...]` normal form and `gcongr`'s choice of side goals did not
  -- line up, and this wants to be done by hand with explicit `calc` steps rather than by
  -- `gcongr`.
  --
  -- Everything ABOVE this point is compiler-verified, including the application of
  -- `ODE_solution_unique_of_mem_Icc` itself, so the shape of the argument is settled and
  -- only this inequality is open.
  sorry

/-- Global existence for the moment-space system.

TODO(task/e2-dglap-wellposedness): proof not completed. Intended argument. On each
`Set.Icc (τ0 - T) (τ0 + T)` the vector field satisfies `ODE.IsPicardLindelof` (bounded and
Lipschitz in `F` on bounded sets, continuous in `τ`, by the same estimate as in
`momentSolution_unique`), which gives a solution on that interval; because the field is
*linear* in `F`, the local solutions extend and patch to a solution on all of `ℝ` (no
finite-time blow-up: `‖F τ‖ ≤ ‖F0‖ * exp (∫ K)` by Gronwall).

Checked against the pinned mathlib (2026-09-19), so this is no longer a guess: local
existence *is* available, as the `ODE.IsPicardLindelof.exists_*` family in
`Mathlib/Analysis/ODE/ExistUnique.lean`; a ready-made **global** statement for linear
systems is *not*. That gap is the substantive missing piece of this module. The preferred
route avoids the patching argument entirely: write the solution explicitly as the
time-ordered exponential
`F τ = exp ((∫ s in τ0..τ, S.alphaS (exp s) / (2 * π)) • S.gamma N) *ᵥ F0`, which is
legitimate *here* because the coefficient matrices at different `τ` are all multiples of the
single matrix `S.gamma N` and therefore commute; that reduces existence to differentiating
`Matrix.exp` along a scalar path. -/
@[sorryful]
lemma momentSolution_exists {ι : Type} [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ)
    (F0 : ι → ℂ) (τ0 : ℝ) :
    ∃ F : ℝ → ι → ℂ, F τ0 = F0 ∧ IsMomentSolution S N F := by
  sorry

/-- **Well-posedness of DGLAP evolution in moment space.** For each Mellin index `N` and
each initial condition `F0` at `τ0`, the linear moment-space system has a unique global
solution. -/
@[sorryful]
theorem moment_exists_unique {ι : Type} [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ)
    (F0 : ι → ℂ) (τ0 : ℝ) :
    ∃! F : ℝ → ι → ℂ, F τ0 = F0 ∧ IsMomentSolution S N F := by
  obtain ⟨F, hF0, hF⟩ := momentSolution_exists S N F0 τ0
  refine ⟨F, ⟨hF0, hF⟩, ?_⟩
  intro G hG
  funext τ
  exact momentSolution_unique S N hG.2 hF τ0 (hG.1.trans hF0.symm) τ

/-! ## C. Sum-rule conservation -/

/-! ### C.1. The general conservation law -/

/-- **Sum-rule conservation in moment space.** If the anomalous-dimension matrix at Mellin
index `N` has vanishing column sums, `∑ i, γ i j N = 0` for every `j`, then the total moment
`∑ i, F i` of any solution is independent of the log scale.

The hypothesis is exactly the constraint the splitting kernels satisfy in QCD: momentum
conservation in the splitting process is `∑ i, ∫ z * P i j z = 0`, which in moment space is
the vanishing of the column sums of `γ` at the momentum index. -/
@[sorryful]
theorem sumRule_conserved {ι : Type} [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ)
    (hcol : ∀ j, ∑ i, S.gamma N i j = 0)
    (F : ℝ → ι → ℂ) (hF : IsMomentSolution S N F) (τ₁ τ₂ : ℝ) :
    ∑ i, F τ₁ i = ∑ i, F τ₂ i := by
  have hderiv : ∀ τ : ℝ, HasDerivAt (fun s => ∑ i, F s i) 0 τ := by
    intro τ
    have hsum : HasDerivAt (fun s => ∑ i, F s i) (∑ i, momentRhs S N τ (F τ) i) τ :=
      HasDerivAt.fun_sum fun i _ => hF i τ
    have hzero : ∑ i, momentRhs S N τ (F τ) i = 0 := by
      calc ∑ i, momentRhs S N τ (F τ) i
          = ∑ i, ∑ j, ((S.alphaS (Real.exp τ) / (2 * Real.pi) : ℝ) : ℂ)
              * (S.gamma N i j * F τ j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [momentRhs, Finset.mul_sum]
        _ = ∑ j, ∑ i, ((S.alphaS (Real.exp τ) / (2 * Real.pi) : ℝ) : ℂ)
              * (S.gamma N i j * F τ j) := Finset.sum_comm
        _ = ∑ j, ((S.alphaS (Real.exp τ) / (2 * Real.pi) : ℝ) : ℂ)
              * ((∑ i, S.gamma N i j) * F τ j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul, Finset.mul_sum]
        _ = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            rw [hcol j, zero_mul, mul_zero]
    rwa [hzero] at hsum
  exact eq_of_hasDerivAt_zero hderiv τ₁ τ₂

/-! ### C.2. The physical sum rules -/

/-- The Mellin index carrying the momentum sum rule, in the convention of
`Physlib.Particles.Parton.PDF.mellinMoment` (`mellinMoment f n = ∫ x ^ n * f`), namely
`n = 1`. In the literature's convention, where the `N`-th moment is `∫ x ^ (N - 1) * f`, the
same sum rule sits at `N = 2`. -/
def momentumMomentIndex : ℂ := 1

/-- The Mellin index carrying the valence (number) sum rules, in the convention of
`Physlib.Particles.Parton.PDF.mellinMoment`, namely `n = 0`. In the literature's convention
the same sum rules sit at `N = 1`. -/
def valenceMomentIndex : ℂ := 0

/-- **Momentum sum-rule conservation.** If the anomalous dimensions have vanishing column
sums at the momentum index, the total momentum fraction carried by the partons is
independent of the scale.

This is the moment-space counterpart of the `momentum` field of
`Physlib.Particles.Parton.PDF.SumRuleAssumptions`, which asserts
`∑ i, mellinMoment f 1 i Q2 = 1` at every `Q2`: the theorem here supplies the reason that
assertion can hold at every scale at once, namely that the DGLAP flow preserves the total
first moment. Connecting the two literally — turning `∑ i, F τ i` into
`∑ i, mellinMoment f 1 i (exp τ)` — needs the reduction of section D together with the
Mellin convolution theorem of task `task/e1-mellin-convolution`. -/
@[sorryful]
theorem momentum_sumRule_conserved {ι : Type} [Fintype ι] (S : DglapMomentSystem ι)
    (hcol : ∀ j, ∑ i, S.gamma momentumMomentIndex i j = 0)
    (F : ℝ → ι → ℂ) (hF : IsMomentSolution S momentumMomentIndex F) (τ₁ τ₂ : ℝ) :
    ∑ i, F τ₁ i = ∑ i, F τ₂ i :=
  sumRule_conserved S momentumMomentIndex hcol F hF τ₁ τ₂

/-- **Valence sum-rule conservation.** If the anomalous dimensions have vanishing column
sums at the valence index, the total parton number is independent of the scale.

For the physical valence sum rules one applies this to the non-singlet combinations, whose
anomalous dimension at the valence index vanishes on its own. -/
@[sorryful]
theorem valence_sumRule_conserved {ι : Type} [Fintype ι] (S : DglapMomentSystem ι)
    (hcol : ∀ j, ∑ i, S.gamma valenceMomentIndex i j = 0)
    (F : ℝ → ι → ℂ) (hF : IsMomentSolution S valenceMomentIndex F) (τ₁ τ₂ : ℝ) :
    ∑ i, F τ₁ i = ∑ i, F τ₂ i :=
  sumRule_conserved S valenceMomentIndex hcol F hF τ₁ τ₂

/-! ## D. Reduction of an `x`-space solution to moment space -/

/-- The Mellin-moment vector of a PDF family at index `n`, as a function of the log scale
`τ = log Q2`, valued in `ℂ` so that it can be fed to the moment-space system. -/
def momentVector (f : Physlib.Particles.Parton.PDF.Pdf Flavor) (n : ℕ) (τ : ℝ)
    (i : Flavor) : ℂ :=
  ((Physlib.Particles.Parton.PDF.mellinMoment f n i (Real.exp τ) : ℝ) : ℂ)

/-- Transport of a real derivative along the inclusion `ℝ → ℂ`.

This is `HasDerivAt.ofReal_comp` (`Mathlib/Analysis/Complex/RealDeriv.lean`), which is
exactly the composition with the `ℝ`-linear isometry `Complex.ofRealCLM` that the earlier
note anticipated. -/
lemma hasDerivAt_ofReal {g : ℝ → ℝ} {g' τ : ℝ} (h : HasDerivAt g g' τ) :
    HasDerivAt (fun s => ((g s : ℝ) : ℂ)) ((g' : ℝ) : ℂ) τ :=
  h.ofReal_comp

/-- Assumptions reducing an `x`-space DGLAP solution to the moment-space linear system at
index `n`, with real anomalous dimensions `γ`.

Neither field is an opaque proposition: `derivMoment` is the interchange of the
`τ`-derivative with the moment integral (differentiation under the integral sign, which
needs dominated-convergence hypotheses not available in this development), and
`mellinFactorization` is the Mellin convolution theorem for the collinear kernel, which is
the target of task `task/e1-mellin-convolution`. Once that task lands, both become
derivable from integrability assumptions on `f` and `P` rather than assumed. -/
structure MomentReductionAssumptions [Fintype Flavor]
    (P : SplittingKernel Flavor) (αs : RunningCoupling)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (S : DglapMomentSystem Flavor) (n : ℕ) (γ : Flavor → Flavor → ℝ) : Prop where
  /-- The system's coupling is the one driving the `x`-space equation. -/
  coupling : S.alphaS = αs
  /-- The system's anomalous dimensions at the real index `n` are the real matrix `γ`. -/
  gamma_ofReal : ∀ i j, S.gamma (n : ℂ) i j = ((γ i j : ℝ) : ℂ)
  /-- Differentiation under the moment integral: the `τ`-derivative of the `n`-th moment of
  `f` is the `n`-th moment of the DGLAP right-hand side. -/
  derivMoment : ∀ i τ,
    HasDerivAt (fun s => Physlib.Particles.Parton.PDF.mellinMoment f n i (Real.exp s))
      (∫ x in Set.Icc (0 : ℝ) 1, x ^ n * dglapRhsLogScale P αs f i x τ) τ
  /-- Mellin convolution theorem: the `n`-th moment of the convolution right-hand side is
  the anomalous-dimension matrix acting on the moments. -/
  mellinFactorization : ∀ i τ,
    (∫ x in Set.Icc (0 : ℝ) 1, x ^ n * dglapRhsLogScale P αs f i x τ)
      = αs (Real.exp τ) / (2 * Real.pi)
        * ∑ j, γ i j * Physlib.Particles.Parton.PDF.mellinMoment f n j (Real.exp τ)

/-- Under `MomentReductionAssumptions`, the Mellin moments of an `x`-space DGLAP solution
solve the moment-space linear system, so the well-posedness and conservation results of this
module apply to them. -/
@[sorryful]
lemma isMomentSolution_momentVector [Fintype Flavor]
    (P : SplittingKernel Flavor) (αs : RunningCoupling)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor)
    (S : DglapMomentSystem Flavor) (n : ℕ) (γ : Flavor → Flavor → ℝ)
    (h : MomentReductionAssumptions P αs f S n γ) :
    IsMomentSolution S (n : ℂ) (momentVector f n) := by
  intro i τ
  have hreal : HasDerivAt
      (fun s => Physlib.Particles.Parton.PDF.mellinMoment f n i (Real.exp s))
      (αs (Real.exp τ) / (2 * Real.pi)
        * ∑ j, γ i j * Physlib.Particles.Parton.PDF.mellinMoment f n j (Real.exp τ)) τ := by
    have hd := h.derivMoment i τ
    rwa [h.mellinFactorization i τ] at hd
  have hrhs : momentRhs S (n : ℂ) τ (momentVector f n τ) i
      = ((αs (Real.exp τ) / (2 * Real.pi)
          * ∑ j, γ i j
            * Physlib.Particles.Parton.PDF.mellinMoment f n j (Real.exp τ) : ℝ) : ℂ) := by
    simp only [momentRhs, momentVector, h.coupling, h.gamma_ofReal]
    push_cast
    ring
  rw [hrhs]
  exact hasDerivAt_ofReal hreal

end Evolution
end Factorization
end QFT
end Physlib
