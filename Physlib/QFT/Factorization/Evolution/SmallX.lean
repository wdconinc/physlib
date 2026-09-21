/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.Evolution.Basic
/-!

# Small-`x` evolution: the Cauchy problem for BFKL and Balitsky-Kovchegov

## i. Overview

At small momentum fraction `x` the evolution variable is the rapidity `Y = log (1 / x)` and
the evolving object is the dipole scattering amplitude, not a parton density. Leading-order
Balitsky-Kovchegov (BK) evolution has the shape

`∂ N / ∂ Y = K N - B (N, N)`,

with `K` the (linear) BFKL kernel and `B` the quadratic dipole term whose minus sign is the
saturation effect. BFKL evolution is the same equation with `B` dropped.

This module formalizes that Cauchy problem *abstractly*: the amplitude is a point of a real
Banach space `E`, the BFKL kernel is a bounded linear operator on `E`, and the dipole term
is a bounded bilinear map. What is proved is exactly what that structure supports, which is
strictly less than well-posedness of the physical equation; see `## iii. Conventions` for
the four places where the gap is real.

The point of interest is that the linear and non-linear cases separate differently from how
one might expect by analogy with `Physlib.QFT.Factorization.Evolution.MomentSpace`, where
DGLAP in moment space is a *linear* system with a unique *global* solution:

- **Uniqueness is still global for BK** (`bkSolution_unique`). The quadratic term does not
  break it. The reason is that a solution defined on all of `ℝ` is continuous, hence bounded
  on every compact rapidity interval, hence confined to a ball on which the vector field is
  Lipschitz.
- **Existence is only local** (`bk_exists_local`), and this is not an artefact of the proof:
  `exists_no_global_bkSolution` exhibits a system of exactly this algebraic shape, with a
  bounded kernel and a bounded dipole pairing, whose solution does not exist globally. So
  global existence cannot be deduced from the abstract structure; it needs the sign of the
  physical dipole term and the unitarity bound `0 ≤ N ≤ 1`, neither of which is formalized
  here.
- **For BFKL the global statement does hold** (`bfkl_exists_unique`), with the solution the
  operator exponential of the kernel.

## ii. Key results

- `SmallXSystem` is the data: a bounded BFKL kernel and a bounded dipole pairing.
- `bkRhs` is the BK right-hand side and `IsBkSolution` the Cauchy problem in rapidity;
  `IsBfklSolution` is the same for the linearized system.
- `bkRhs_lipschitzOnWith` is the Lipschitz estimate on a ball, with the explicit constant
  `‖K‖ + 2 R ‖B‖` that carries all the non-linearity.
- `bkSolution_unique_on_Icc` and `bkSolution_unique` are uniqueness, on an interval and
  globally.
- `bk_exists_local` is local existence in rapidity.
- `bfkl_exists_unique` is global well-posedness of the linearized (BFKL) system.
- `exists_no_global_bkSolution` is the failure of global existence for the quadratic system.
- `norm_bkRhs_sub_bfkl` is the quantitative dilute limit: BFKL approximates BK to an error
  quadratic in the amplitude.

## iii. Conventions

The evolution variable is the rapidity `Y`, increasing towards small `x`; there is no
`log Q2` here and no running coupling as a function of `Y`. Leading-order BFKL and BK have a
fixed coupling, which is absorbed into `bfklKernel` and `dipolePairing`. Running-coupling BK
puts the coupling inside the kernel, at a dipole-size-dependent scale; that is a different
(and `Y`-dependent) kernel and is *not* covered by this module.

Four honest gaps, none of them papered over:

1. `E` is an abstract Banach space. The dipole space -- functions of the transverse dipole
   vector `r` and impact parameter `b` -- is not constructed, and neither is the physical
   BK kernel as an operator on it. Every statement below is about the algebraic shape of the
   equation, not about the leading-order kernel.
2. `bfklKernel` is *bounded*. The physical LO BFKL operator is not bounded on the natural
   sup-norm dipole space: its eigenvalues `χ (γ) = 2 ψ (1) - ψ (γ) - ψ (1 - γ)` are
   unbounded as `γ → 0` or `γ → 1`. Boundedness is therefore a genuine restriction, met
   after a cutoff on dipole sizes or on a space with a restricted Mellin contour, and not by
   the LO kernel on its natural domain.
3. `dipolePairing` is bounded bilinear. This assumption is the mild one: the non-linear term
   is the dipole kernel integrated against a product of two amplitudes, so an integrable
   kernel gives `‖B (N, N)‖ ≤ ‖K‖₁ ‖N‖ ^ 2` on a sup-norm space.
4. The unitarity bound is absent. That `0 ≤ N ≤ 1` is preserved by BK -- the a priori bound
   that rules out blow-up and upgrades local to global existence for the *physical* equation
   -- is not stated or used anywhere below. `exists_no_global_bkSolution` is precisely the
   statement that without it the abstract structure is not enough.

## iv. Table of contents

- A. The small-`x` evolution system
- B. The Lipschitz estimate
- C. Uniqueness
  - C.1. On a rapidity interval
  - C.2. Globally in rapidity
- D. Local existence
- E. BFKL: global well-posedness of the linearized system
- F. Failure of global existence for the quadratic system

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace Factorization
namespace Evolution

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## A. The small-`x` evolution system -/

/-- The data of a leading-order small-`x` evolution system on a Banach space `E` of dipole
amplitudes.

`bfklKernel` is the linear BFKL kernel, assumed to be a bounded operator on `E`.
`dipolePairing` is the quadratic dipole term of the Balitsky-Kovchegov equation, assumed to
be a bounded bilinear map; in the physical equation it is the dipole kernel integrated
against the product `N (x, z) N (z, y)`. Both fields are named for what they are, and both
assumptions are restrictions on which equations this development covers, discussed in the
module docstring. -/
structure SmallXSystem (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The BFKL kernel, as a bounded linear operator on the space of dipole amplitudes. -/
  bfklKernel : E →L[ℝ] E
  /-- The quadratic dipole term of the BK equation, as a bounded bilinear map. -/
  dipolePairing : E →L[ℝ] E →L[ℝ] E

/-- The right-hand side of the Balitsky-Kovchegov equation:

`bkRhs S N = S.bfklKernel N - S.dipolePairing N N`.

The minus sign is the saturation sign: the quadratic term subtracts from the linear BFKL
growth. -/
def bkRhs (S : SmallXSystem E) (N : E) : E :=
  S.bfklKernel N - S.dipolePairing N N

/-- The linearization of a small-`x` system at zero amplitude: the same BFKL kernel with the
dipole term dropped. This is the BFKL system. -/
def SmallXSystem.linearized (S : SmallXSystem E) : SmallXSystem E where
  bfklKernel := S.bfklKernel
  dipolePairing := 0

@[simp]
lemma SmallXSystem.linearized_bfklKernel (S : SmallXSystem E) :
    S.linearized.bfklKernel = S.bfklKernel := rfl

@[simp]
lemma bkRhs_linearized (S : SmallXSystem E) (N : E) :
    bkRhs S.linearized N = S.bfklKernel N := by
  simp [bkRhs, SmallXSystem.linearized]

/-- `N` solves the Balitsky-Kovchegov equation in rapidity: it is differentiable in `Y` at
every rapidity with derivative `bkRhs S (N Y)`. -/
def IsBkSolution (S : SmallXSystem E) (N : ℝ → E) : Prop :=
  ∀ Y, HasDerivAt N (bkRhs S (N Y)) Y

/-- `N` solves the BFKL equation in rapidity, i.e. the Balitsky-Kovchegov equation of the
linearized system. -/
def IsBfklSolution (S : SmallXSystem E) (N : ℝ → E) : Prop :=
  IsBkSolution S.linearized N

lemma isBfklSolution_iff (S : SmallXSystem E) (N : ℝ → E) :
    IsBfklSolution S N ↔ ∀ Y, HasDerivAt N (S.bfklKernel (N Y)) Y := by
  simp [IsBfklSolution, IsBkSolution]

/-- **The dilute limit is quadratically accurate.** The BFKL right-hand side differs from
the BK right-hand side by at most `‖B‖ ‖N‖ ^ 2`, so BFKL is the small-amplitude limit of BK
with a controlled error. This is the precise sense in which `bfklKernel` deserves its
name. -/
lemma norm_bkRhs_sub_bfkl (S : SmallXSystem E) (N : E) :
    ‖bkRhs S N - S.bfklKernel N‖ ≤ ‖S.dipolePairing‖ * ‖N‖ ^ 2 := by
  have h : bkRhs S N - S.bfklKernel N = -(S.dipolePairing N N) := by
    simp [bkRhs]
  rw [h, norm_neg]
  calc ‖S.dipolePairing N N‖
      ≤ ‖S.dipolePairing‖ * ‖N‖ * ‖N‖ := S.dipolePairing.le_opNorm₂ N N
    _ = ‖S.dipolePairing‖ * ‖N‖ ^ 2 := by ring

/-! ## B. The Lipschitz estimate

The whole difference between BFKL and BK sits in this estimate. For the linear system the
Lipschitz constant is `‖K‖`, valid on all of `E`. For BK the constant grows with the radius
of the ball one restricts to, and there is no constant valid on all of `E`; that is what
forces every statement downstream either onto a ball or onto a bounded rapidity interval. -/

/-- The algebraic identity behind the Lipschitz estimate: the difference of two values of
the BK right-hand side, with the quadratic term split so that each summand is linear in
`X - Y`. -/
lemma bkRhs_sub (S : SmallXSystem E) (X Y : E) :
    bkRhs S X - bkRhs S Y
      = S.bfklKernel (X - Y)
        - (S.dipolePairing (X - Y) X + S.dipolePairing Y (X - Y)) := by
  simp only [bkRhs, map_sub, ContinuousLinearMap.sub_apply]
  abel

/-- **The BK vector field is Lipschitz on balls**, with constant `‖K‖ + 2 R ‖B‖` on the
closed ball of radius `R`.

The constant depends on `R`: unlike the DGLAP moment system of
`Physlib.QFT.Factorization.Evolution.MomentSpace`, whose vector field is Lipschitz with a
constant depending only on the rapidity interval, here there is no single constant valid on
all of `E`. -/
lemma bkRhs_lipschitzOnWith (S : SmallXSystem E) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith
      ⟨‖S.bfklKernel‖ + 2 * R * ‖S.dipolePairing‖,
        add_nonneg (norm_nonneg S.bfklKernel)
          (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * R) (norm_nonneg S.dipolePairing))⟩
      (bkRhs S) (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun X hX Y hY => ?_
  have hXn : ‖X‖ ≤ R := by simpa using hX
  have hYn : ‖Y‖ ≤ R := by simpa using hY
  have h1 : ‖S.bfklKernel (X - Y)‖ ≤ ‖S.bfklKernel‖ * ‖X - Y‖ :=
    S.bfklKernel.le_opNorm _
  have h2 : ‖S.dipolePairing (X - Y) X‖ ≤ ‖S.dipolePairing‖ * ‖X - Y‖ * R := by
    refine (S.dipolePairing.le_opNorm₂ _ _).trans ?_
    have hnn : 0 ≤ ‖S.dipolePairing‖ * ‖X - Y‖ := by positivity
    exact mul_le_mul_of_nonneg_left hXn hnn
  have h3 : ‖S.dipolePairing Y (X - Y)‖ ≤ ‖S.dipolePairing‖ * R * ‖X - Y‖ := by
    refine (S.dipolePairing.le_opNorm₂ _ _).trans ?_
    have hnn : 0 ≤ ‖X - Y‖ := norm_nonneg _
    have hmid : ‖S.dipolePairing‖ * ‖Y‖ ≤ ‖S.dipolePairing‖ * R :=
      mul_le_mul_of_nonneg_left hYn (norm_nonneg S.dipolePairing)
    exact mul_le_mul_of_nonneg_right hmid hnn
  simp only [dist_eq_norm]
  calc ‖bkRhs S X - bkRhs S Y‖
      = ‖S.bfklKernel (X - Y)
          - (S.dipolePairing (X - Y) X + S.dipolePairing Y (X - Y))‖ := by
        rw [bkRhs_sub]
    _ ≤ ‖S.bfklKernel (X - Y)‖
          + ‖S.dipolePairing (X - Y) X + S.dipolePairing Y (X - Y)‖ := norm_sub_le _ _
    _ ≤ ‖S.bfklKernel (X - Y)‖
          + (‖S.dipolePairing (X - Y) X‖ + ‖S.dipolePairing Y (X - Y)‖) := by
        have htri := norm_add_le (S.dipolePairing (X - Y) X) (S.dipolePairing Y (X - Y))
        linarith
    _ ≤ ‖S.bfklKernel‖ * ‖X - Y‖
          + (‖S.dipolePairing‖ * ‖X - Y‖ * R + ‖S.dipolePairing‖ * R * ‖X - Y‖) :=
        add_le_add h1 (add_le_add h2 h3)
    _ = (‖S.bfklKernel‖ + 2 * R * ‖S.dipolePairing‖) * ‖X - Y‖ := by ring

/-! ## C. Uniqueness -/

/-! ### C.1. On a rapidity interval -/

/-- **Uniqueness of BK solutions on a rapidity interval.** Two solutions of the
Balitsky-Kovchegov equation on `Set.Ioo a b`, continuous up to the endpoints and agreeing at
one interior rapidity, agree on all of `Set.Icc a b`.

No bound on the solutions is assumed: continuity on the compact interval supplies one, and
`bkRhs_lipschitzOnWith` is then applied on a ball large enough to contain both solutions. -/
lemma bkSolution_unique_on_Icc (S : SmallXSystem E) {F G : ℝ → E} {a b Y₀ : ℝ}
    (hY₀ : Y₀ ∈ Set.Ioo a b)
    (hFc : ContinuousOn F (Set.Icc a b)) (hGc : ContinuousOn G (Set.Icc a b))
    (hF : ∀ Y ∈ Set.Ioo a b, HasDerivAt F (bkRhs S (F Y)) Y)
    (hG : ∀ Y ∈ Set.Ioo a b, HasDerivAt G (bkRhs S (G Y)) Y)
    (h0 : F Y₀ = G Y₀) :
    Set.EqOn F G (Set.Icc a b) := by
  obtain ⟨R₁, hR₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc
  obtain ⟨R₂, hR₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc
  set R : ℝ := max (max R₁ R₂) 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hle₁ : R₁ ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hle₂ : R₂ ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  have hFR : ∀ Y ∈ Set.Ioo a b, F Y ∈ Metric.closedBall (0 : E) R := by
    intro Y hY
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (hR₁ Y (Set.mem_Icc_of_Ioo hY)).trans hle₁
  have hGR : ∀ Y ∈ Set.Ioo a b, G Y ∈ Metric.closedBall (0 : E) R := by
    intro Y hY
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (hR₂ Y (Set.mem_Icc_of_Ioo hY)).trans hle₂
  exact ODE_solution_unique_of_mem_Icc (v := fun _ => bkRhs S)
    (s := fun _ => Metric.closedBall (0 : E) R)
    (fun _ _ => bkRhs_lipschitzOnWith S hR0) hY₀ hFc hF hFR hGc hG hGR h0

/-! ### C.2. Globally in rapidity -/

/-- **Uniqueness of BK solutions is global.** Two solutions of the Balitsky-Kovchegov
equation defined on all of `ℝ` and agreeing at one rapidity are equal.

The quadratic term does not obstruct this, which is worth stating because it is the
non-linearity that obstructs global *existence* (`exists_no_global_bkSolution`). A solution
defined on all of `ℝ` is continuous, hence bounded on every compact rapidity interval, hence
confined to a ball on which `bkRhs_lipschitzOnWith` gives a Lipschitz constant. -/
lemma bkSolution_unique (S : SmallXSystem E) {F G : ℝ → E}
    (hF : IsBkSolution S F) (hG : IsBkSolution S G)
    (Y₀ : ℝ) (h0 : F Y₀ = G Y₀) (Y : ℝ) :
    F Y = G Y := by
  have hFd : Differentiable ℝ F := fun t => (hF t).differentiableAt
  have hGd : Differentiable ℝ G := fun t => (hG t).differentiableAt
  set a : ℝ := min Y₀ Y - 1 with hadef
  set b : ℝ := max Y₀ Y + 1 with hbdef
  have hY₀ : Y₀ ∈ Set.Ioo a b :=
    ⟨by simp only [hadef]; have := min_le_left Y₀ Y; linarith,
     by simp only [hbdef]; have := le_max_left Y₀ Y; linarith⟩
  have hYm : Y ∈ Set.Icc a b :=
    ⟨by simp only [hadef]; have := min_le_right Y₀ Y; linarith,
     by simp only [hbdef]; have := le_max_right Y₀ Y; linarith⟩
  exact bkSolution_unique_on_Icc S hY₀ hFd.continuous.continuousOn
    hGd.continuous.continuousOn (fun t _ => hF t) (fun t _ => hG t) h0 hYm

/-! ## D. Local existence

The BK vector field is a bounded linear map minus a bounded bilinear map evaluated on the
diagonal, hence smooth, so Picard-Lindelöf applies at every amplitude. What it gives is a
solution on *some* rapidity interval around the initial rapidity, with no control on its
length beyond what the Lipschitz constant of section B provides. Section F shows that this
is the best that follows from the structure assumed here. -/

/-- The BK vector field is continuously differentiable. -/
lemma contDiff_bkRhs (S : SmallXSystem E) : ContDiff ℝ 1 (bkRhs S) := by
  have h1 : ContDiff ℝ 1 (fun N : E => S.bfklKernel N) := S.bfklKernel.contDiff
  have h2 : ContDiff ℝ 1 (fun N : E => S.dipolePairing N N) :=
    S.dipolePairing.contDiff.clm_apply contDiff_id
  exact h1.sub h2

/-- **Local existence in rapidity for the Balitsky-Kovchegov equation.** For every initial
amplitude `N₀` at rapidity `Y₀` there is a solution on some open rapidity interval around
`Y₀`.

The interval is not claimed to be all of `ℝ`, and by `exists_no_global_bkSolution` it cannot
be, for systems of this generality. -/
lemma bk_exists_local [CompleteSpace E] (S : SmallXSystem E) (N₀ : E) (Y₀ : ℝ) :
    ∃ N : ℝ → E, N Y₀ = N₀ ∧ ∃ ε > (0 : ℝ),
      ∀ Y ∈ Set.Ioo (Y₀ - ε) (Y₀ + ε), HasDerivAt N (bkRhs S (N Y)) Y :=
  (contDiff_bkRhs S).contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    Y₀

/-! ## E. BFKL: global well-posedness of the linearized system

For the linear system the solution can be written down: the coefficient operator is
independent of rapidity, so the solution is the operator exponential of `Y - Y₀` times the
kernel. This is the statement whose DGLAP analogue is left open in
`Physlib.QFT.Factorization.Evolution.MomentSpace` (`momentSolution_exists`); it is available
here because the kernel is a single bounded operator rather than a rapidity-dependent
multiple of a matrix. -/

/-- The BFKL evolution operator from rapidity `Y₀` to rapidity `Y`: the exponential of the
kernel. -/
def bfklEvolution [CompleteSpace E] (S : SmallXSystem E) (Y₀ Y : ℝ) : E →L[ℝ] E :=
  NormedSpace.exp ((Y - Y₀) • S.bfklKernel)

/-- The BFKL solution with initial amplitude `N₀` at rapidity `Y₀`. -/
def bfklFlow [CompleteSpace E] (S : SmallXSystem E) (N₀ : E) (Y₀ : ℝ) : ℝ → E :=
  fun Y => bfklEvolution S Y₀ Y N₀

@[simp]
lemma bfklFlow_self [CompleteSpace E] (S : SmallXSystem E) (N₀ : E) (Y₀ : ℝ) :
    bfklFlow S N₀ Y₀ Y₀ = N₀ := by
  simp only [bfklFlow, bfklEvolution, sub_self, zero_smul, NormedSpace.exp_zero]
  rfl

/-- The BFKL flow solves the BFKL equation. The derivative is computed by differentiating
the operator exponential along the scalar path `Y ↦ Y - Y₀` and commuting the kernel past
its own exponential. -/
lemma hasDerivAt_bfklFlow [CompleteSpace E] (S : SmallXSystem E) (N₀ : E) (Y₀ Y : ℝ) :
    HasDerivAt (bfklFlow S N₀ Y₀) (S.bfklKernel (bfklFlow S N₀ Y₀ Y)) Y := by
  -- The operator exponential is differentiated along the rapidity shift `u ↦ u - Y₀`. No
  -- type ascription is written on the operator-valued hypotheses: `E →L[ℝ] E` carries both
  -- a `ContinuousLinearMap` and a `NormedRing` additive structure, and stating the type by
  -- hand makes unification pick the wrong one. For the same reason the shift is taken with
  -- `HasDerivAt.comp_sub_const` rather than the general chain rule `HasDerivAt.scomp`,
  -- whose hypothesis `HasDerivAt g g' (h x)` is a higher-order pattern that does not
  -- unify here.
  have hcomp := HasDerivAt.comp_sub_const Y Y₀ (hasDerivAt_exp_smul_const S.bfklKernel (Y - Y₀))
  have hcomm : NormedSpace.exp ((Y - Y₀) • S.bfklKernel) * S.bfklKernel
      = S.bfklKernel * NormedSpace.exp ((Y - Y₀) • S.bfklKernel) :=
    (((Commute.refl S.bfklKernel).smul_right (Y - Y₀)).exp_right).eq.symm
  have happ := hcomp.clm_apply (hasDerivAt_const Y N₀)
  simp only [map_zero, add_zero, hcomm] at happ
  -- `show` forces the goal to be elaborated at default transparency, which is what unfolds
  -- `bfklFlow` and identifies multiplication in `E →L[ℝ] E` with composition; `simpa`
  -- matches only at reducible transparency and fails on both counts.
  show HasDerivAt (fun Z : ℝ => NormedSpace.exp ((Z - Y₀) • S.bfklKernel) N₀)
    (S.bfklKernel (NormedSpace.exp ((Y - Y₀) • S.bfklKernel) N₀)) Y
  exact happ

/-- **Well-posedness of BFKL evolution.** For every initial amplitude at every rapidity the
linearized small-`x` system has a unique global solution.

Existence is the operator exponential `bfklFlow`; uniqueness is the general BK uniqueness
statement `bkSolution_unique` applied to the linearized system. -/
theorem bfkl_exists_unique [CompleteSpace E] (S : SmallXSystem E) (N₀ : E) (Y₀ : ℝ) :
    ∃! N : ℝ → E, N Y₀ = N₀ ∧ IsBfklSolution S N := by
  refine ⟨bfklFlow S N₀ Y₀, ⟨bfklFlow_self S N₀ Y₀, ?_⟩, ?_⟩
  · rw [isBfklSolution_iff]
    exact fun Y => hasDerivAt_bfklFlow S N₀ Y₀ Y
  · rintro G ⟨hG0, hG⟩
    funext Y
    refine bkSolution_unique S.linearized hG ?_ Y₀ ?_ Y
    · intro Z
      simpa using hasDerivAt_bfklFlow S N₀ Y₀ Z
    · rw [hG0, bfklFlow_self]

/-! ## F. Failure of global existence for the quadratic system

Global existence is where the analogy with the linear DGLAP moment system breaks. It breaks
at the level of the *structure*, not of the proof technique: the system below has a bounded
BFKL kernel (zero) and a bounded dipole pairing, and no global solution from the initial
amplitude `1`.

The pairing used is the negative of multiplication, i.e. the *wrong* sign relative to
physical BK, where the quadratic term subtracts from the linear growth. That is the content
of the statement: the sign of the dipole term is load-bearing. With the physical sign and
the unitarity bound `0 ≤ N ≤ 1` there is no blow-up, but neither the sign convention alone
nor the abstract bounds assumed in `SmallXSystem` deliver that -- the unitarity bound is an
input this development does not have. -/

/-- The scalar equation `F' = F ^ 2` has no solution on all of `ℝ` with `F 0 = 1`.

This is the finite-rapidity blow-up, in its simplest form. Because `F` is non-decreasing and
`F 0 = 1`, it stays at least `1` on `Set.Icc 0 1`, so `Y ↦ -(F Y)⁻¹ - Y` is well defined
there and has zero derivative; being constant it forces `(F 1)⁻¹ = 0`, which contradicts
`1 ≤ F 1`. -/
lemma not_exists_global_solution_sq :
    ¬ ∃ F : ℝ → ℝ, F 0 = 1 ∧ ∀ Y, HasDerivAt F (F Y ^ 2) Y := by
  rintro ⟨F, hF0, hF⟩
  have hdiff : Differentiable ℝ F := fun y => (hF y).differentiableAt
  have hmono : Monotone F := by
    refine monotone_of_deriv_nonneg hdiff fun y => ?_
    rw [(hF y).deriv]
    positivity
  have hge : ∀ y ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ) ≤ F y := by
    intro y hy
    calc (1 : ℝ) = F 0 := hF0.symm
      _ ≤ F y := hmono hy.1
  have hne : ∀ y ∈ Set.Icc (0 : ℝ) 1, F y ≠ 0 := by
    intro y hy
    have := hge y hy
    linarith
  have hwc : ContinuousOn (fun y => -(F y)⁻¹ - y) (Set.Icc (0 : ℝ) 1) := by
    refine ContinuousOn.sub (ContinuousOn.neg ?_) continuousOn_id
    exact hdiff.continuous.continuousOn.inv₀ hne
  have hwd : ∀ y ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun y => -(F y)⁻¹ - y) 0 (Set.Ici y) y := by
    intro y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.le⟩
    have hsq : F y ^ 2 ≠ 0 := pow_ne_zero 2 (hne y hy')
    have hinv : HasDerivAt (fun z => (F z)⁻¹) (-1) y := by
      have h := (hF y).inv (hne y hy')
      rw [neg_div, div_self hsq] at h
      exact h
    have hval : HasDerivAt (fun z => -(F z)⁻¹ - z) (-(-1) - 1) y :=
      hinv.neg.sub (hasDerivAt_id y)
    have hz : (-(-1 : ℝ)) - 1 = 0 := by norm_num
    rw [hz] at hval
    exact hval.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hwc hwd 1 (Set.right_mem_Icc.2 zero_le_one)
  have h1 : (1 : ℝ) ≤ F 1 := hge 1 (Set.right_mem_Icc.2 zero_le_one)
  have hc2 : -(F 1)⁻¹ - 1 = -(F 0)⁻¹ - 0 := hconst
  rw [hF0, inv_one] at hc2
  have hzero : (F 1)⁻¹ = 0 := by linarith
  rw [inv_eq_zero.mp hzero] at h1
  linarith

/-- **Global existence fails for the quadratic system.** There is a small-`x` system with a
bounded BFKL kernel and a bounded dipole pairing, and an initial amplitude, for which the
Balitsky-Kovchegov equation has no solution defined for all rapidities.

Contrast `bfkl_exists_unique`, where the same statement holds for every linear system, and
`bkSolution_unique`, where uniqueness holds for every system including this one. The
obstruction is existence alone, and it is an obstruction of the structure, not of the proof
method: nothing short of an a priori bound on the amplitude can remove it. -/
lemma exists_no_global_bkSolution :
    ∃ (S : SmallXSystem ℝ) (N₀ Y₀ : ℝ), ¬ ∃ N : ℝ → ℝ, N Y₀ = N₀ ∧ IsBkSolution S N := by
  refine ⟨⟨0, -ContinuousLinearMap.mul ℝ ℝ⟩, 1, 0, ?_⟩
  rintro ⟨N, hN0, hN⟩
  refine not_exists_global_solution_sq ⟨N, hN0, fun Y => ?_⟩
  have h := hN Y
  simpa [bkRhs, pow_two] using h

end Evolution
end Factorization
end QFT
end Physlib
