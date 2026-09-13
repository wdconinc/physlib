/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Factorization.Convolution.Mellin
public import Physlib.QFT.Factorization.Evolution.Basic
/-!

# The DGLAP operator as a collinear convolution

`Physlib.QFT.Factorization.Evolution.Basic` defines the DGLAP operator through the *general*
integral operator `convolveAt`, with an unconstrained two-variable splitting kernel
`P : Flavor → Flavor → ℝ → ℝ → ℝ`. Physically the splitting kernels are collinear: they have the
scaling form `P i j x z = z⁻¹ * p i j (x / z)` on `x ≤ z`. This module records that condition and
its two consequences: the operator is a flavor sum of collinear convolutions, and its Mellin
transform is the flavor sum of products, the factor `mellinDis (p i j) N` being the anomalous
dimension of the channel.

The moment-space transform is what turns DGLAP from an integro-differential equation into an
ordinary differential equation in the scale; the well-posedness of that equation is a separate
target and is not addressed here.

## Scope

As in `Physlib.QFT.Factorization.Convolution.Mellin`, only integrable coefficient functions are
covered. The real QCD splitting functions have `1 / (1 - z)` endpoint singularities regulated by
plus-distributions and are therefore *not* of the form assumed here; `IsCollinearSplittingKernel`
holds for the regular parts and for toy kernels, and the plus-distribution extension is a separate
development.

## Table of contents

- A. Collinear splitting kernels
- B. The operator in collinear form
- C. The operator in moment space

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib
namespace QFT
namespace Factorization
namespace Evolution

variable {Flavor : Type}

/-!

## A. Collinear splitting kernels

-/

/-- A splitting-kernel family has collinear (scaling) form with coefficient functions `p` when
every flavor channel is the collinear kernel of `p i j`, i.e.
`P i j x z = z⁻¹ * p i j (x / z)` on the support `x ≤ z`, `0 < z`, and `0` elsewhere. -/
def IsCollinearSplittingKernel (P : SplittingKernel Flavor)
    (p : Flavor → Flavor → ℝ → ℝ) : Prop :=
  ∀ i j x z, P i j x z = Convolution.collinearKernel (p i j) x z

/-- Each channel of a collinear splitting-kernel family is a collinear kernel. -/
lemma isCollinearKernel_of_isCollinearSplittingKernel
    {P : SplittingKernel Flavor} {p : Flavor → Flavor → ℝ → ℝ}
    (h : IsCollinearSplittingKernel P p) (i j : Flavor) :
    Convolution.IsCollinearKernel (fun x z => P i j x z) (p i j) :=
  fun x z => h i j x z

/-!

## B. The operator in collinear form

-/

/-- With collinear splitting kernels the DGLAP operator is the flavor sum of the collinear
convolutions `(p i j ⊗ f j) (x)`, i.e. `∑_j ∫_x^1 (dz / z) p i j (x / z) f j (z, Q²)`. -/
lemma dglapOperator_eq_sum_collinear [Fintype Flavor]
    (P : SplittingKernel Flavor) (p : Flavor → Flavor → ℝ → ℝ)
    (h : IsCollinearSplittingKernel P p)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor) (i : Flavor) (x Q2 : ℝ) :
    dglapOperator P f i x Q2
      = ∑ j, Convolution.convolveAt (Convolution.collinearKernel (p i j))
          (fun z => f j z Q2) x := by
  simp only [dglapOperator]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact (isCollinearKernel_of_isCollinearSplittingKernel h i j).convolveAt_eq _ x

/-!

## C. The operator in moment space

-/

/-- **The DGLAP operator in moment space.** For collinear splitting kernels, the Mellin transform
of the evolution operator is the flavor sum of products
`∑_j M[p i j] (N) * M[f j] (N)`; the coefficients `M[p i j] (N)` are the anomalous dimensions of
the channel. Together with the convolution theorem this is what reduces the evolution equation to
an ordinary differential equation in the scale at fixed `N`.

Depends on `Convolution.mellinDis_convolveAt` and therefore on the unproved change-of-variables
step; see `Convolution.integral_mellinIntegrand_of_mem`. -/
@[sorryful]
theorem mellinDis_dglapOperator [Fintype Flavor]
    (P : SplittingKernel Flavor) (p : Flavor → Flavor → ℝ → ℝ)
    (hP : IsCollinearSplittingKernel P p)
    (f : Physlib.Particles.Parton.PDF.Pdf Flavor) (i : Flavor) (Q2 : ℝ) (N : ℂ)
    (h : ∀ j, Convolution.MellinConvolutionAssumptions (p i j) (fun z => f j z Q2) N) :
    Convolution.mellinDis (fun x => dglapOperator P f i x Q2) N
      = ∑ j, Convolution.mellinDis (p i j) N
          * Convolution.mellinDis (fun z => f j z Q2) N := by
  have hop : (fun x => dglapOperator P f i x Q2)
      = fun x => ∑ j, Convolution.convolveAt (Convolution.collinearKernel (p i j))
          (fun z => f j z Q2) x :=
    funext (fun x => dglapOperator_eq_sum_collinear P p hP f i x Q2)
  rw [hop, Convolution.mellinDis_finsetSum Finset.univ _ N
    (fun j _ => (h j).convolutionConvergent)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact Convolution.mellinDis_convolveAt (p i j) (fun z => f j z Q2) N (h j)

end Evolution
end Factorization
end QFT
end Physlib
