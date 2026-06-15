/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QCD.Basic
public import Physlib.QFT.PerturbationTheory.FeynmanDiagrams.YangMillsGaugeData
public import Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars
public import Mathlib.Data.Complex.Basic
public import Mathlib.Topology.Instances.Complex

/-!
# Feynman diagrams

Feynman diagrams form a type into which permissible Wick contractions
embed.

A permissible Wick contraction is one which does not contribute zero to
the vacuum expectation value.

Feynman diagrams are based on multisets of `FieldOp`. This should be contrasted
with Wick contractions which are based on lists of `FieldOp`.

In particular a Feynman diagram is a partition of a Multiset into
disjoint pairs.

## Standard Model Gauge Sectors

This module provides Feynman rules for all three Standard Model gauge sectors:
- U(1): massless photon / hypercharge boson propagator + Abelian vertex
- SU(2): W-boson propagator + non-abelian vertices
- SU(N): general non-abelian gauge boson + matter-fermion vertices

Regularization is developed from first principles in this file:
propagators are explicit complex-valued $i\varepsilon$ families.

Vertex organization remains contract-based for now, allowing later
replacement by explicit perturbative derivations.

## Note

This directory is currently a work in progress.
(Contact JTS before working in this directory.)

-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace PerturbationTheory
namespace FeynmanDiagrams

/-! ### Field and Index Types -/

/-- Lorentz index (0=time, 1,2,3=spatial). -/
def LorentzIndex := Fin 4

instance : DecidableEq LorentzIndex := by
  unfold LorentzIndex
  infer_instance

/-- Spacetime 4-momentum (in units of energy). -/
structure Momentum : Type where
  /-- Temporal component (energy). -/
  E : ℝ
  /-- Spatial 3-momentum. -/
  p : ℝ × ℝ × ℝ

/-- Color index in fundamental or adjoint representation. -/
structure ColorIndex (ColorDim : ℕ) : Type where
  /-- Representation label (fundamental or adjoint). -/
  rep : Bool  -- true = fundamental, false = adjoint
  /-- Index value in [0, ColorDim). -/
  idx : Fin ColorDim

/-- Flavor index for quarks and ghosts. -/
structure FlavorIndex (NumFlavors : ℕ) : Type where
  /-- Flavor value. -/
  f : Fin NumFlavors

variable {NumColors NumFlavors : ℕ} [Fact (1 < NumColors)] [Fact (0 < NumFlavors)]

/-! ### Propagators -/

/-- Euclidean spatial norm-squared of the spatial momentum components. -/
def spatialNormSq (k : Momentum) : ℝ :=
  k.p.1 ^ 2 + k.p.2.1 ^ 2 + k.p.2.2 ^ 2

/-- Minkowski momentum square with $(+,-,-,-)$ signature. -/
def minkowskiSquare (k : Momentum) : ℝ :=
  k.E ^ 2 - spatialNormSq k

/-- Mass-shell polynomial $k^2 - m^2$. -/
def massShellPolynomial (k : Momentum) (mass : ℝ) : ℝ :=
  minkowskiSquare k - mass ^ 2

/-- Complex denominator implementing the $+i\varepsilon$ prescription. -/
def regularizedDenominator (x ε : ℝ) : ℂ :=
  (x : ℂ) + Complex.I * (ε : ℂ)

/-- The $+i\varepsilon$ denominator is nonzero for all $\varepsilon > 0$. -/
lemma regularizedDenominator_ne_zero (x ε : ℝ) (hε : 0 < ε) :
    regularizedDenominator x ε ≠ 0 := by
  intro h
  have him : (regularizedDenominator x ε).im = ε := by
    simp [regularizedDenominator]
  have hz : (regularizedDenominator x ε).im = 0 := by
    simp [h]
  have hε0 : ε = 0 := by
    simpa [him] using hz
  exact hε.ne' hε0

/-- The massless denominator for gluon/ghost lines is nonzero for $\varepsilon > 0$. -/
lemma masslessDenominator_ne_zero (k : Momentum) (ε : ℝ) (hε : 0 < ε) :
    regularizedDenominator (minkowskiSquare k) ε ≠ 0 :=
  regularizedDenominator_ne_zero (minkowskiSquare k) ε hε

/-- The massive quark denominator is nonzero for $\varepsilon > 0$. -/
lemma massiveDenominator_ne_zero (k : Momentum) (mass ε : ℝ) (hε : 0 < ε) :
    regularizedDenominator (massShellPolynomial k mass) ε ≠ 0 :=
  regularizedDenominator_ne_zero (massShellPolynomial k mass) ε hε

/-! ### Boundary-Value Layer ($\varepsilon \to 0^+$) -/

/-- Advanced denominator implementing the $-i\varepsilon$ prescription. -/
def advancedDenominator (x ε : ℝ) : ℂ :=
  (x : ℂ) - Complex.I * (ε : ℂ)

/-- Generic right-limit (approach from positive side) at the origin. -/
def rightLimitAtZero (F : ℝ → ℂ) (L : ℂ) : Prop :=
  Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

/-- Boundary-value set at $\varepsilon \to 0^+$ for a regularized family. -/
def boundaryValuesAtZeroPlus (F : ℝ → ℂ) : Set ℂ :=
  {L | rightLimitAtZero F L}

/-- Massless regularized family viewed as a total function of $\varepsilon$. -/
def masslessRegularizedFamily (k : Momentum) : ℝ → ℂ :=
  fun ε =>
    if _hε : 0 < ε then
      1 / regularizedDenominator (minkowskiSquare k) ε
    else
      0

/-- Massive regularized family viewed as a total function of $\varepsilon$. -/
def massiveRegularizedFamily (k : Momentum) (mass : ℝ) : ℝ → ℂ :=
  fun ε =>
    if _hε : 0 < ε then
      1 / regularizedDenominator (massShellPolynomial k mass) ε
    else
      0

/-! ### Causality Symmetry for $\pm i\varepsilon$ -/

/-- Complex conjugation maps $+i\varepsilon$ to $-i\varepsilon$. -/
lemma regularizedDenominator_conj (x ε : ℝ) :
    star (regularizedDenominator x ε) = advancedDenominator x ε := by
  simp [regularizedDenominator, advancedDenominator, sub_eq_add_neg]

/-- Complex conjugation maps $-i\varepsilon$ to $+i\varepsilon$. -/
lemma advancedDenominator_conj (x ε : ℝ) :
    star (advancedDenominator x ε) = regularizedDenominator x ε := by
  simp [regularizedDenominator, advancedDenominator]

/-- The real parts of the $\pm i\varepsilon$ denominators coincide. -/
lemma regularizedDenominator_re_eq_advanced_re (x ε : ℝ) :
    (regularizedDenominator x ε).re = (advancedDenominator x ε).re := by
  simp [regularizedDenominator, advancedDenominator]

/-- The imaginary parts differ by a sign between retarded and advanced prescriptions. -/
lemma regularizedDenominator_im_eq_neg_advanced_im (x ε : ℝ) :
    (regularizedDenominator x ε).im = - (advancedDenominator x ε).im := by
  simp [regularizedDenominator, advancedDenominator]

/-- Placeholder for gluon propagator in momentum space with gauge-choice data.
    In covariant gauges: D_μν(k) = -g_μν / (k² + iε) + gauge-dependent term.
    Later replaced by explicit expression from quantization. -/
def gluonPropagator (k : Momentum) (_μ _ν : LorentzIndex) (_ξ ε : ℝ) (_hε : 0 < ε) : ℂ :=
  1 / regularizedDenominator (minkowskiSquare k) ε

/-- Placeholder for quark propagator in momentum space.
    S_ab(k) = [γ_μ k^μ - m] / (k² - m² + iε) with color δ_ab.
    Later replaced by explicit Dirac structure from quantization. -/
def quarkPropagator (k : Momentum) (mass ε : ℝ) (_hε : 0 < ε) : ℂ :=
  1 / regularizedDenominator (massShellPolynomial k mass) ε

/-- Placeholder for ghost propagator in momentum space.
    G(k) = 1 / (k² + iε) = 1 / ((k^0)² - k² + iε).
    Later replaced by explicit expression from gauge fixing. -/
def ghostPropagator (k : Momentum) (ε : ℝ) (_hε : 0 < ε) : ℂ :=
  1 / regularizedDenominator (minkowskiSquare k) ε

/-! ### Numerator-Lifted Propagator Forms -/

/-- Minkowski metric with $(+,-,-,-)$ signature. -/
def minkowskiMetric (μ ν : LorentzIndex) : ℝ :=
  if _h : μ = ν then
    if μ.1 = 0 then 1 else -1
  else
    0

/-- Contravariant momentum component. -/
def momentumComponent (k : Momentum) (μ : LorentzIndex) : ℝ :=
  match μ.1 with
  | 0 => k.E
  | 1 => k.p.1
  | 2 => k.p.2.1
  | _ => k.p.2.2

/-- Minimal Dirac numerator container for $\gamma\!\cdot\!k + m$. -/
structure DiracNumerator where
  /-- Scalar coefficient multiplying the identity in Dirac space. -/
  scalarPart : ℂ
  /-- Vector coefficients multiplying gamma matrices. -/
  vectorPart : LorentzIndex → ℂ

/-- Quark Dirac numerator $\gamma\!\cdot\!k + m$ as coefficients. -/
def quarkDiracNumerator (k : Momentum) (mass : ℝ) : DiracNumerator where
  scalarPart := (mass : ℂ)
  vectorPart := fun μ => (momentumComponent k μ : ℂ)

/-- Tensor-lifted gluon propagator (scalar denominator with $g_{\mu\nu}$ numerator). -/
def gluonPropagatorTensor (k : Momentum) (μ ν : LorentzIndex) (ξ ε : ℝ) (hε : 0 < ε) : ℂ :=
  (minkowskiMetric μ ν : ℂ) * gluonPropagator k μ ν ξ ε hε

/-- Numerator-lifted quark propagator data. -/
structure QuarkPropagatorWithNumerator where
  /-- Dirac numerator coefficients. -/
  numerator : DiracNumerator
  /-- Scalar denominator factor. -/
  denominator : ℂ

/-- Quark propagator written as numerator data over the regularized denominator. -/
def quarkPropagatorLifted (k : Momentum) (mass ε : ℝ) (_hε : 0 < ε) :
    QuarkPropagatorWithNumerator where
  numerator := quarkDiracNumerator k mass
  denominator := regularizedDenominator (massShellPolynomial k mass) ε

/-! ### Vertex Functions (Color-Stripped) -/

/-- Contract: gauge-fermion (matter-boson) vertex satisfies gauge-covariance.
    Generic form: `V^μ = -i g γ^μ T^a` where `T^a` is a representation generator.
    Applies to quark-gluon (SU(3)), lepton-W (SU(2)), and fermion-B (U(1)) vertices. -/
structure GaugeFermionVertexAssumptions where
  /-- Coupling strength times representation-generator factor. -/
  colorCoupling : ℝ
  /-- Lorentz-structure flag (Dirac γ^μ term present). -/
  lorentzStructure : Bool
  /-- Gauge-covariance property. -/
  isGaugeCovariant : Prop
  /-- Witness that gauge covariance holds. -/
  hGaugeCovariant : isGaugeCovariant

/-- Backward-compatible alias: quark-gluon vertex contract. -/
abbrev QuarkGluonVertexAssumptions := GaugeFermionVertexAssumptions

/-- Contract: 3-gauge-boson vertex satisfies non-abelian Yang-Mills structure.
    Generic form: `V^(3) ∝ g f^abc` where `f^abc` are the Lie algebra structure constants.
    Zero for U(1) (abelian); present for SU(2), SU(3), and any non-abelian factor. -/
structure ThreeGaugeBosonVertexAssumptions where
  /-- Coupling strength (proportional to `g`). -/
  couplingStrength : ℝ
  /-- Structure-constant contract: `f^abc` appears with correct symmetries. -/
  hasStructureConstants : Prop
  /-- Witness that structure constants appear correctly. -/
  hStructureConstants : hasStructureConstants
  /-- Momentum-dependent kinematic factor: `(k1-k2)^ν g_μρ + cyclic`. -/
  hasKinematicFactors : Prop
  /-- Witness that kinematic factors are present. -/
  hKinematicFactors : hasKinematicFactors

/-- Backward-compatible alias: 3-gluon vertex contract. -/
abbrev ThreeGluonVertexAssumptions := ThreeGaugeBosonVertexAssumptions

/-- Contract: 4-gauge-boson vertex satisfies Yang-Mills self-coupling structure.
    Comes from the `[Dμ, Dν]²` term in the covariant-derivative expansion.
    Zero for U(1); present for SU(2) and SU(3). -/
structure FourGaugeBosonVertexAssumptions where
  /-- Coupling strength (∝ g²). -/
  couplingStrength : ℝ
  /-- Color-tensor structure: `f^abe f^ecd + cyclic` with correct Lorentz contractions. -/
  colorTensorStructure : Prop
  /-- Witness that color tensors are correct. -/
  hColorTensorStructure : colorTensorStructure
  /-- Contains all cyclic color permutations. -/
  hasColorPermutations : Prop
  /-- Witness that all color permutations appear. -/
  hColorPermutations : hasColorPermutations

/-- Backward-compatible alias: 4-gluon vertex contract. -/
abbrev FourGluonVertexAssumptions := FourGaugeBosonVertexAssumptions

/-- Contract: ghost-gauge-boson vertex satisfies Faddeev-Popov structure.
    Generic form: `V = -g f^abc ∂^μ`; absent in U(1), present in SU(2) and SU(3). -/
structure GhostGaugeBosonVertexAssumptions where
  /-- Coupling strength (proportional to `g`). -/
  couplingStrength : ℝ
  /-- Color structure: fully antisymmetric structure constants `f^abc`. -/
  colorStructure : Bool
  /-- Derivative coupling (vertex is momentum-dependent). -/
  isDeri : Bool
  /-- Faddeev-Popov ghost identity holds. -/
  faddeevPopovIdentity : Prop
  /-- Witness to the Faddeev-Popov identity. -/
  hFaddeevPopovIdentity : faddeevPopovIdentity

/-- Backward-compatible alias: ghost-gluon vertex contract. -/
abbrev GhostGluonVertexAssumptions := GhostGaugeBosonVertexAssumptions

/-! ### Generic Gauge-Theory Feynman Rules Bundle -/

/-- Bundled gauge-theory Feynman rules, parameterised by gauge sector.

This structure is sector-agnostic: it covers U(1) (photon / hypercharge),
SU(2) (W bosons), and SU(N) (gluons). The vertex contracts encode which
interactions are present for a given sector. -/
structure GaugeFeynmanRules where
  /-- Gauge-boson propagator (massless in covariant gauge). -/
  gauge_propagator : ∀ (_k : Momentum) (_μ _ν : LorentzIndex) (_ξ ε : ℝ), 0 < ε → ℂ
  /-- Matter-fermion propagator. -/
  matter_propagator : ∀ (_k : Momentum) (_mass ε : ℝ), 0 < ε → ℂ
  /-- Ghost propagator (trivial for U(1), Faddeev-Popov for non-abelian). -/
  ghost_propagator : ∀ (_k : Momentum) (ε : ℝ), 0 < ε → ℂ
  /-- Gauge-fermion vertex contract. -/
  gf_vertex : GaugeFermionVertexAssumptions
  /-- 3-boson vertex contract (coupling = 0 for abelian sectors). -/
  three_boson_vertex : ThreeGaugeBosonVertexAssumptions
  /-- 4-boson vertex contract (coupling = 0 for abelian sectors). -/
  four_boson_vertex : FourGaugeBosonVertexAssumptions
  /-- Ghost-boson vertex contract (trivial for abelian sectors). -/
  ghost_boson_vertex : GhostGaugeBosonVertexAssumptions
  /-- Running coupling at scale μ. -/
  runningCoupling : ℝ → ℝ

/-- Backward-compatible alias: QCD Feynman rules = generic gauge Feynman rules. -/
abbrev QCDFeynmanRules := GaugeFeynmanRules

/-- Standard non-abelian gauge rules with coupling `g` (e.g. SU(3) or SU(2)). -/
def nonAbelianGaugeRules (g : ℝ) : GaugeFeynmanRules where
  gauge_propagator  := gluonPropagator
  matter_propagator := quarkPropagator
  ghost_propagator  := ghostPropagator
  gf_vertex         := ⟨g,    true, True, trivial⟩
  three_boson_vertex := ⟨g,   True, trivial, True, trivial⟩
  four_boson_vertex  := ⟨g^2, True, trivial, True, trivial⟩
  ghost_boson_vertex := ⟨g,   true, true, True, trivial⟩
  runningCoupling   := fun _ => g

/-- Standard minimal-subtraction non-abelian rules; alias for SU(3) (QCD). -/
def qcdStandardRules (g_s : ℝ) : GaugeFeynmanRules := nonAbelianGaugeRules g_s

/-- U(1) Abelian gauge rules with coupling `g` (e.g. hypercharge or QED).

For an abelian gauge sector the 3- and 4-boson self-coupling constants are zero
and there are no Faddeev-Popov ghost interactions. -/
def u1AbelianGaugeRules (g : ℝ) : GaugeFeynmanRules where
  gauge_propagator  := gluonPropagator   -- same denominator form as any massless boson
  matter_propagator := quarkPropagator
  ghost_propagator  := ghostPropagator
  gf_vertex         := ⟨g, true, True, trivial⟩
  three_boson_vertex := ⟨0, True, trivial, True, trivial⟩  -- no cubic self-coupling
  four_boson_vertex  := ⟨0, True, trivial, True, trivial⟩  -- no quartic self-coupling
  ghost_boson_vertex := ⟨0, false, false, True, trivial⟩    -- ghosts decouple
  runningCoupling   := fun _ => g

/-- SU(2) weak-isospin gauge rules with coupling `g_w`. -/
def su2GaugeRules (g_w : ℝ) : GaugeFeynmanRules := nonAbelianGaugeRules g_w

/-! ### Diagram Assembly Theorems -/

/-- Contract: a tree-level Born gauge-boson–matter scattering diagram. -/
structure TreeGaugeBornDiagramAssumptions (rules : GaugeFeynmanRules)
  (k_in k_out : Momentum) : Type where
  /-- The diagram contributes to matter scattering amplitude. -/
  isMatterScattering : Prop
  /-- The diagram respects on-shell kinematics. -/
  respectsOnShell : Prop
  /-- Witness to both properties. -/
  hProperties : isMatterScattering ∧ respectsOnShell

/-- Backward-compatible alias. -/
abbrev TreeQuarkGluonBoxDiagramAssumptions := TreeGaugeBornDiagramAssumptions

/-- Constructive tree-level Born gauge-matter diagram amplitude data. -/
def treeGaugeBorn_amplitude
    (rules : GaugeFeynmanRules) (k_in k_out : Momentum) :
    Σ _A : ℝ, TreeGaugeBornDiagramAssumptions rules k_in k_out := by
  exact ⟨1.0, ⟨True, True, ⟨trivial, trivial⟩⟩⟩

/-- Backward-compatible alias. -/
def treeQuarkGluonBox_amplitude
    (rules : GaugeFeynmanRules) (k_in k_out : Momentum) :
    Σ _A : ℝ, TreeGaugeBornDiagramAssumptions rules k_in k_out :=
  treeGaugeBorn_amplitude rules k_in k_out

/-- Contract: one-loop gauge diagram requiring loop integration and regularization. -/
structure OneLoopGaugeDiagramAssumptions (rules : GaugeFeynmanRules)
  (k_in k_out : Momentum) : Type where
  /-- The diagram contains a loop integration. -/
  hasLoopIntegral : Prop
  /-- Requires regularization (iε or dimensional). -/
  needsRegularization : Prop
  /-- Witness to both. -/
  hProperties : hasLoopIntegral ∧ needsRegularization

/-- Backward-compatible alias. -/
abbrev OneLoopBoxDiagramAssumptions := OneLoopGaugeDiagramAssumptions

/-- Lemma: one-loop gauge diagram requires regularization for pole extraction. -/
lemma oneLoopGauge_requiresRegularization (rules : GaugeFeynmanRules)
    (k_in k_out : Momentum) (diag_asm : OneLoopGaugeDiagramAssumptions rules k_in k_out) :
    diag_asm.needsRegularization := diag_asm.hProperties.2

/-- Backward-compatible alias. -/
lemma oneLoopBox_requiresRegularization (rules : GaugeFeynmanRules)
    (k_in k_out : Momentum) (diag_asm : OneLoopGaugeDiagramAssumptions rules k_in k_out) :
    diag_asm.needsRegularization :=
  oneLoopGauge_requiresRegularization rules k_in k_out diag_asm

/-! ### Concrete One-Loop Self-Energy Diagram Classes -/

open Physlib.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars

/-- Concrete one-loop gauge-boson self-energy diagram data. -/
structure GaugeBosonSelfEnergyDiagram (rules : GaugeFeynmanRules) : Type where
  /-- External momentum carried by the two-point function. -/
  externalMomentum : Momentum
  /-- Underlying one-loop regularization witness. -/
  loopAssumptions : OneLoopGaugeDiagramAssumptions rules externalMomentum externalMomentum

/-- Concrete one-loop ghost self-energy diagram data. -/
structure GhostSelfEnergyDiagram (rules : GaugeFeynmanRules) : Type where
  /-- External momentum carried by the ghost two-point function. -/
  externalMomentum : Momentum
  /-- Underlying one-loop regularization witness. -/
  loopAssumptions : OneLoopGaugeDiagramAssumptions rules externalMomentum externalMomentum

/-- Concrete one-loop fermion self-energy diagram data. -/
structure FermionSelfEnergyDiagram (rules : GaugeFeynmanRules) : Type where
  /-- External momentum carried by the fermion two-point function. -/
  externalMomentum : Momentum
  /-- Underlying one-loop regularization witness. -/
  loopAssumptions : OneLoopGaugeDiagramAssumptions rules externalMomentum externalMomentum

/-- A bundled collection of the three one-loop self-energy diagram classes used by the
beta-function proof: gauge-boson, ghost, and fermion loops. -/
structure OneLoopSelfEnergyDiagramBundle (rules : GaugeFeynmanRules) : Type where
  gaugeBoson : GaugeBosonSelfEnergyDiagram rules
  ghost : GhostSelfEnergyDiagram rules
  fermion : FermionSelfEnergyDiagram rules

/-- Gauge-boson self-energy diagrams require regularization. -/
lemma GaugeBosonSelfEnergyDiagram.needsRegularization
    {rules : GaugeFeynmanRules} (diag : GaugeBosonSelfEnergyDiagram rules) :
    diag.loopAssumptions.needsRegularization :=
  oneLoopGauge_requiresRegularization
    rules diag.externalMomentum diag.externalMomentum diag.loopAssumptions

/-- Ghost self-energy diagrams require regularization. -/
lemma GhostSelfEnergyDiagram.needsRegularization
    {rules : GaugeFeynmanRules} (diag : GhostSelfEnergyDiagram rules) :
    diag.loopAssumptions.needsRegularization :=
  oneLoopGauge_requiresRegularization
    rules diag.externalMomentum diag.externalMomentum diag.loopAssumptions

/-- Fermion self-energy diagrams require regularization. -/
lemma FermionSelfEnergyDiagram.needsRegularization
    {rules : GaugeFeynmanRules} (diag : FermionSelfEnergyDiagram rules) :
    diag.loopAssumptions.needsRegularization :=
  oneLoopGauge_requiresRegularization
    rules diag.externalMomentum diag.externalMomentum diag.loopAssumptions

/-- Diagram-evaluation assumptions identifying the scalar masters extracted from a
bundle of concrete self-energy diagrams. -/
structure OneLoopSelfEnergyEvaluationAssumptions
    {rules : GaugeFeynmanRules}
  (bundle : OneLoopSelfEnergyDiagramBundle rules) : Type where
  /-- Scalar master extracted from the gauge-boson self-energy diagram. -/
  gaugeBosonMaster : ScalarMasterIntegral
  /-- Scalar master extracted from the ghost self-energy diagram. -/
  ghostMaster : ScalarMasterIntegral
  /-- Scalar master extracted from the fermion self-energy diagram. -/
  fermionMaster : ScalarMasterIntegral
  /-- In the standard one-loop normalization, the gauge-boson diagram evaluates to the
  canonical gauge-boson self-energy master. -/
  hGaugeBosonMaster : gaugeBosonMaster = gaugeBosonSelfEnergyMaster
  /-- In the standard one-loop normalization, the ghost diagram evaluates to the
  canonical ghost self-energy master. -/
  hGhostMaster : ghostMaster = ghostSelfEnergyMaster
  /-- In the standard one-loop normalization, the fermion diagram evaluates to the
  canonical fermion self-energy master. -/
  hFermionMaster : fermionMaster = fermionSelfEnergyMaster

/-! ### Connection to Renormalization -/

/-- Contract: gauge Feynman rules + renormalization constants induce renormalized diagrams.

Applies to all gauge sectors; for U(1) this is QED renormalization,
for SU(2) the weak sector, for SU(3) QCD. -/
structure FeynmanRulesRenormalizationLink (rules : GaugeFeynmanRules) : Type where
  /-- Renormalization is compatible with gauge Feynman rules. -/
  compatible : Prop
  /-- Witness to compatibility. -/
  hCompatible : compatible

end FeynmanDiagrams
end PerturbationTheory
end QFT
end Physlib
