/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.Scattering.DIS.PVES.Electroweak.Parameters
public import Physlib.QFT.Scattering.DIS.PVES.Electroweak.NeutralCurrent
public import Physlib.QFT.Scattering.DIS.PVES.Interference.Basic
public import Physlib.QFT.Scattering.DIS.PVES.Processes.EE
public import Physlib.QFT.Scattering.DIS.PVES.Processes.EP
public import Physlib.QFT.Scattering.DIS.PVES.Examples.Basic
public import Physlib.QFT.Scattering.DIS.PVES.Examples.Moller
/-!

# DIS PVES Basic API

This module exports base PVES interfaces:
- electroweak parameter and effective coupling contracts,
- neutral-current mediator and gamma/Z/interference decomposition contracts.

## Scope of the present formalization

Two limitations are load-bearing for anyone building on these modules, and are recorded here
rather than left to be rediscovered.

**The asymmetry chain carries no electroweak content.** `Interference`, both `Processes` and
both `Examples` are stated over `Electroweak.NeutralCurrentDecomposition`, an abstract triple
of functions `ℝ → ℝ → ℝ`. The bridge theorems relating the beam-helicity asymmetry to the
interference-over-total ratio are algebraic consequences of that decomposition; `sin^2(theta_W)`
appears nowhere in them. `Electroweak.Parameters`, `Electroweak.NeutralCurrentCouplings`,
`Electroweak.EffectiveModel` and `Electroweak.NeutralCurrentFeynmanRules` are declared but never
instantiated anywhere in the library. Connecting the two halves -- deriving a decomposition from
the parameters, so that an asymmetry statement mentions the weak mixing angle -- is the open
work in this subtree.

**`Electroweak.Parameters` is tree-level and on-shell.** `weakMassRatioConsistency` is
equivalent to `rho = 1` (`Electroweak.rhoParameter_eq_one_of_weakMassRatio`), and the structure
carries no renormalization-scheme or scale label, so two parameter sets differing only by scheme
are indistinguishable. It therefore cannot represent the running MS-bar angle
`sin^2(theta-hat_W)(mu)` used in low-`Q^2` parity-violating deep-inelastic analyses, nor the
`rho_PV` and `kappa` factors through which electroweak radiative corrections act on the
effective couplings.

-/

@[expose] public section

namespace Physlib
namespace QFT
namespace Scattering
namespace DIS
namespace PVES

/-- Re-export alias for the electroweak effective model contract. -/
abbrev EffectiveElectroweakModel := Electroweak.EffectiveModel

/-- Re-export alias for neutral-current decomposition contracts. -/
abbrev NeutralCurrentDecomposition := Electroweak.NeutralCurrentDecomposition

end PVES
end DIS
end Scattering
end QFT
end Physlib
