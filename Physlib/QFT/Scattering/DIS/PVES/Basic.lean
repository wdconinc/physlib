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
