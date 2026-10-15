/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.LocalRing.ParameterQuotient
public import Aglib.RingTheory.RegularLocalRing.ParameterQuotient

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.RegularLocal
export IsLocalRing
  (exists_generators_containing_parameter spanFinrank_maximalIdeal_quotient_parameter_le)
export IsRegularLocalRing
  (regularLocal_quotient_parameter)
end Quillen.RegularLocal

end
