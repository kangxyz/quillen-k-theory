/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.LocalRing.ParameterAvoidance

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.RegularLocal
export IsLocalRing
  (exists_parameter_avoiding_minimalPrimes isDomain_of_prime_parameter)
end Quillen.RegularLocal

end
