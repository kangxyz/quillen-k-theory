/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.BasisExactness

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SheafCohomology
export TopCat.Sheaf
  (acyclic_of_sections_on_basis exactAt_of_sections_on_basis exact_of_sections_on_basis
  quasiIso_of_sections_on_basis)
end Quillen.SheafCohomology

end
