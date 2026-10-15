/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.MappingCone.Acyclicity

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.HomologicalAlgebra
export CochainComplex
  (mappingCone_acyclic_of_quasiIso)
end Quillen.HomologicalAlgebra

end
