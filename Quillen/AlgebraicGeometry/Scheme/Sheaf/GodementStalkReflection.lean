/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (godement_isZero_of_moduleStalks godement_quasiIso_of_moduleStalks)
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
alias godement_isIso_of_moduleStalks := AlgebraicGeometry.Scheme.Modules.isIso_of_moduleStalk
end Quillen.SchemeSheaf

end
