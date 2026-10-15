/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Locality.Isomorphisms

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules
  (moduleSheaf_isIso_iff_stalks moduleSheaf_isIso_restrict_of_openCover
  moduleSheaf_isIso_restrict_of_stalks)
end Quillen.CoherentScheme

end
