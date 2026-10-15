/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Generators.OpenFreeFunctor

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (freeYonedaEquiv_naturality_source injective_sections_restrict_surjective openFreeFunctor
  openFreeFunctor_map_mono openFreeHomEquiv_naturality_open)
end Quillen.SchemeSheaf

end
