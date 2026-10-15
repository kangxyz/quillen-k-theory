/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (finiteLocallyFree_closedUnderFiniteProducts finiteLocallyFree_extensionClosed
  finiteLocallyFree_of_shortExact vectorBundleExactInclusion vectorBundleExactStructure
  vectorBundleExactStructure_conflation)
end Quillen.SchemeSheaf

end
