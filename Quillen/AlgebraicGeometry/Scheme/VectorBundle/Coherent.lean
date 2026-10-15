/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (coherent_of_finiteLocallyFree finiteLocallyFree_le_coherent vectorBundleToCoherent
  vectorBundleToCoherentExact vectorBundleToCoherentRestrictIso vectorBundleToCoherent_additive
  vectorBundleToCoherent_comp_inclusion vectorBundleToCoherent_faithful
  vectorBundleToCoherent_full vectorBundleToCoherent_restrict
  vectorBundleToCoherent_shortExact_iff)
end Quillen.SchemeSheaf

end
