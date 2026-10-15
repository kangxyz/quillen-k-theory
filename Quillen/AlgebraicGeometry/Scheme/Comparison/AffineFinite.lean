/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteType
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteType

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (affineFiniteSheaf_of_finiteLocallyFree finite_globalSections_of_finiteLocallyFree
  finite_globalSections_of_finitePresentation finite_globalSections_of_finiteType
  finite_globalSections_of_localGenerators finite_restrictPrincipal_of_overGenerators
  generatingSectionsOverToRestrict generatingSectionsOverToRestrict_isFiniteType)
end Quillen.SchemeSheaf

end
