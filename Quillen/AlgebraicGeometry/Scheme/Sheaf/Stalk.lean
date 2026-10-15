/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (exists_germ_smul_representatives germ_moduleSkyscraperCocone_desc
  instModulePointPresheafObjRingSheaf instModulePointPresheafObjStructureSheaf
  instModulePointSection instModuleSchemeModuleStalk moduleSkyscraper moduleSkyscraperCocone
  moduleSkyscraperFromStalk moduleSkyscraperObj moduleStalk moduleStalkExactFunctor
  moduleStalkForgetIso moduleStalkMap moduleStalkSkyscraperAdjunction
  moduleStalkSkyscraperHomEquiv moduleStalkToSkyscraper moduleStalkToSkyscraper_naturality_left
  moduleStalk_additive moduleStalk_isLeftAdjoint moduleStalk_preservesFiniteLimits
  mono_of_moduleStalk pointPresheaf pointPresheaf_isSheaf pointPresheaf_map_smul
  stalkFunctor_additive stalkFunctor_preservesFiniteLimits)
end Quillen.SchemeSheaf

end
