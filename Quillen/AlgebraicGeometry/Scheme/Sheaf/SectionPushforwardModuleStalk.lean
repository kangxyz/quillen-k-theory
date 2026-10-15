/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.SectionStalk

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (sectionPushforwardModuleStalkIso sectionPushforwardModuleStalkIso_germ sectionStalkRingMap
  sectionStalkRingMap_hom_comp sectionStalkRingMap_retraction section_stalk_point)
end Quillen.SchemeSheaf

end
