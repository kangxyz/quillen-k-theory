/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (flatExactPullback moduleSkyscraperPushforwardIso moduleSkyscraperPushforwardObjIso
  mono_pullback_of_flat_all pullbackModuleStalkIso pullback_preservesFiniteLimits_of_flat
  pullback_preservesMonomorphisms_of_flat shortExact_pullback_of_flat_all)
end Quillen.SchemeSheaf

end
