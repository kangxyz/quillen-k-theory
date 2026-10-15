/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.InjectiveComplex

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf.TwoOpen
export AlgebraicGeometry.Scheme.Modules.TwoOpen
  (app_res augmentation augmentationNat augmentation_injective cochainSequence
  cochainSequence_shortExact difference differenceNat difference_apply difference_augmentation
  difference_surjective injectiveResolution_cochainSequence_shortExact pairFunctor
  pairFunctor_additive res res_res sectionSequence sectionSequence_exact
  sectionSequence_shortExact sectionsFunctor sectionsFunctor_additive)
end Quillen.SchemeSheaf.TwoOpen

end
