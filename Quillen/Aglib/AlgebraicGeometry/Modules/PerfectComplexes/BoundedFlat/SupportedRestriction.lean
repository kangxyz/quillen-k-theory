/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Pairs
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Restriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PairPullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Pullback

/-!
# Supported restriction and bounded-flat pullback

The literal original supported inclusions compare restriction with the actual inverse-image
pair pullback.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Restriction and pullback agree through the original supported inclusions. -/
def boundedFlatPerfectSupportedOriginalRestrictionIso :
    boundedFlatPerfectSupportedInclusion T.ι ⋙ perfectSupportedRestrict j T ≅
      boundedFlatPerfectSupportedPullback (supportRestrictionPair j T) ⋙
        boundedFlatPerfectSupportedInclusion (j ⁻¹ᵁ T).ι :=
  Functor.fullyFaithfulCancelRight (perfectSupported (j ⁻¹ᵁ T).ι).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported T.ι).ι
      (restrictIsoPullbackComplex j))

end Quillen.PerfectComplexes

end

end
