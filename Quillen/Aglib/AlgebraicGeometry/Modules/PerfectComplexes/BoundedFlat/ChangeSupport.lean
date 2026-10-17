/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.ChangeOpenPairs
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Antitone
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PairPullback

/-!
# Identity-base bounded-flat support comparison

The original geometric pullback along the identity-base support square is the same actual
supported inclusion.
-/
@[expose] public section



open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {X : Scheme.{u}} {S T : X.Opens} (h : S ≤ T)

/-- Actual bounded-flat pullback on the identity base is the literal inclusion. -/
def boundedFlatPerfectSupportedChangeOpenIso :
    boundedFlatPerfectSupportedInclusion T.ι ⋙ ObjectProperty.ιOfLE (perfectSupported_antitone h) ≅
      boundedFlatPerfectSupportedPullback (supportChangeOpenPair h) ⋙
        boundedFlatPerfectSupportedInclusion S.ι :=
  Functor.fullyFaithfulCancelRight (perfectSupported S.ι).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported T.ι).ι
      (Scheme.Modules.Complex.pullbackIdIso X).symm)

end Quillen.PerfectComplexes

end

end
