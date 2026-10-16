/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PairPullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PullbackIsomorphisms
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Pullback
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction

/-!
# Original bounded-flat restriction comparisons

The actual original inclusion, open restriction and geometric pair pullback retain their
canonical natural isomorphisms.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The natural isomorphism comparing restriction of the inclusion into perfect complexes with
bounded-flat pullback along the open immersion `j`. -/
def boundedFlatPerfectOriginalRestrictionIso :
    boundedFlatPerfectInclusion X ⋙ perfectRestrict j ≅
      boundedFlatPerfectPullback j ⋙ boundedFlatPerfectInclusion U :=
  Functor.fullyFaithfulCancelRight (locallyPerfect U).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfect X).ι (restrictIsoPullbackComplex j))

variable {A B : AlgebraicGeometry.Scheme.OpenPairs.{u}}

/-- The natural isomorphism comparing the two composites of bounded-flat pullback around the
commutative open-pair square `f : A ⟶ B`. -/
def boundedFlatPerfectOpenPairIso (f : A ⟶ B) :
    boundedFlatPerfectPullback f.hom.right ⋙ boundedFlatPerfectPullback A.obj.hom ≅
      boundedFlatPerfectPullback B.obj.hom ⋙ boundedFlatPerfectPullback f.hom.left :=
  (boundedFlatPerfectPullbackCompIso A.obj.hom f.hom.right).symm ≪≫
    eqToIso (congrArg boundedFlatPerfectPullback (Arrow.w f.hom).symm) ≪≫
    boundedFlatPerfectPullbackCompIso f.hom.left B.obj.hom

end Quillen.PerfectComplexes

end

end
