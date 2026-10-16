/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Pullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlatPullback
public import Aglib.AlgebraicGeometry.Modules.Complex.Pullback

/-!
# Geometric bounded-flat pullback comparisons

The original identity/composition comparisons lift through faithful full-subcategory inclusion. Every strict perfect complex is bounded flat.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- The natural isomorphism identifying pullback along the identity of `X` with the identity on
bounded-flat perfect complexes. -/
def boundedFlatPerfectPullbackIdIso (X : Scheme.{u}) :
    boundedFlatPerfectPullback (𝟙 X) ≅ 𝟭 (BoundedFlatPerfect X) :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfect X).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfect X).ι (Complex.pullbackIdIso X))

/-- The natural isomorphism identifying pullback along `f ≫ g` with pullback first along `g` and
then along `f` on bounded-flat perfect complexes. -/
def boundedFlatPerfectPullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedFlatPerfectPullback (f ≫ g) ≅
      boundedFlatPerfectPullback g ⋙ boundedFlatPerfectPullback f :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfect X).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfect Z).ι (Complex.pullbackCompIso f g))

theorem strictPerfect_boundedFlatPerfect {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    (hK : strictPerfect X K) : boundedFlatPerfect X K :=
  ⟨locallyPerfect_of_strictPerfect hK, strictPerfect_boundedAbove_stalkwiseFlat hK⟩

end Quillen.PerfectComplexes

end

end
