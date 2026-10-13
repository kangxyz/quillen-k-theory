/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.FlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.PullbackFunctor
public import Quillen.AlgebraicGeometry.Scheme.FlatPullback

/-!
# Contravariant locally-perfect K-theory for flat morphisms

This functor uses the actual geometric flat pullback on the original locally
perfect Waldhausen category. The original strict-to-local and public
vector-bundle-to-local maps are natural transformations. This does not assert
that either comparison is an equivalence on arbitrary schemes.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace Quillen.PerfectComplexes

/-- Locally-perfect K-theory with its actual flat pullback maps. -/
def PerfectKFlatFunctor (n : ℕ) : Quillen.Scheme.FlatSchemes.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (PerfectK X.unop.obj n)
  map f := GrpCat.ofHom (perfectKFlatPullback f.unop.hom n)
  map_id X := by
    apply GrpCat.hom_ext
    exact perfectKFlatPullback_id X.unop.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact perfectKFlatPullback_comp g.unop.hom f.unop.hom n

@[simp]
theorem PerfectKFlatFunctor_map {X Y : Quillen.Scheme.FlatSchemes.{u}ᵒᵖ} (f : X ⟶ Y)
    (n : ℕ) : ((PerfectKFlatFunctor n).map f).hom = perfectKFlatPullback f.unop.hom n := rfl

/-- The original strict-to-local comparison is natural on all flat scheme maps. -/
def strictToPerfectFlatNatTrans (n : ℕ) :
    (wideSubcategoryInclusion (@Flat : MorphismProperty Scheme.{u})).op ⋙ StrictKFunctor n ⟶
      PerfectKFlatFunctor n where
  app X := GrpCat.ofHom (strictToPerfectKMap X.unop.obj n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (strictToPerfectKMap_flatPullback f.unop.hom n).symm

@[simp]
theorem strictToPerfectFlatNatTrans_app (n : ℕ) (X : Quillen.Scheme.FlatSchemes.{u}ᵒᵖ) :
    ((strictToPerfectFlatNatTrans n).app X).hom = strictToPerfectKMap X.unop.obj n := rfl

/-- The original public vector-bundle-to-local comparison is natural for flat maps. -/
def vectorBundleToPerfectFlatNatTrans (n : ℕ) :
    (wideSubcategoryInclusion (@Flat : MorphismProperty Scheme.{u})).op ⋙ Quillen.Scheme.KFunctor n
      ⟶
      PerfectKFlatFunctor n where
  app X := GrpCat.ofHom (vectorBundleToPerfectKMap X.unop.obj n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (vectorBundleToPerfectKMap_flatPullback f.unop.hom n).symm

@[simp]
theorem vectorBundleToPerfectFlatNatTrans_app (n : ℕ) (X : Quillen.Scheme.FlatSchemes.{u}ᵒᵖ) :
    ((vectorBundleToPerfectFlatNatTrans n).app X).hom = vectorBundleToPerfectKMap X.unop.obj n :=
      rfl

end Quillen.PerfectComplexes
