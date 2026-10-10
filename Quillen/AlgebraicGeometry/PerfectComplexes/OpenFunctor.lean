/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ComparisonNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.GilletWaldhausen
public import Quillen.AlgebraicGeometry.Scheme.OpenImmersionFunctor

/-!
# Group-valued perfect K-theory functors and original comparison transformations

The category has schemes as objects and only open immersions as arrows. All
functor maps and transformation components are the original geometric K-maps.
The vector-bundle/strict-perfect comparison is a natural isomorphism; the
strict/locally-perfect comparison is a natural transformation only.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Globally strict-perfect K-theory with actual open restriction. -/
def StrictKOpenFunctor (n : ℕ) : Scheme.OpenImmersionSchemes.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (StrictK X.unop.obj n)
  map f := GrpCat.ofHom (strictKRestrict f.unop.hom n)
  map_id X := by
    apply GrpCat.hom_ext
    exact strictKRestrict_id X.unop.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact strictKRestrict_comp g.unop.hom f.unop.hom n

/-- Locally perfect K-theory with actual open restriction. -/
def PerfectKOpenFunctor (n : ℕ) : Scheme.OpenImmersionSchemes.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (PerfectK X.unop.obj n)
  map f := GrpCat.ofHom (perfectKRestrict f.unop.hom n)
  map_id X := by
    apply GrpCat.hom_ext
    exact perfectKRestrict_id X.unop.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact perfectKRestrict_comp g.unop.hom f.unop.hom n

@[simp] theorem StrictKOpenFunctor_map {X Y : Scheme.OpenImmersionSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((StrictKOpenFunctor n).map f).hom = strictKRestrict f.unop.hom n := rfl

@[simp] theorem PerfectKOpenFunctor_map {X Y : Scheme.OpenImmersionSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((PerfectKOpenFunctor n).map f).hom = perfectKRestrict f.unop.hom n := rfl

/-- The original strict-to-local inclusion as a natural transformation. -/
def strictToPerfectOpenNatTrans (n : ℕ) : StrictKOpenFunctor.{u} n ⟶ PerfectKOpenFunctor n where
  app X := GrpCat.ofHom (strictToPerfectKMap X.unop.obj n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (strictToPerfectKMap_restrict f.unop.hom n).symm

/-- The original public vector-bundle comparison to locally perfect K-theory. -/
def vectorBundleToPerfectOpenNatTrans (n : ℕ) :
    Scheme.KOpenFunctor.{u} n ⟶ PerfectKOpenFunctor n where
  app X := GrpCat.ofHom (vectorBundleToPerfectKMap X.unop.obj n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (vectorBundleToPerfectKMap_restrict f.unop.hom n).symm

/-- The all-scheme vector-bundle/strict-perfect equivalence is natural. -/
def vectorBundleToStrictOpenNatIso (n : ℕ) :
    Scheme.KOpenFunctor.{u} n ≅ StrictKOpenFunctor n :=
  NatIso.ofComponents
    (fun X ↦ (vectorBundleToStrictKEquiv X.unop.obj n).toGrpIso)
    (fun f ↦ by
      apply GrpCat.hom_ext
      exact (vectorBundleToStrictKMap_restrict f.unop.hom n).symm)

@[simp] theorem strictToPerfectOpenNatTrans_app (n : ℕ)
    (X : Scheme.OpenImmersionSchemes.{u}ᵒᵖ) :
    ((strictToPerfectOpenNatTrans n).app X).hom = strictToPerfectKMap X.unop.obj n := rfl

@[simp] theorem vectorBundleToPerfectOpenNatTrans_app (n : ℕ)
    (X : Scheme.OpenImmersionSchemes.{u}ᵒᵖ) :
    ((vectorBundleToPerfectOpenNatTrans n).app X).hom =
      vectorBundleToPerfectKMap X.unop.obj n := rfl

@[simp] theorem vectorBundleToStrictOpenNatIso_hom_app (n : ℕ)
    (X : Scheme.OpenImmersionSchemes.{u}ᵒᵖ) :
    ((vectorBundleToStrictOpenNatIso n).hom.app X).hom =
      vectorBundleToStrictKMap X.unop.obj n := rfl

@[simp] theorem vectorBundleToStrictOpenNatIso_inv_app (n : ℕ)
    (X : Scheme.OpenImmersionSchemes.{u}ᵒᵖ) :
    ((vectorBundleToStrictOpenNatIso n).inv.app X).hom =
      (vectorBundleToStrictKEquiv X.unop.obj n).symm.toMonoidHom := rfl

/-- The bundled natural comparison triangle has the original components. -/
theorem vectorBundleToStrictOpenNatIso_comp (n : ℕ) :
    (vectorBundleToStrictOpenNatIso.{u} n).hom ≫ strictToPerfectOpenNatTrans n =
      vectorBundleToPerfectOpenNatTrans n := by
  ext X
  rfl

end Quillen.PerfectComplexes
