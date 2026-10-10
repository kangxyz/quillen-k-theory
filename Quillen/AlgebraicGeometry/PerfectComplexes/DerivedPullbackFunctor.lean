/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPullback
public import Quillen.AlgebraicGeometry.Scheme.QuasiCompact

/-!
# Original perfect K-theory on quasi-compact schemes

The original groups form a contravariant functor under arbitrary scheme maps.
Its natural isomorphism from the bounded-flat model has the unchanged literal
inclusion as forward component. The original strict-perfect and vector-bundle
comparisons are natural transformations; no equivalence of those comparisons
is asserted here.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes

/-- Original perfect K-theory as a contravariant functor on qc schemes. -/
def PerfectKFunctor (n : ℕ) : Quillen.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (PerfectK X.unop.obj n)
  map f := GrpCat.ofHom (perfectKPullback f.unop.hom n)
  map_id X := by apply GrpCat.hom_ext; exact perfectKPullback_id X.unop.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact perfectKPullback_comp g.unop.hom f.unop.hom n

@[simp] theorem PerfectKFunctor_map {X Y : Quillen.Scheme.QuasiCompactSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((PerfectKFunctor n).map f).hom = perfectKPullback f.unop.hom n := rfl

/-- The actual bounded-flat inclusion comparison is a natural isomorphism. -/
def boundedFlatPerfectToPerfectNatIso (n : ℕ) :
    Quillen.Scheme.quasiCompactSchemesInclusion.op ⋙ BoundedFlatPerfectKFunctor.{u} n ≅
      PerfectKFunctor n :=
  NatIso.ofComponents (fun X => (boundedFlatPerfectKEquiv X.unop.obj n).toGrpIso)
    (fun f => by
      apply GrpCat.hom_ext
      exact (perfectKPullback_comp_boundedFlat f.unop.hom n).symm)

@[simp] theorem boundedFlatPerfectToPerfectNatIso_hom_app (n : ℕ)
    (X : Quillen.Scheme.QuasiCompactSchemes.{u}ᵒᵖ) :
    ((boundedFlatPerfectToPerfectNatIso n).hom.app X).hom =
      boundedFlatPerfectToPerfectKMap X.unop.obj n := rfl

@[simp] theorem boundedFlatPerfectToPerfectNatIso_inv_app (n : ℕ)
    (X : Quillen.Scheme.QuasiCompactSchemes.{u}ᵒᵖ) :
    ((boundedFlatPerfectToPerfectNatIso n).inv.app X).hom =
      (boundedFlatPerfectKEquiv X.unop.obj n).symm.toMonoidHom := rfl

/-- The original strict-to-local comparison is natural under arbitrary qc scheme maps. -/
def strictToPerfectNatTrans (n : ℕ) :
    Quillen.Scheme.quasiCompactSchemesInclusion.op ⋙ StrictKFunctor.{u} n ⟶
      PerfectKFunctor n where
  app X := GrpCat.ofHom (strictToPerfectKMap X.unop.obj n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (strictToPerfectKMap_pullback f.unop.hom n).symm

@[simp] theorem strictToPerfectNatTrans_app (n : ℕ)
    (X : Quillen.Scheme.QuasiCompactSchemes.{u}ᵒᵖ) :
    ((strictToPerfectNatTrans n).app X).hom = strictToPerfectKMap X.unop.obj n := rfl

/-- The original vector-bundle-to-local comparison is natural under arbitrary qc scheme maps. -/
def vectorBundleToPerfectNatTrans (n : ℕ) :
    Quillen.Scheme.quasiCompactSchemesInclusion.op ⋙ Quillen.Scheme.KFunctor.{u} n ⟶
      PerfectKFunctor n where
  app X := GrpCat.ofHom (vectorBundleToPerfectKMap X.unop.obj n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (vectorBundleToPerfectKMap_pullback f.unop.hom n).symm

@[simp] theorem vectorBundleToPerfectNatTrans_app (n : ℕ)
    (X : Quillen.Scheme.QuasiCompactSchemes.{u}ᵒᵖ) :
    ((vectorBundleToPerfectNatTrans n).app X).hom = vectorBundleToPerfectKMap X.unop.obj n := rfl

end Quillen.PerfectComplexes
