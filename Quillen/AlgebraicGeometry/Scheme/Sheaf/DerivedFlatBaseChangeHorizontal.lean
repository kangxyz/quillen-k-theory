/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatPullbackComposition
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.CartesianBaseChangeHorizontal
/-! # Horizontal pasting of the original derived flat base-change maps

For two horizontally adjacent cartesian squares with flat bottom legs, the original derived
mate of the pasted square equals the composite of the original two derived mates, transported
through the geometric flat-pullback comparisons. The proof retains the ordinary mate and both
installed composite units and applies the actual right-derived universal property.
-/

@[expose] public section
open Quillen
open Quillen.SchemeSheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
/-- The original standard ambient categories. -/
local instance horizontalStandard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {W' W U V' V X : Scheme.{u}}
  (c : W' ⟶ W) (d : W' ⟶ V') (k : V' ⟶ V)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d b k) (h : IsPullback a b f j) [Flat k] [Flat j]
/-- The horizontal composite uses the original derived mates and geometric pullback comparisons. -/
def derivedFlatBaseChangeHorizontalComposite :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    derivedPushforwardPlus f ⋙ derivedFlatPullbackPlus (k ≫ j) ⟶
      derivedFlatPullbackPlus (c ≫ a) ⋙ derivedPushforwardPlus d := by
  letI := flat_cartesian_baseChange a b f j h
  letI := flat_cartesian_baseChange c d b k hs
  exact
    (Functor.isoWhiskerLeft (derivedPushforwardPlus f)
      (derivedFlatPullbackPlusCompIso k j).symm).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedFlatBaseChangeMap a b f j h) (derivedFlatPullbackPlus k) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (derivedFlatPullbackPlus a) (derivedFlatBaseChangeMap c d b k hs) ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (derivedFlatPullbackPlusCompIso c a)
      (derivedPushforwardPlus d)).hom
/-- The component retains the two literal derived mates and both composition maps. -/
theorem derivedFlatBaseChangeHorizontalComposite_app (K : DerivedCategory.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    (derivedFlatBaseChangeHorizontalComposite c d k a b f j hs h).app K =
      (derivedFlatPullbackPlusCompIso k j).inv.app ((derivedPushforwardPlus f).obj K) ≫
      (derivedFlatPullbackPlus k).map ((derivedFlatBaseChangeMap a b f j h).app K) ≫
      (derivedFlatBaseChangeMap c d b k hs).app ((derivedFlatPullbackPlus a).obj K) ≫
      (derivedPushforwardPlus d).map ((derivedFlatPullbackPlusCompIso c a).hom.app K) := by
  simp [derivedFlatBaseChangeHorizontalComposite]

omit [Flat k] [Flat j] in
/-- The horizontal mate equation holds in the actual componentwise bounded-below complexes. -/
theorem cartesianBaseChangeMap_paste_horiz_complex (K : CochainComplex.Plus U.Modules) :
    (NatIso.mapCochainComplexPlus (Scheme.Modules.pullbackComp k j)).inv.app
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj K) ≫
      (Scheme.Modules.pullback k).mapCochainComplexPlus.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K) ≫
      (NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap c d b k hs)).app
        ((Scheme.Modules.pullback a).mapCochainComplexPlus.obj K) ≫
      (Scheme.Modules.pushforward d).mapCochainComplexPlus.map
        ((NatIso.mapCochainComplexPlus (Scheme.Modules.pullbackComp c a)).hom.app K) =
    (NatTrans.mapCochainComplexPlus
      (cartesianBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h))).app K := by
  apply ObjectProperty.hom_ext
  ext n : 1
  change (Scheme.Modules.pullbackComp k j).inv.app _ ≫
      (Scheme.Modules.pullback k).map ((cartesianBaseChangeMap a b f j h).app (K.obj.X n)) ≫
      (cartesianBaseChangeMap c d b k hs).app ((Scheme.Modules.pullback a).obj (K.obj.X n)) ≫
      (Scheme.Modules.pushforward d).map ((Scheme.Modules.pullbackComp c a).hom.app (K.obj.X n)) = _
  rw [← cartesianBaseChangeMap_paste_horiz c d k a b f j hs h (K.obj.X n)]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

/-- Source comparison transports the original composite units. -/
private theorem derivedFlatBaseChangeHorizontal_source_unit (K : CochainComplex.Plus U.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.pullback (k ≫ j))).app K ≫
      (derivedFlatPullbackPlusCompIso k j).inv.app
        ((derivedPushforwardPlus f).obj (DerivedCategory.Plus.Q.obj K)) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (Scheme.Modules.pullbackComp k j)).inv.app
          ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj K)) ≫
      (Scheme.Modules.pullback k).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pullback j).mapCochainComplexPlus.obj
          ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj K)) ≫
      (derivedFlatPullbackPlus k).map
        ((Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
          (Scheme.Modules.pullback j)).app K) := by
  rw [Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc]
  erw [(derivedFlatPullbackPlusCompIso k j).inv.naturality]
  rw [← Category.assoc, derivedFlatPullbackPlusCompIso_inv_unit]
  simp only [Functor.rightDerivedFunctorPlusCompUnit_app, Functor.comp_map,
    Category.assoc, CategoryTheory.Functor.map_comp]
  rfl
/-- The two original mate unit equations compose before the final pullback comparison. -/
private theorem derivedFlatBaseChangeHorizontal_middle_unit (K : CochainComplex.Plus U.Modules) :
    let := flat_cartesian_baseChange a b f j h
    let := flat_cartesian_baseChange c d b k hs
    (Scheme.Modules.pullback k).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pullback j).mapCochainComplexPlus.obj
          ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj K)) ≫
      (derivedFlatPullbackPlus k).map
        ((Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
          (Scheme.Modules.pullback j)).app K) ≫
      (derivedFlatPullbackPlus k).map
        ((derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj K)) ≫
      (derivedFlatBaseChangeMap c d b k hs).app
        ((derivedFlatPullbackPlus a).obj (DerivedCategory.Plus.Q.obj K)) =
    DerivedCategory.Plus.Q.map
        ((Scheme.Modules.pullback k).mapCochainComplexPlus.map
          ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K)) ≫
      DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap c d b k hs)).app
          ((Scheme.Modules.pullback a).mapCochainComplexPlus.obj K)) ≫
      (Scheme.Modules.pushforward d).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pullback c).mapCochainComplexPlus.obj
          ((Scheme.Modules.pullback a).mapCochainComplexPlus.obj K)) ≫
      (derivedPushforwardPlus d).map
        ((Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback a)
          (Scheme.Modules.pullback c)).app K) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b k hs
  dsimp only
  have hm := congrArg ((derivedFlatPullbackPlus k).map)
    (derivedFlatBaseChangeMap_unit a b f j h K)
  simp only [CategoryTheory.Functor.map_comp] at hm
  erw [← Category.assoc
    ((derivedFlatPullbackPlus k).map
      ((Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.pullback j)).app K))
    ((derivedFlatPullbackPlus k).map
      ((derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj K)))]
  erw [hm]
  erw [Category.assoc, ← Category.assoc
    ((Scheme.Modules.pullback k).rightDerivedFunctorPlusUnit.app _)]
  erw [← (Scheme.Modules.pullback k).rightDerivedFunctorPlusUnit.naturality]
  simp only [Functor.comp_map, Category.assoc]
  erw [Functor.rightDerivedFunctorPlusCompUnit_app]
  erw [CategoryTheory.Functor.map_comp, Category.assoc,
    (derivedFlatBaseChangeMap c d b k hs).naturality]
  simp only [Functor.comp_map]
  have hb := derivedFlatBaseChangeMap_unit c d b k hs
    ((Scheme.Modules.pullback a).mapCochainComplexPlus.obj K)
  rw [Functor.rightDerivedFunctorPlusCompUnit_app] at hb
  have hb' := congrArg (fun z => z ≫ (derivedPushforwardPlus d).map
    ((derivedFlatPullbackPlus c).map
      ((Scheme.Modules.pullback a).rightDerivedFunctorPlusUnit.app K))) hb
  simp only [Category.assoc] at hb'
  erw [hb']
  simp only [Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc,
    CategoryTheory.Functor.map_comp]
  rfl

/-- Target comparison transports the original composite units. -/
private theorem derivedFlatBaseChangeHorizontal_target_unit (K : CochainComplex.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    (Scheme.Modules.pushforward d).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pullback c).mapCochainComplexPlus.obj
          ((Scheme.Modules.pullback a).mapCochainComplexPlus.obj K)) ≫
      (derivedPushforwardPlus d).map
        ((Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback a)
          (Scheme.Modules.pullback c)).app K) ≫
      (derivedPushforwardPlus d).map
        ((derivedFlatPullbackPlusCompIso c a).hom.app (DerivedCategory.Plus.Q.obj K)) =
    DerivedCategory.Plus.Q.map
        ((Scheme.Modules.pushforward d).mapCochainComplexPlus.map
          ((NatIso.mapCochainComplexPlus (Scheme.Modules.pullbackComp c a)).hom.app K)) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback (c ≫ a))
        (Scheme.Modules.pushforward d)).app K := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b k hs
  have hm := congrArg ((derivedPushforwardPlus d).map)
    (derivedFlatPullbackPlusCompIso_unit c a K)
  simp only [CategoryTheory.Functor.map_comp] at hm
  erw [hm]
  erw [← Category.assoc
    ((Scheme.Modules.pushforward d).rightDerivedFunctorPlusUnit.app _)]
  erw [← (Scheme.Modules.pushforward d).rightDerivedFunctorPlusUnit.naturality]
  simp only [Functor.comp_map, Category.assoc, Functor.rightDerivedFunctorPlusCompUnit_app]
  rfl

/-- The horizontal composite retains the exact original mate and composite unit square. -/
theorem derivedFlatBaseChangeHorizontalComposite_unit (K : CochainComplex.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.pullback (k ≫ j))).app K ≫
      (derivedFlatBaseChangeHorizontalComposite c d k a b f j hs h).app
        (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus
          (cartesianBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h))).app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback (c ≫ a))
        (Scheme.Modules.pushforward d)).app K := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b k hs
  erw [derivedFlatBaseChangeHorizontalComposite_app]
  have hsource := congrArg (fun z => z ≫
    (derivedFlatPullbackPlus k).map
      ((derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj K)) ≫
    (derivedFlatBaseChangeMap c d b k hs).app
      ((derivedFlatPullbackPlus a).obj (DerivedCategory.Plus.Q.obj K)) ≫
    (derivedPushforwardPlus d).map
      ((derivedFlatPullbackPlusCompIso c a).hom.app (DerivedCategory.Plus.Q.obj K)))
    (derivedFlatBaseChangeHorizontal_source_unit k f j K)
  simp only [Category.assoc] at hsource
  erw [hsource]
  have hmiddle := congrArg (fun z => z ≫ (derivedPushforwardPlus d).map
    ((derivedFlatPullbackPlusCompIso c a).hom.app (DerivedCategory.Plus.Q.obj K)))
    (derivedFlatBaseChangeHorizontal_middle_unit c d k a b f j hs h K)
  simp only [Category.assoc] at hmiddle
  erw [hmiddle, derivedFlatBaseChangeHorizontal_target_unit c d k a b f j hs h K]
  have hraw := congrArg (DerivedCategory.Plus.Q.map)
    (cartesianBaseChangeMap_paste_horiz_complex c d k a b f j hs h K)
  simp only [CategoryTheory.Functor.map_comp] at hraw
  have hfinal := congrArg (fun z => z ≫
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback (c ≫ a))
      (Scheme.Modules.pushforward d)).app K) hraw
  simpa only [Category.assoc] using hfinal

/-- Horizontal pasting is equality of the original derived base-change maps. -/
theorem derivedFlatBaseChangeMap_paste_horiz :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    derivedFlatBaseChangeHorizontalComposite c d k a b f j hs h =
      derivedFlatBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b k hs
  let := (Scheme.Modules.pushforward f).isRightDerivedFunctor_comp_of_preservesHomology
    (Scheme.Modules.pullback (k ≫ j))
  apply Functor.rightDerived_ext
    ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
      (Scheme.Modules.pullback (k ≫ j)).rightDerivedFunctorPlus)
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
      (Scheme.Modules.pullback (k ≫ j))) (CochainComplex.Plus.quasiIso U.Modules) _ _ _
  apply NatTrans.ext
  funext K
  exact (derivedFlatBaseChangeHorizontalComposite_unit c d k a b f j hs h K).trans
    (derivedFlatBaseChangeMap_unit (c ≫ a) d f (k ≫ j) (hs.paste_horiz h) K).symm
end AlgebraicGeometry.Scheme.Modules
