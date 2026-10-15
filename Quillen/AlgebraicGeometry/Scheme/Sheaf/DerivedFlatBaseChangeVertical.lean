/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.CartesianBaseChangePasting
/-! # Vertical pasting of the original derived flat base-change maps

The original mate of a vertically pasted cartesian square equals the composite of the two
original mates through the actual derived pushforward composition comparisons. The base leg
is flat; pulled-back flatness is derived from the cartesian square. The proof retains the
ordinary mate equation and installed composite units on all bounded-below complexes.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
/-- The original standard ambient categories. -/
local instance verticalStandard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {Z' Z W U V X : Scheme.{u}}
  (c : Z' ⟶ Z) (d : Z' ⟶ W) (g : Z ⟶ U)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d g a) (h : IsPullback a b f j) [Flat j]
/-- Vertical composition uses the actual two derived mates and pushforward comparisons. -/
def derivedFlatBaseChangeVerticalComposite :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d g a hs
    derivedPushforwardPlus (g ≫ f) ⋙ derivedFlatPullbackPlus j ⟶
      derivedFlatPullbackPlus c ⋙ derivedPushforwardPlus (d ≫ b) := by
  letI := flat_cartesian_baseChange a b f j h
  letI := flat_cartesian_baseChange c d g a hs
  exact
    (Functor.isoWhiskerRight (derivedPushforwardPlusCompIso g f)
      (derivedFlatPullbackPlus j)).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (derivedPushforwardPlus g) (derivedFlatBaseChangeMap a b f j h) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedFlatBaseChangeMap c d g a hs) (derivedPushforwardPlus b) ≫
    (Functor.associator _ _ _).hom ≫
    (Functor.isoWhiskerLeft (derivedFlatPullbackPlus c)
      (derivedPushforwardPlusCompIso d b).symm).hom
/-- The vertical component retains the two literal derived mates. -/
theorem derivedFlatBaseChangeVerticalComposite_app (K : DerivedCategory.Plus Z.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d g a hs
    (derivedFlatBaseChangeVerticalComposite c d g a b f j hs h).app K =
      (derivedFlatPullbackPlus j).map ((derivedPushforwardPlusCompIso g f).hom.app K) ≫
      (derivedFlatBaseChangeMap a b f j h).app ((derivedPushforwardPlus g).obj K) ≫
      (derivedPushforwardPlus b).map ((derivedFlatBaseChangeMap c d g a hs).app K) ≫
      (derivedPushforwardPlusCompIso d b).inv.app ((derivedFlatPullbackPlus c).obj K) := by
  simp [derivedFlatBaseChangeVerticalComposite]
omit [Flat j] in
/-- The vertical ordinary mate equation holds in the actual bounded-below complexes. -/
theorem cartesianBaseChangeMap_paste_vert_complex (K : CochainComplex.Plus Z.Modules) :
    (Scheme.Modules.pullback j).mapCochainComplexPlus.map
        ((NatIso.mapCochainComplexPlus (Scheme.Modules.pushforwardComp g f)).inv.app K) ≫
      (NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app
        ((Scheme.Modules.pushforward g).mapCochainComplexPlus.obj K) ≫
      (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap c d g a hs)).app K) ≫
      (NatIso.mapCochainComplexPlus (Scheme.Modules.pushforwardComp d b)).hom.app
        ((Scheme.Modules.pullback c).mapCochainComplexPlus.obj K) =
    (NatTrans.mapCochainComplexPlus
      (cartesianBaseChangeMap c (d ≫ b) (g ≫ f) j (hs.paste_vert h))).app K := by
  apply ObjectProperty.hom_ext
  ext n : 1
  change (Scheme.Modules.pullback j).map ((Scheme.Modules.pushforwardComp g f).inv.app _) ≫
      (cartesianBaseChangeMap a b f j h).app ((Scheme.Modules.pushforward g).obj (K.obj.X n)) ≫
      (Scheme.Modules.pushforward b).map ((cartesianBaseChangeMap c d g a hs).app (K.obj.X n)) ≫
      (Scheme.Modules.pushforwardComp d b).hom.app ((Scheme.Modules.pullback c).obj (K.obj.X n)) = _
  rw [← Category.assoc
    ((cartesianBaseChangeMap a b f j h).app ((Scheme.Modules.pushforward g).obj (K.obj.X n)))]
  rw [← cartesianBaseChangeMap_paste c d g a b f j hs h (K.obj.X n)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  simp only [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl
omit [Flat j] in
/-- The inverse direct-image comparison retains its original geometric unit square. -/
private theorem derivedPushforwardPlusCompIso_inv_unit (K : CochainComplex.Plus Z.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward g)
        (Scheme.Modules.pushforward f)).app K ≫
      (derivedPushforwardPlusCompIso g f).inv.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (Scheme.Modules.pushforwardComp g f)).hom.app K) ≫
      (derivedPushforwardPlusUnit (g ≫ f)).app K := by
  apply (Iso.comp_inv_eq ((derivedPushforwardPlusCompIso g f).app
    (DerivedCategory.Plus.Q.obj K))).mpr
  erw [Category.assoc, derivedPushforwardPlusCompIso_unit g f K]
  erw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  simp only [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  erw [Category.id_comp]

/-- The source comparison retains the original pushforward composite unit. -/
private theorem derivedFlatBaseChangeVertical_source_unit (K : CochainComplex.Plus Z.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward (g ≫ f))
        (Scheme.Modules.pullback j)).app K ≫
      (derivedFlatPullbackPlus j).map
        ((derivedPushforwardPlusCompIso g f).hom.app (DerivedCategory.Plus.Q.obj K)) =
    DerivedCategory.Plus.Q.map
        ((Scheme.Modules.pullback j).mapCochainComplexPlus.map
          ((NatIso.mapCochainComplexPlus (Scheme.Modules.pushforwardComp g f)).inv.app K)) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.pullback j)).app
          ((Scheme.Modules.pushforward g).mapCochainComplexPlus.obj K) ≫
      (derivedFlatPullbackPlus j).map
        ((derivedPushforwardPlus f).map ((derivedPushforwardPlusUnit g).app K)) := by
  have hm := congrArg ((derivedFlatPullbackPlus j).map)
    (derivedPushforwardPlusCompIso_unit g f K)
  simp only [CategoryTheory.Functor.map_comp] at hm
  rw [Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc]
  erw [hm]
  have hn := (Scheme.Modules.pullback j).rightDerivedFunctorPlusUnit.naturality
    ((NatIso.mapCochainComplexPlus (Scheme.Modules.pushforwardComp g f)).inv.app K)
  simp only [Functor.comp_map] at hn
  have hn' := congrArg (fun z => z ≫ (derivedFlatPullbackPlus j).map
    ((Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward g)
      (Scheme.Modules.pushforward f)).app K)) hn.symm
  simp only [Category.assoc] at hn'
  simp only [Functor.rightDerivedFunctorPlusCompUnit_app,
    CategoryTheory.Functor.map_comp, Category.assoc, derivedPushforwardPlus,
    derivedPushforwardPlusUnit, derivedFlatPullbackPlus, flatExactPullback,
    Functor.comp_obj] at hn' ⊢
  convert hn' using 1
  rfl

/-- The two original vertical mate squares retain the original units. -/
private theorem derivedFlatBaseChangeVertical_middle_unit (K : CochainComplex.Plus Z.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d g a hs
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.pullback j)).app
        ((Scheme.Modules.pushforward g).mapCochainComplexPlus.obj K) ≫
      (derivedFlatPullbackPlus j).map
        ((derivedPushforwardPlus f).map ((derivedPushforwardPlusUnit g).app K)) ≫
      (derivedFlatBaseChangeMap a b f j h).app
        ((derivedPushforwardPlus g).obj (DerivedCategory.Plus.Q.obj K)) ≫
      (derivedPushforwardPlus b).map
        ((derivedFlatBaseChangeMap c d g a hs).app (DerivedCategory.Plus.Q.obj K)) =
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app
          ((Scheme.Modules.pushforward g).mapCochainComplexPlus.obj K)) ≫
      DerivedCategory.Plus.Q.map
        ((Scheme.Modules.pushforward b).mapCochainComplexPlus.map
          ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap c d g a hs)).app K)) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward d)
        (Scheme.Modules.pushforward b)).app
          ((Scheme.Modules.pullback c).mapCochainComplexPlus.obj K) ≫
      (derivedPushforwardPlus b).map
        ((derivedPushforwardPlus d).map
          ((Scheme.Modules.pullback c).rightDerivedFunctorPlusUnit.app K)) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d g a hs
  have hn := (derivedFlatBaseChangeMap a b f j h).naturality
    ((derivedPushforwardPlusUnit g).app K)
  simp only [Functor.comp_map] at hn
  have hn' := congrArg (fun z => z ≫ (derivedPushforwardPlus b).map
    ((derivedFlatBaseChangeMap c d g a hs).app (DerivedCategory.Plus.Q.obj K))) hn
  simp only [Category.assoc] at hn'
  erw [hn']
  erw [← Category.assoc
    ((Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
      (Scheme.Modules.pullback j)).app _)]
  erw [derivedFlatBaseChangeMap_unit a b f j h
    ((Scheme.Modules.pushforward g).mapCochainComplexPlus.obj K)]
  simp only [Category.assoc]
  have hm := congrArg ((derivedPushforwardPlus b).map)
    (derivedFlatBaseChangeMap_unit c d g a hs K)
  simp only [Functor.rightDerivedFunctorPlusCompUnit_app,
    CategoryTheory.Functor.map_comp, Category.assoc] at hm
  erw [Functor.rightDerivedFunctorPlusCompUnit_app (Scheme.Modules.pullback a)
    (Scheme.Modules.pushforward b)]
  simp only [Category.assoc]
  erw [hm]
  erw [← Category.assoc
    ((Scheme.Modules.pushforward b).rightDerivedFunctorPlusUnit.app _)]
  erw [← (Scheme.Modules.pushforward b).rightDerivedFunctorPlusUnit.naturality
    ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap c d g a hs)).app K)]
  simp only [Functor.comp_map, Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc]
  rfl

/-- The target comparison retains the inverse direct-image composition and original units. -/
private theorem derivedFlatBaseChangeVertical_target_unit (K : CochainComplex.Plus Z.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d g a hs
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward d)
        (Scheme.Modules.pushforward b)).app
        ((Scheme.Modules.pullback c).mapCochainComplexPlus.obj K) ≫
      (derivedPushforwardPlus b).map
        ((derivedPushforwardPlus d).map
          ((Scheme.Modules.pullback c).rightDerivedFunctorPlusUnit.app K)) ≫
      (derivedPushforwardPlusCompIso d b).inv.app
        ((derivedFlatPullbackPlus c).obj (DerivedCategory.Plus.Q.obj K)) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (Scheme.Modules.pushforwardComp d b)).hom.app
          ((Scheme.Modules.pullback c).mapCochainComplexPlus.obj K)) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback c)
        (Scheme.Modules.pushforward (d ≫ b))).app K := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d g a hs
  erw [(derivedPushforwardPlusCompIso d b).inv.naturality
    ((Scheme.Modules.pullback c).rightDerivedFunctorPlusUnit.app K)]
  erw [← Category.assoc, derivedPushforwardPlusCompIso_inv_unit d b
    ((Scheme.Modules.pullback c).mapCochainComplexPlus.obj K)]
  simp only [Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc]
  rfl

/-- The vertical composite retains the original ordinary mate in its installed unit square. -/
theorem derivedFlatBaseChangeVerticalComposite_unit (K : CochainComplex.Plus Z.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d g a hs
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward (g ≫ f))
        (Scheme.Modules.pullback j)).app K ≫
      (derivedFlatBaseChangeVerticalComposite c d g a b f j hs h).app
        (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus
          (cartesianBaseChangeMap c (d ≫ b) (g ≫ f) j (hs.paste_vert h))).app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback c)
        (Scheme.Modules.pushforward (d ≫ b))).app K := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d g a hs
  erw [derivedFlatBaseChangeVerticalComposite_app]
  have hsource := congrArg (fun z => z ≫
    (derivedFlatBaseChangeMap a b f j h).app
      ((derivedPushforwardPlus g).obj (DerivedCategory.Plus.Q.obj K)) ≫
    (derivedPushforwardPlus b).map
      ((derivedFlatBaseChangeMap c d g a hs).app (DerivedCategory.Plus.Q.obj K)) ≫
    (derivedPushforwardPlusCompIso d b).inv.app
      ((derivedFlatPullbackPlus c).obj (DerivedCategory.Plus.Q.obj K)))
    (derivedFlatBaseChangeVertical_source_unit g f j K)
  simp only [Category.assoc] at hsource
  erw [hsource]
  have hmiddle := congrArg (fun z => z ≫ (derivedPushforwardPlusCompIso d b).inv.app
    ((derivedFlatPullbackPlus c).obj (DerivedCategory.Plus.Q.obj K)))
    (derivedFlatBaseChangeVertical_middle_unit c d g a b f j hs h K)
  simp only [Category.assoc] at hmiddle
  erw [hmiddle, derivedFlatBaseChangeVertical_target_unit c d g a b f j hs h K]
  have hraw := congrArg (DerivedCategory.Plus.Q.map)
    (cartesianBaseChangeMap_paste_vert_complex c d g a b f j hs h K)
  simp only [CategoryTheory.Functor.map_comp] at hraw
  have hfinal := congrArg (fun z => z ≫
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback c)
      (Scheme.Modules.pushforward (d ≫ b))).app K) hraw
  simpa only [Category.assoc] using hfinal
/-- Vertical pasting is equality of the original derived base-change maps. -/
theorem derivedFlatBaseChangeMap_paste_vert :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d g a hs
    derivedFlatBaseChangeVerticalComposite c d g a b f j hs h =
      derivedFlatBaseChangeMap c (d ≫ b) (g ≫ f) j (hs.paste_vert h) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d g a hs
  let := (Scheme.Modules.pushforward (g ≫ f)).isRightDerivedFunctor_comp_of_preservesHomology
    (Scheme.Modules.pullback j)
  apply Functor.rightDerived_ext
    ((Scheme.Modules.pushforward (g ≫ f)).rightDerivedFunctorPlus ⋙
      (Scheme.Modules.pullback j).rightDerivedFunctorPlus)
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward (g ≫ f))
      (Scheme.Modules.pullback j)) (CochainComplex.Plus.quasiIso Z.Modules) _ _ _
  apply NatTrans.ext
  funext K
  exact (derivedFlatBaseChangeVerticalComposite_unit c d g a b f j hs h K).trans
    (derivedFlatBaseChangeMap_unit c (d ≫ b) (g ≫ f) j (hs.paste_vert h) K).symm
end AlgebraicGeometry.Scheme.Modules
