/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.GTheory.SmallModelLocalization
public import Quillen.KTheory.Map.SmallModelUniverse
public import Quillen.Localization.Serre.Naturality
public import Quillen.Topology.ClassifyingSpace.UniversePromotion
public import Quillen.CategoryTheory.SmallModel.Functoriality
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Naturality of the original SmallModel localization boundaries

The same-universe square uses the original exact functors and ordinary natural
isomorphism. Universe promotion retains each original normalized localization
row and its complete zero-nullhomotopy. The upper relative comparison is pulled
back along the actual `AsSmall.up` map, then the original fiber-comparison
bijection gives naturality of the original connecting homomorphism.

`Universe.connectingHom_universe` compares the two actual SmallModels of one
localization functor. Its target comparison is the original
`smallKUniverseEquiv`; its supported comparison is the restriction of the actual
model comparison. No boundary comparison or homotopy-coherence law is an input.
The principal-closed scheme boundary is the current application.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w w₁ w₂ u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject Topology unitInterval

namespace Quillen.SmallModelBoundaryNaturality.Upward
variable {C : Type u} [SmallCategory C] {D : Type (max u v)} [SmallCategory D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

private def sourceLiftedQ : AsSmall.{max u v} EC.QCategory ⥤ ED.QCategory := AsSmall.down ⋙ F.mapQ

private def normalizedLiftedQ : AsSmall.{max u v} EC.QCategory ⥤ ED.QCategory :=
  rebaseFunctor (sourceLiftedQ F) (AsSmall.up.obj EC.qZero) ED.qZero
    (ED.qIsoOfIso F.toFunctor.mapZeroObject)

private def sourceUpKMap (n : ℕ) : EC.K n →*
    ShiftedHomotopyGroup (AsSmall.{max u v} EC.QCategory) (AsSmall.up.obj EC.qZero) n :=
  piMap n (classifyingSpaceMapUniversal
    (AsSmall.up : EC.QCategory ⥤ AsSmall.{max u v} EC.QCategory))
    (classifyingSpaceMapUniversal_point AsSmall.up EC.qZero)

private def normalizedLiftedKMap (n : ℕ) : EC.K n →* ED.K n :=
  (pointedShiftedHomotopyGroupMap (sourceLiftedQ F) (AsSmall.up.obj EC.qZero) ED.qZero
    (ED.qIsoOfIso F.toFunctor.mapZeroObject) n).comp (sourceUpKMap (EC := EC) n)

private theorem correctedCast {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y z : Y} (h : f x = y) (p : Path y z)
    (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport (p.cast h rfl) n (homotopyGroupMap f rfl a) =
      pathTransport p n (homotopyGroupMap f h a) := by
  subst y
  rfl

private theorem normalizedLiftedKMap_eq_universalKMap (n : ℕ) :
    normalizedLiftedKMap F n = F.universalKMap n := by
  ext a
  let U : EC.QCategory ⥤ AsSmall.{max u v} EC.QCategory := AsSmall.up
  let z := ED.qIsoOfIso F.toFunctor.mapZeroObject
  let b := sourceUpKMap (EC := EC) n a
  have hr := pathTransport_rebaseFunctor_homotopyGroupMap (sourceLiftedQ F)
    (AsSmall.up.obj EC.qZero) ED.qZero z (n+1) b
  have hc := correctedCast (classifyingSpaceMap (sourceLiftedQ F)).hom
    (classifyingSpaceMap_point (sourceLiftedQ F) (AsSmall.up.obj EC.qZero))
    (classifyingSpacePath z.hom) (n+1) b
  have hm : homotopyGroupMap (classifyingSpaceMap (sourceLiftedQ F)).hom
      (classifyingSpaceMap_point (sourceLiftedQ F) (AsSmall.up.obj EC.qZero)) b =
    homotopyGroupMap (classifyingSpaceMapUniversal F.mapQ)
      (classifyingSpaceMapUniversal_point F.mapQ EC.qZero) a := by
    change homotopyGroupMap (classifyingSpaceMap (sourceLiftedQ F)).hom _
      (homotopyGroupMap (classifyingSpaceMapUniversal U)
        (classifyingSpaceMapUniversal_point U EC.qZero) a) = _
    rw [← homotopyGroupMap_comp]
    have hmap : (classifyingSpaceMap (sourceLiftedQ F)).hom.comp
        (classifyingSpaceMapUniversal U) = classifyingSpaceMapUniversal F.mapQ := by
      rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_comp]
      rfl
    exact congrFun (homotopyGroupMap_congr hmap _ _) a
  exact hr.symm.trans (hc.trans
    ((congrArg (pathTransport (classifyingSpacePath z.hom) (n+1)) hm).trans
      (F.universalKMap_apply n a).symm))

end Quillen.SmallModelBoundaryNaturality.Upward


namespace Quillen.SmallModelBoundaryNaturality.Upward
variable {A C : Type u} [SmallCategory A] [SmallCategory C]
  {D E : Type (max u v)} [SmallCategory D] [SmallCategory E]
  [Preadditive A] [HasFiniteBiproducts A] [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D] [Preadditive E] [HasFiniteBiproducts E]
  {EA : ExactStructure A} {EC : ExactStructure C} {ED : ExactStructure D} {EE : ExactStructure E}

private def normalizedLiftedIso (F : ExactFunctor EC ED) : sourceLiftedQ F ≅ normalizedLiftedQ F :=
  rebaseFunctorIso (sourceLiftedQ F) (AsSmall.up.obj EC.qZero) ED.qZero
    (ED.qIsoOfIso F.toFunctor.mapZeroObject)

private def rawNormalizedIso (F : ExactFunctor EA EC) : F.mapQ ≅ F.normalizedQ :=
  rebaseFunctorIso F.mapQ EA.qZero EC.qZero (EC.qIsoOfIso F.toFunctor.mapZeroObject)

private def normalizedLiftedNatIso {F G : ExactFunctor EC ED} (e : F.toFunctor ≅ G.toFunctor) :
    normalizedLiftedQ F ≅ normalizedLiftedQ G :=
  (normalizedLiftedIso F).symm ≪≫
    Functor.isoWhiskerLeft AsSmall.down (ExactFunctor.mapQIso e) ≪≫ normalizedLiftedIso G

private def leftCompositionIso (H : ExactFunctor EA EC) (F : ExactFunctor EC ED) :
    universeLiftFunctor.{u,u,u,u,max u v} H.normalizedQ ⋙ normalizedLiftedQ F ≅
      normalizedLiftedQ (H.comp F) := by
  refine Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft AsSmall.down
      (Functor.isoWhiskerRight (rawNormalizedIso H).symm AsSmall.up))
        (normalizedLiftedQ F) ≪≫
    Functor.isoWhiskerLeft (universeLiftFunctor.{u,u,u,u,max u v} H.mapQ)
      (normalizedLiftedIso F).symm ≪≫ ?_ ≪≫ normalizedLiftedIso (H.comp F)
  apply eqToIso
  change AsSmall.down ⋙ H.mapQ ⋙ F.mapQ = AsSmall.down ⋙ (H.comp F).mapQ
  rw [ExactFunctor.mapQ_comp]

private def rightCompositionIso (F : ExactFunctor EC ED) (G : ExactFunctor ED EE) :
    normalizedLiftedQ F ⋙ G.normalizedQ ≅ normalizedLiftedQ (F.comp G) := by
  refine Functor.isoWhiskerRight (normalizedLiftedIso F).symm G.normalizedQ ≪≫
    Functor.isoWhiskerLeft (sourceLiftedQ F)
      (rebaseFunctorIso G.mapQ ED.qZero EE.qZero
        (EE.qIsoOfIso G.toFunctor.mapZeroObject)).symm ≪≫ ?_ ≪≫
          normalizedLiftedIso (F.comp G)
  apply eqToIso
  change AsSmall.down ⋙ F.mapQ ⋙ G.mapQ = AsSmall.down ⋙ (F.comp G).mapQ
  rw [ExactFunctor.mapQ_comp]

private theorem normalizedLiftedQ_obj_zero (F : ExactFunctor EC ED) :
    (normalizedLiftedQ F).obj (AsSmall.up.obj EC.qZero) = ED.qZero :=
  rebaseFunctor_obj_base _ _ _ _

private def normalizedMap (F : ExactFunctor EC ED) : C(EC.KSpace, ED.KSpace) :=
  (classifyingSpaceMap (normalizedLiftedQ F)).hom.comp
    (classifyingSpaceMapUniversal (AsSmall.up : EC.QCategory ⥤ AsSmall.{max u v} EC.QCategory))

private theorem normalizedMap_point (F : ExactFunctor EC ED) :
    normalizedMap F EC.kBasepoint = ED.kBasepoint := by
  change classifyingSpaceMap (normalizedLiftedQ F)
    (classifyingSpaceMapUniversal AsSmall.up (classifyingSpacePoint EC.qZero)) = _
  rw [classifyingSpaceMapUniversal_point, classifyingSpaceMap_point, normalizedLiftedQ_obj_zero]
  rfl

private theorem universalKMap_eq_piMap (F : ExactFunctor EC ED) (n : ℕ) :
    F.universalKMap n = piMap n (normalizedMap F) (normalizedMap_point F) := by
  rw [← normalizedLiftedKMap_eq_universalKMap]
  change (piMap n (classifyingSpaceMap (normalizedLiftedQ F)).hom _).comp
    (piMap n (classifyingSpaceMapUniversal AsSmall.up) _) = _
  rw [← homotopyGroupMapHom_comp]
  rfl

end Quillen.SmallModelBoundaryNaturality.Upward


namespace Quillen.SmallModelBoundaryNaturality.Upward
attribute [local instance] Abelian.hasFiniteBiproducts SerreLocalization.canonicalQuotientAbelian
open SerreLocalization
variable {C : Type u} [Category.{u} C] [Abelian C]
  {C' : Type (max u v)} [Category.{max u v} C'] [Abelian C']
  (P : ObjectProperty C) [P.IsSerreClass] (Q : ObjectProperty C') [Q.IsSerreClass]
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure C'))
  (hF : ∀ X : C, P X → Q (F.toFunctor.obj X))

private def supportFunctor : P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F.toFunctor) (fun X => hF X.obj X.property)
private instance supportFunctor_additive : (supportFunctor P Q F hF).Additive := by
  unfold supportFunctor
  infer_instance

private def supportExact : ExactFunctor (ObjectProperty.subcategoryExactStructure P)
    (ObjectProperty.subcategoryExactStructure Q) where
  toFunctor := supportFunctor P Q F hF
  map_conflation T hT := by
    have h : ((T.map (supportFunctor P Q F hF)).map Q.ι).ShortExact :=
      F.map_conflation (T.map P.ι) ((ObjectProperty.exactInclusion P).map_conflation T hT)
    exact {
      exact := Q.ι.reflects_exact_of_faithful _ h.exact
      mono_f := Q.ι.mono_of_mono_map h.mono_f
      epi_g := Q.ι.epi_of_epi_map h.epi_g }

private def supportSquareIso :
    universeLiftFunctor.{u,u,u,u,max u v} (inclusionNormalizedQ P) ⋙ normalizedLiftedQ F ≅
      normalizedLiftedQ (supportExact P Q F hF) ⋙ inclusionNormalizedQ Q :=
  leftCompositionIso (ObjectProperty.exactInclusion P) F ≪≫
    normalizedLiftedNatIso (F := (ObjectProperty.exactInclusion P).comp F)
      (G := (supportExact P Q F hF).comp (ObjectProperty.exactInclusion Q)) (Iso.refl _) ≪≫
    (rightCompositionIso (supportExact P Q F hF) (ObjectProperty.exactInclusion Q)).symm

variable {D : Type u} [Category.{u} D] [Abelian D]
  {D' : Type (max u v)} [Category.{max u v} D'] [Abelian D']
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]
  (L' : C' ⥤ D') [L'.IsLocalization Q.isoModSerre] [L'.Additive]
  (U : ExactFunctor (abelianExactStructure D) (abelianExactStructure D'))
  (e : L ⋙ U.toFunctor ≅ F.toFunctor ⋙ L')

private def quotientExact : ExactFunctor (abelianExactStructure P.isoModSerre.Localization)
    (abelianExactStructure Q.isoModSerre.Localization) :=
  ((targetLiftExactFunctor P L).comp U).comp (targetInverseExactFunctor Q L')

private def quotientOrdinaryIso :
    ((ExactFunctor.serreLocalization P P.isoModSerre.Q).comp
      (quotientExact P Q L L' U)).toFunctor ≅
    (F.comp (ExactFunctor.serreLocalization Q Q.isoModSerre.Q)).toFunctor := by
  let E := (targetLift Q L').asEquivalence
  change ((P.isoModSerre.Q ⋙ targetLift P L) ⋙ U.toFunctor) ⋙ E.inverse ≅
    F.toFunctor ⋙ Q.isoModSerre.Q
  rw [targetLift_fac]
  refine Functor.isoWhiskerRight e E.inverse ≪≫ ?_
  rw [← targetLift_fac Q L']
  exact Functor.isoWhiskerLeft (F.toFunctor ⋙ Q.isoModSerre.Q) E.unitIso.symm ≪≫
    Functor.rightUnitor _

private def quotientSquareIso :
    universeLiftFunctor.{u,u,u,u,max u v} (quotientNormalizedQ P) ⋙
      normalizedLiftedQ (quotientExact P Q L L' U) ≅
    normalizedLiftedQ F ⋙ quotientNormalizedQ Q :=
  leftCompositionIso (ExactFunctor.serreLocalization P P.isoModSerre.Q)
      (quotientExact P Q L L' U) ≪≫
    normalizedLiftedNatIso (quotientOrdinaryIso P Q F L L' U e) ≪≫
    (rightCompositionIso F (ExactFunctor.serreLocalization Q Q.isoModSerre.Q)).symm


private def upperSquareHomotopy :=
  Naturality.squareHomotopy
    (universeLiftFunctor.{u,u,u,u,max u v} (quotientNormalizedQ P)) (quotientNormalizedQ Q)
    (normalizedLiftedQ F) (normalizedLiftedQ (quotientExact P Q L L' U))
    (quotientSquareIso P Q F L L' U e).hom

private def upperFiberMap :=
  HomotopyFiber.basedHomotopySquareMap
    (classifyingSpaceMap (normalizedLiftedQ F)).hom
    (classifyingSpaceMap (normalizedLiftedQ (quotientExact P Q L L' U))).hom
    (upperSquareHomotopy P Q F L L' U e)
    (classifyingSpacePoint
      (AsSmall.up.obj (abelianExactStructure P.isoModSerre.Localization).qZero))
    (abelianExactStructure Q.isoModSerre.Localization).kBasepoint
    ((classifyingSpaceMap_point _ _).trans
      (congrArg classifyingSpacePoint (normalizedLiftedQ_obj_zero _)))

private def upperComparisonHomotopy :
    ((upperFiberMap P Q F L L' U e).comp
      (TheoremB.naturalTransformationFiberLift
        (universeLiftFunctor.{u,u,u,u,max u v} (inclusionNormalizedQ P))
        (universeLiftFunctor.{u,u,u,u,max u v} (quotientNormalizedQ P))
        (AsSmall.up.obj (abelianExactStructure P.isoModSerre.Localization).qZero)
        (UniversePromotion.liftNullTransformation (inclusionNormalizedQ P)
          (quotientNormalizedQ P) _ (normalizedQuotientInclusionZeroIso P).hom))).HomotopyRel
      ((basedLocalizationFiberComparison Q).comp
        (classifyingSpaceMap (normalizedLiftedQ (supportExact P Q F hF))).hom)
      {classifyingSpacePoint
        (AsSmall.up.obj (ObjectProperty.subcategoryExactStructure P).qZero)} := by
  apply Naturality.fiberSquareComparisonHomotopyRelAt
    (universeLiftFunctor.{u,u,u,u,max u v} (inclusionNormalizedQ P))
    (universeLiftFunctor.{u,u,u,u,max u v} (quotientNormalizedQ P))
    (inclusionNormalizedQ Q) (quotientNormalizedQ Q)
    (normalizedLiftedQ (supportExact P Q F hF)) (normalizedLiftedQ F)
    (normalizedLiftedQ (quotientExact P Q L L' U))
    (AsSmall.up.obj (abelianExactStructure P.isoModSerre.Localization).qZero)
    (abelianExactStructure Q.isoModSerre.Localization).qZero
    (UniversePromotion.liftNullTransformation (inclusionNormalizedQ P)
      (quotientNormalizedQ P) _ (normalizedQuotientInclusionZeroIso P).hom)
    (normalizedQuotientInclusionZeroIso Q).hom
    (supportSquareIso P Q F hF).hom (quotientSquareIso P Q F L L' U e).hom
    (normalizedLiftedQ_obj_zero _)
    (AsSmall.up.obj (ObjectProperty.subcategoryExactStructure P).qZero)
    (abelianExactStructure C').qZero
  · change (normalizedLiftedQ F).obj (AsSmall.up.obj
      ((ObjectProperty.exactInclusion P).normalizedQ.obj
        (ObjectProperty.subcategoryExactStructure P).qZero)) = _
    rw [SerreLocalization.normalizedQ_obj_zero, normalizedLiftedQ_obj_zero]
  · change (ObjectProperty.exactInclusion Q).normalizedQ.obj
      ((normalizedLiftedQ (supportExact P Q F hF)).obj
        (AsSmall.up.obj (ObjectProperty.subcategoryExactStructure P).qZero)) = _
    rw [normalizedLiftedQ_obj_zero, SerreLocalization.normalizedQ_obj_zero]
  · exact SerreLocalization.normalizedQ_obj_zero _
  · change (normalizedLiftedQ (quotientExact P Q L L' U)).obj (AsSmall.up.obj
      ((ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ.obj
        ((ObjectProperty.exactInclusion P).normalizedQ.obj
          (ObjectProperty.subcategoryExactStructure P).qZero))) = _
    rw [SerreLocalization.normalizedQ_obj_zero, SerreLocalization.normalizedQ_obj_zero,
      normalizedLiftedQ_obj_zero]
  · exact fun Y => (abelianExactStructure C').qHom_subsingleton_of_isZero Y _ (isZero_zero _)
  · exact fun Y => (abelianExactStructure Q.isoModSerre.Localization).qHom_subsingleton_of_isZero
      Y _ (isZero_zero _)

private def squareHomotopy :
    ((normalizedMap (quotientExact P Q L L' U)).comp
      (classifyingSpaceMap (quotientNormalizedQ P)).hom).Homotopy
    ((classifyingSpaceMap (quotientNormalizedQ Q)).hom.comp (normalizedMap F)) :=
  ((upperSquareHomotopy P Q F L L' U e).compContinuousMap
    (classifyingSpaceMapUniversal (AsSmall.up : (abelianExactStructure C).QCategory ⥤
      AsSmall.{max u v} (abelianExactStructure C).QCategory))).cast
    (by
      apply ContinuousMap.ext
      intro x
      exact congrArg (classifyingSpaceMap (normalizedLiftedQ (quotientExact P Q L L' U)))
        (ContinuousMap.congr_fun (UniversePromotion.liftedRowSquare.{u,v}
          (quotientNormalizedQ P)) x).symm)
    rfl


private theorem squareHomotopy_basepoint (t : unitInterval) :
    squareHomotopy P Q F L L' U e (t, (abelianExactStructure C).kBasepoint) =
      (abelianExactStructure Q.isoModSerre.Localization).kBasepoint := by
  change upperSquareHomotopy P Q F L L' U e
    (t, classifyingSpaceMapUniversal AsSmall.up
      (classifyingSpacePoint (abelianExactStructure C).qZero)) = _
  rw [classifyingSpaceMapUniversal_point]
  apply Naturality.edge_vertex (quotientSquareIso P Q F L L' U e).hom _ _ _ _
    (fun Y => (abelianExactStructure Q.isoModSerre.Localization).qHom_subsingleton_of_isZero
      Y _ (isZero_zero _)) t
  · change (normalizedLiftedQ (quotientExact P Q L L' U)).obj (AsSmall.up.obj
      ((ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ.obj
        (abelianExactStructure C).qZero)) = _
    rw [SerreLocalization.normalizedQ_obj_zero, normalizedLiftedQ_obj_zero]
  · change (ExactFunctor.serreLocalization Q Q.isoModSerre.Q).normalizedQ.obj
      ((normalizedLiftedQ F).obj (AsSmall.up.obj (abelianExactStructure C).qZero)) = _
    rw [normalizedLiftedQ_obj_zero, SerreLocalization.normalizedQ_obj_zero]

private def fiberMap : C(NormalizedLocalizationFiber P, NormalizedLocalizationFiber Q) :=
  HomotopyFiber.basedHomotopySquareMap (normalizedMap F)
    (normalizedMap (quotientExact P Q L L' U)) (squareHomotopy P Q F L L' U e) _ _
    (normalizedMap_point (quotientExact P Q L L' U))

private theorem fiberMap_eq_upper :
    fiberMap P Q F L L' U e = (upperFiberMap P Q F L L' U e).comp
      (UniversePromotion.rowFiberUp.{u,v} (quotientNormalizedQ P)
        (abelianExactStructure P.isoModSerre.Localization).qZero) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

private def comparisonHomotopy :
    ((fiberMap P Q F L L' U e).comp (basedLocalizationFiberComparison P)).HomotopyRel
      ((basedLocalizationFiberComparison Q).comp (normalizedMap (supportExact P Q F hF)))
      {(ObjectProperty.subcategoryExactStructure P).kBasepoint} := by
  let Hup := upperComparisonHomotopy P Q F hF L L' U e
  let H := Hup.toHomotopy.compContinuousMap
    (classifyingSpaceMapUniversal
      (AsSmall.up : (ObjectProperty.subcategoryExactStructure P).QCategory ⥤
        AsSmall.{max u v} (ObjectProperty.subcategoryExactStructure P).QCategory))
  have hstart :
      ((upperFiberMap P Q F L L' U e).comp
        (TheoremB.naturalTransformationFiberLift
          (universeLiftFunctor.{u,u,u,u,max u v} (inclusionNormalizedQ P))
          (universeLiftFunctor.{u,u,u,u,max u v} (quotientNormalizedQ P))
          (AsSmall.up.obj (abelianExactStructure P.isoModSerre.Localization).qZero)
          (UniversePromotion.liftNullTransformation (inclusionNormalizedQ P)
            (quotientNormalizedQ P) _ (normalizedQuotientInclusionZeroIso P).hom))).comp
        (classifyingSpaceMapUniversal AsSmall.up) =
      (fiberMap P Q F L L' U e).comp (basedLocalizationFiberComparison P) := by
    rw [fiberMap_eq_upper]
    rw [ContinuousMap.comp_assoc, ← UniversePromotion.rowFiberUp_naturalLift]
    rfl
  let H' := H.cast hstart rfl
  refine { toHomotopy := H', prop' := ?_ }
  intro t z hz
  have hz' : z = (ObjectProperty.subcategoryExactStructure P).kBasepoint :=
    Set.mem_singleton_iff.mp hz
  subst z
  have hf : H' (t, (ObjectProperty.subcategoryExactStructure P).kBasepoint) =
      H' (0, (ObjectProperty.subcategoryExactStructure P).kBasepoint) := by
    change Hup (t, classifyingSpaceMapUniversal AsSmall.up
      (classifyingSpacePoint (ObjectProperty.subcategoryExactStructure P).qZero)) =
        Hup (0, classifyingSpaceMapUniversal AsSmall.up
          (classifyingSpacePoint (ObjectProperty.subcategoryExactStructure P).qZero))
    rw [classifyingSpaceMapUniversal_point]
    exact (Hup.prop t _ (Set.mem_singleton _)).trans
      (Hup.prop 0 _ (Set.mem_singleton _)).symm
  exact hf.trans (H'.apply_zero _)

private theorem fiberMap_basepoint :
    fiberMap P Q F L L' U e (normalizedFiberBasepoint P) = normalizedFiberBasepoint Q :=
  HomotopyFiber.basedHomotopySquareMap_basepoint
    (normalizedMap F) (normalizedMap (quotientExact P Q L L' U))
    (squareHomotopy P Q F L L' U e)
    (abelianExactStructure C).kBasepoint
    (abelianExactStructure P.isoModSerre.Localization).kBasepoint
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ_map_point
    (abelianExactStructure C').kBasepoint
    (abelianExactStructure Q.isoModSerre.Localization).kBasepoint
    (normalizedMap_point F) (normalizedMap_point (quotientExact P Q L L' U))
    (ExactFunctor.serreLocalization Q Q.isoModSerre.Q).normalizedQ_map_point
    (squareHomotopy_basepoint P Q F L L' U e)


set_option maxHeartbeats 800000 in
-- Elaboration compares the original fiber-group types across the two model universes.
private theorem comparisonHom_naturality (n : ℕ) :
    (localizationFiberComparisonHom Q n).comp ((supportExact P Q F hF).universalKMap n) =
      (piMap n (fiberMap P Q F L L' U e) (fiberMap_basepoint P Q F L L' U e)).comp
        (localizationFiberComparisonHom P n) := by
  let Hc := comparisonHomotopy P Q F hF L L' U e
  have hfixed : ∀ t, Hc.toHomotopy
      (t, (ObjectProperty.subcategoryExactStructure P).kBasepoint) =
        normalizedFiberBasepoint Q := by
    intro t
    exact (Hc.prop t _ (Set.mem_singleton _)).trans
      ((congrArg (fiberMap P Q F L L' U e) (basedLocalizationFiberComparison_basepoint P)).trans
        (fiberMap_basepoint P Q F L L' U e))
  rw [universalKMap_eq_piMap]
  unfold localizationFiberComparisonHom
  rw [← homotopyGroupMapHom_comp, ← homotopyGroupMapHom_comp]
  exact (piMap_eq_of_based_homotopy n _ _ Hc.toHomotopy hfixed).symm

include e in
private theorem formalConnectingHom_naturality (n : ℕ) :
    ((supportExact P Q F hF).universalKMap n).comp (connectingHom P n) =
      (connectingHom Q n).comp ((quotientExact P Q L L' U).universalKMap (n + 1)) := by
  have htop := HomotopyFiber.connectingHom_basedHomotopySquare_natural
    (normalizedMap F) (normalizedMap (quotientExact P Q L L' U))
    (squareHomotopy P Q F L L' U e)
    (abelianExactStructure C).kBasepoint
    (abelianExactStructure P.isoModSerre.Localization).kBasepoint
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ_map_point
    (abelianExactStructure C').kBasepoint
    (abelianExactStructure Q.isoModSerre.Localization).kBasepoint
    (normalizedMap_point F) (normalizedMap_point (quotientExact P Q L L' U))
    (ExactFunctor.serreLocalization Q Q.isoModSerre.Q).normalizedQ_map_point
    (squareHomotopy_basepoint P Q F L L' U e) n
  rw [← universalKMap_eq_piMap] at htop
  apply MonoidHom.ext
  intro a
  apply (localizationFiberComparisonHom_bijective Q n).injective
  have hc := DFunLike.congr_fun (comparisonHom_naturality P Q F hF L L' U e n)
    (connectingHom P n a)
  have hp := DFunLike.congr_fun (comparison_comp_connectingHom P n) a
  have hq := DFunLike.congr_fun (comparison_comp_connectingHom Q n)
    ((quotientExact P Q L L' U).universalKMap (n + 1) a)
  change localizationFiberComparisonHom Q n
      ((supportExact P Q F hF).universalKMap n (connectingHom P n a)) =
    localizationFiberComparisonHom Q n (connectingHom Q n
      ((quotientExact P Q L L' U).universalKMap (n + 1) a))
  calc
    _ = piMap n (fiberMap P Q F L L' U e) (fiberMap_basepoint P Q F L L' U e)
        (localizationFiberComparisonHom P n (connectingHom P n a)) := hc
    _ = piMap n (fiberMap P Q F L L' U e) (fiberMap_basepoint P Q F L L' U e)
        (fiberConnectingHom P n a) := congrArg _ hp
    _ = fiberConnectingHom Q n
        ((quotientExact P Q L L' U).universalKMap (n + 1) a) := DFunLike.congr_fun htop a
    _ = _ := hq.symm

private def actualTargetSquareIso :
    ((targetLiftExactFunctor P L).comp U).toFunctor ≅
      ((quotientExact P Q L L' U).comp (targetLiftExactFunctor Q L')).toFunctor := by
  let E := (targetLift Q L').asEquivalence
  exact (Functor.rightUnitor (targetLift P L ⋙ U.toFunctor)).symm ≪≫
    Functor.isoWhiskerLeft (targetLift P L ⋙ U.toFunctor) E.counitIso.symm

include e in
private theorem actualConnectingHom_naturality (n : ℕ) :
    ((supportExact P Q F hF).universalKMap n).comp (actualConnectingHom P L n) =
      (actualConnectingHom Q L' n).comp (U.universalKMap (n + 1)) := by
  have ht := ExactFunctor.universalKMap_eq_of_natIso (actualTargetSquareIso P Q L L' U) (n + 1)
  rw [ExactFunctor.universalKMap_comp, ExactFunctor.universalKMap_comp,
    ExactFunctor.universalKMap_eq_KMap (targetLiftExactFunctor P L),
    ExactFunctor.universalKMap_eq_KMap (targetLiftExactFunctor Q L')] at ht
  have hc := formalConnectingHom_naturality P Q F hF L L' U e n
  apply MonoidHom.ext
  intro a
  obtain ⟨x, rfl⟩ := (targetKEquiv P L (n + 1)).surjective a
  have hx : U.universalKMap (n + 1) (targetKEquiv P L (n + 1) x) =
      targetKEquiv Q L' (n + 1) ((quotientExact P Q L L' U).universalKMap (n + 1) x) :=
    DFunLike.congr_fun ht x
  change (supportExact P Q F hF).universalKMap n (connectingHom P n
      ((targetKEquiv P L (n + 1)).symm (targetKEquiv P L (n + 1) x))) =
    connectingHom Q n ((targetKEquiv Q L' (n + 1)).symm
      (U.universalKMap (n + 1) (targetKEquiv P L (n + 1) x)))
  rw [MulEquiv.symm_apply_apply, hx, MulEquiv.symm_apply_apply]
  exact DFunLike.congr_fun hc x

end Quillen.SmallModelBoundaryNaturality.Upward


namespace Quillen.SmallModelBoundaryNaturality.Square
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EssentiallySmall.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [EssentiallySmall.{w} D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] [EssentiallySmall.{w} C']
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D'] [EssentiallySmall.{w} D']
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))
  (F' : ExactFunctor (abelianExactStructure C') (abelianExactStructure D'))
  (V : ExactFunctor (abelianExactStructure C) (abelianExactStructure C'))
  (U : ExactFunctor (abelianExactStructure D) (abelianExactStructure D'))
  (e : (F.comp U).toFunctor ≅ (V.comp F').toFunctor)

/-- The ordinary square obtained from the original chosen-model unit isomorphisms. -/
def ordinarySquare :
    CategoryTheory.SmallModel.functor F.toFunctor ⋙
      (CategoryTheory.SmallModel.mapAbelianExactFunctor U).toFunctor ≅
    (CategoryTheory.SmallModel.mapAbelianExactFunctor V).toFunctor ⋙
      CategoryTheory.SmallModel.functor F'.toFunctor :=
  (ExactFunctor.smallModelCompIso F U).symm ≪≫
    ExactFunctor.smallModelNatIso e ≪≫ ExactFunctor.smallModelCompIso V F'

include e in
/-- The actual ambient comparison sends kernel objects into the target kernel. -/
theorem preservesSupported (X : SmallModel.{w} C)
    (hX : SmallModelGLocalization.supported F X) :
    SmallModelGLocalization.supported F'
      ((CategoryTheory.SmallModel.mapAbelianExactFunctor V).toFunctor.obj X) := by
  have h : IsZero ((CategoryTheory.SmallModel.mapAbelianExactFunctor U).toFunctor.obj
      ((CategoryTheory.SmallModel.functor F.toFunctor).obj X)) :=
    (CategoryTheory.SmallModel.mapAbelianExactFunctor U).toFunctor.map_isZero hX
  exact h.of_iso ((ordinarySquare F F' V U e).app X).symm

variable
  [PreservesFiniteLimits F.toFunctor] [PreservesFiniteColimits F.toFunctor]
  [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre]
  [PreservesFiniteLimits F'.toFunctor] [PreservesFiniteColimits F'.toFunctor]
  [F'.toFunctor.IsLocalization F'.toFunctor.kernel.isoModSerre]

/-- The original ambient functor restricted to the actual supported categories. -/
def supportExact : ExactFunctor
    (ObjectProperty.subcategoryExactStructure (SmallModelGLocalization.supported F))
    (ObjectProperty.subcategoryExactStructure (SmallModelGLocalization.supported F')) :=
  SerreLocalization.inducedSupportExactFunctor (SmallModelGLocalization.supported F)
    (SmallModelGLocalization.supported F') (CategoryTheory.SmallModel.mapAbelianExactFunctor V)
      (preservesSupported F F' V U e)

/-- Original SmallModel boundaries commute with the genuine exact-functor square. -/
theorem connecting_naturality (n : ℕ) :
    ((supportExact F F' V U e).KMap n).comp (SmallModelGLocalization.connectingHom F n) =
      (SmallModelGLocalization.connectingHom F' n).comp (U.smallKMap (n + 1)) := by
  let V' := CategoryTheory.SmallModel.mapAbelianExactFunctor V
  let U' := CategoryTheory.SmallModel.mapAbelianExactFunctor U
  have hn := SerreLocalization.actualConnectingHom_naturality
    (SmallModelGLocalization.supported F) (SmallModelGLocalization.supported F')
    V' (preservesSupported F F' V U e)
    (CategoryTheory.SmallModel.functor F.toFunctor)
    (CategoryTheory.SmallModel.functor F'.toFunctor) U' (ordinarySquare F F' V U e) n
  apply MonoidHom.ext
  intro a
  change (supportExact F F' V U e).KMap n
      (SerreLocalization.actualConnectingHom (SmallModelGLocalization.supported F)
        (CategoryTheory.SmallModel.functor F.toFunctor) n
        (SmallModelLocalization.standardKEquiv D (n + 1) a)) =
    SerreLocalization.actualConnectingHom (SmallModelGLocalization.supported F')
      (CategoryTheory.SmallModel.functor F'.toFunctor) n
      (SmallModelLocalization.standardKEquiv D' (n + 1) (U.smallKMap (n + 1) a))
  have hu := DFunLike.congr_fun (SmallModelLocalization.smallKMap_comparison U (n + 1)) a
  change SmallModelLocalization.standardKEquiv D' (n + 1) (U.smallKMap (n + 1) a) =
    U'.KMap (n + 1) (SmallModelLocalization.standardKEquiv D (n + 1) a) at hu
  exact (DFunLike.congr_fun hn (SmallModelLocalization.standardKEquiv D (n + 1) a)).trans
    (congrArg (SerreLocalization.actualConnectingHom (SmallModelGLocalization.supported F')
      (CategoryTheory.SmallModel.functor F'.toFunctor) n) hu.symm)

end Quillen.SmallModelBoundaryNaturality.Square


namespace Quillen.SmallModelBoundaryNaturality.Universe
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : Type u₁) [Category.{v₁} C] [Abelian C]
  [EssentiallySmall.{w₁} C] [EssentiallySmall.{w₂} C]

/-- The canonical change of SmallModel with the standard abelian exact structures. -/
def standardComparison : ExactFunctor (abelianExactStructure (SmallModel.{w₁} C))
    (abelianExactStructure (SmallModel.{w₂} C)) where
  toFunctor := ((abelianExactStructure C).smallModelUniverseComparison.{w₁,w₂}).toFunctor
  map_conflation S h := by
    have hs : (abelianExactStructure C).smallModel.{w₁}.conflation S := by
      rwa [abelianExactStructure_smallModel]
    have ht := ((abelianExactStructure C).smallModelUniverseComparison.{w₁,w₂}).map_conflation S hs
    exact (congrArg (fun E : ExactStructure (SmallModel.{w₂} C) =>
      E.conflation
        (S.map ((abelianExactStructure C).smallModelUniverseComparison.{w₁,w₂}).toFunctor))
      (abelianExactStructure_smallModel.{w₂} C)).mp ht

instance standardComparison_isEquivalence :
    (standardComparison.{w₁,w₂} C).toFunctor.IsEquivalence :=
  inferInstanceAs
    (((abelianExactStructure C).smallModelUniverseComparison.{w₁,w₂}).toFunctor.IsEquivalence)

/-- The actual model comparison commutes with the original standard K-equivalences. -/
theorem standardComparison_K_square (n : ℕ) :
    ((standardComparison.{w₁,w₂} C).universalKMap n).comp
      (SmallModelLocalization.standardKEquiv.{w₁} C n).toMonoidHom =
    (SmallModelLocalization.standardKEquiv.{w₂} C n).toMonoidHom.comp
      ((abelianExactStructure C).smallKUniverseEquiv.{w₁,w₂} n).toMonoidHom := by
  change ((standardComparison.{w₁,w₂} C).universalKMap n).comp
      ((CategoryTheory.SmallModel.abelianExactComparison.{w₁} C).KMap n) =
    ((CategoryTheory.SmallModel.abelianExactComparison.{w₂} C).KMap n).comp
      (((abelianExactStructure C).smallModelUniverseComparison.{w₁,w₂}).universalKMap n)
  rw [← ExactFunctor.universalKMap_eq_KMap, ← ExactFunctor.universalKMap_eq_KMap,
    ← ExactFunctor.universalKMap_comp, ← ExactFunctor.universalKMap_comp]
  exact ExactFunctor.universalKMap_eq_of_natIso (Iso.refl _) n

variable {C} {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [EssentiallySmall.{w₁} D] [EssentiallySmall.{w₂} D]
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))

/-- The ordinary square obtained from the original chosen-model unit isomorphisms. -/
def ordinarySquare :
    CategoryTheory.SmallModel.functor.{w₁} F.toFunctor ⋙
      (standardComparison.{w₁,w₂} D).toFunctor ≅
    (standardComparison.{w₁,w₂} C).toFunctor ⋙
      CategoryTheory.SmallModel.functor.{w₂} F.toFunctor :=
  (ExactFunctor.smallModelUniverseComparisonNaturalityIso.{w₁,w₂} F).symm

/-- The actual ambient comparison sends kernel objects into the target kernel. -/
theorem preservesSupported (X : SmallModel.{w₁} C)
    (hX : SmallModelGLocalization.supported.{w₁} F X) :
    SmallModelGLocalization.supported.{w₂} F
      ((standardComparison.{w₁,w₂} C).toFunctor.obj X) := by
  have h : IsZero ((standardComparison.{w₁,w₂} D).toFunctor.obj
      ((CategoryTheory.SmallModel.functor.{w₁} F.toFunctor).obj X)) :=
    (standardComparison.{w₁,w₂} D).toFunctor.map_isZero hX
  exact h.of_iso ((ordinarySquare.{w₁,w₂} F).app X).symm

variable
  [PreservesFiniteLimits F.toFunctor] [PreservesFiniteColimits F.toFunctor]
  [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre]

/-- Restrict the actual model comparison to the localization kernels. -/
def supportFunctor : (SmallModelGLocalization.supported.{w₁} F).FullSubcategory ⥤
    (SmallModelGLocalization.supported.{w₂} F).FullSubcategory :=
  (SmallModelGLocalization.supported.{w₂} F).lift
    ((SmallModelGLocalization.supported.{w₁} F).ι ⋙
      (standardComparison.{w₁,w₂} C).toFunctor)
    (fun X => preservesSupported F X.obj X.property)

instance supportFunctor_additive : (supportFunctor.{w₁,w₂} F).Additive := by
  unfold supportFunctor
  infer_instance

/-- The original ambient functor restricted to the actual supported categories. -/
def supportExact : ExactFunctor
    (ObjectProperty.subcategoryExactStructure (SmallModelGLocalization.supported.{w₁} F))
    (ObjectProperty.subcategoryExactStructure (SmallModelGLocalization.supported.{w₂} F)) where
  toFunctor := supportFunctor.{w₁,w₂} F
  map_conflation T hT := by
    have h : ((T.map (supportFunctor.{w₁,w₂} F)).map
        (SmallModelGLocalization.supported.{w₂} F).ι).ShortExact :=
      (standardComparison.{w₁,w₂} C).map_conflation
        (T.map (SmallModelGLocalization.supported.{w₁} F).ι)
        ((ObjectProperty.exactInclusion (SmallModelGLocalization.supported.{w₁} F)).map_conflation
          T hT)
    exact {
      exact := (SmallModelGLocalization.supported.{w₂} F).ι.reflects_exact_of_faithful _ h.exact
      mono_f := (SmallModelGLocalization.supported.{w₂} F).ι.mono_of_mono_map h.mono_f
      epi_g := (SmallModelGLocalization.supported.{w₂} F).ι.epi_of_epi_map h.epi_g }


omit [PreservesFiniteLimits F.toFunctor] [PreservesFiniteColimits F.toFunctor]
  [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre] in
/-- The original model equivalence both preserves and reflects the supported property. -/
theorem supported_iff (X : SmallModel.{w₁} C) :
    SmallModelGLocalization.supported.{w₁} F X ↔
    SmallModelGLocalization.supported.{w₂} F
      ((standardComparison.{w₁,w₂} C).toFunctor.obj X) := by
  constructor
  · exact preservesSupported F X
  · intro hX
    have h : IsZero ((standardComparison.{w₁,w₂} D).toFunctor.obj
        ((CategoryTheory.SmallModel.functor.{w₁} F.toFunctor).obj X)) :=
      hX.of_iso ((ordinarySquare.{w₁,w₂} F).app X)
    exact IsZero.of_full_of_faithful_of_isZero (standardComparison.{w₁,w₂} D).toFunctor _ h

/-- The actual model equivalence restricted to the localization kernels. -/
def supportEquivalence : (SmallModelGLocalization.supported.{w₁} F).FullSubcategory ≌
    (SmallModelGLocalization.supported.{w₂} F).FullSubcategory :=
  (standardComparison.{w₁,w₂} C).toFunctor.asEquivalence.congrFullSubcategory
    (by funext X; exact propext (supported_iff F X).symm)

instance supportFunctor_isEquivalence : (supportFunctor.{w₁,w₂} F).IsEquivalence := by
  change (supportEquivalence.{w₁,w₂} F).functor.IsEquivalence
  infer_instance

/-- The exact support comparison retains the genuine categorical equivalence. -/
instance supportExact_isEquivalence : (supportExact.{w₁,w₂} F).toFunctor.IsEquivalence :=
  inferInstanceAs (supportFunctor.{w₁,w₂} F).IsEquivalence

/-- The same support comparison reflects both standard abelian admissibility classes. -/
instance supportExact_mapQ_isEquivalence : (supportExact.{w₁,w₂} F).mapQ.IsEquivalence := by
  apply ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N f hf
    exact (abelianExactStructure_inflation_iff _ _).2
      ((supportExact.{w₁,w₂} F).toFunctor.mono_of_mono_map
        ((abelianExactStructure_inflation_iff _ _).1 hf))
  · intro M N f hf
    exact (abelianExactStructure_deflation_iff _ _).2
      ((supportExact.{w₁,w₂} F).toFunctor.epi_of_epi_map
        ((abelianExactStructure_deflation_iff _ _).1 hf))

end Quillen.SmallModelBoundaryNaturality.Universe


namespace Quillen.SmallModelBoundaryNaturality.Universe
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{max w v} C]
  [EssentiallySmall.{w} D] [EssentiallySmall.{max w v} D]
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))
  [PreservesFiniteLimits F.toFunctor] [PreservesFiniteColimits F.toFunctor]
  [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre]

/-- The original lower and upper SmallModel boundaries commute in every degree. -/
theorem connectingHom_universe (n : ℕ) :
    ((supportExact.{w,max w v} F).universalKMap n).comp
      (SmallModelGLocalization.connectingHom.{w} F n) =
    (SmallModelGLocalization.connectingHom.{max w v} F n).comp
      ((abelianExactStructure D).smallKUniverseEquiv.{w,max w v} (n+1)).toMonoidHom := by
  have hn := Quillen.SmallModelBoundaryNaturality.Upward.actualConnectingHom_naturality
    (SmallModelGLocalization.supported.{w} F) (SmallModelGLocalization.supported.{max w v} F)
    (standardComparison.{w,max w v} C) (preservesSupported.{w,max w v} F)
    (CategoryTheory.SmallModel.functor.{w} F.toFunctor)
    (CategoryTheory.SmallModel.functor.{max w v} F.toFunctor)
    (standardComparison.{w,max w v} D) (ordinarySquare.{w,max w v} F) n
  apply MonoidHom.ext
  intro a
  change (supportExact.{w,max w v} F).universalKMap n
      (SerreLocalization.actualConnectingHom (SmallModelGLocalization.supported.{w} F)
        (CategoryTheory.SmallModel.functor.{w} F.toFunctor) n
        (SmallModelLocalization.standardKEquiv.{w} D (n+1) a)) =
    SerreLocalization.actualConnectingHom (SmallModelGLocalization.supported.{max w v} F)
      (CategoryTheory.SmallModel.functor.{max w v} F.toFunctor) n
      (SmallModelLocalization.standardKEquiv.{max w v} D (n+1)
        ((abelianExactStructure D).smallKUniverseEquiv.{w,max w v} (n+1) a))
  exact (DFunLike.congr_fun hn (SmallModelLocalization.standardKEquiv.{w} D (n+1) a)).trans
    (congrArg (SerreLocalization.actualConnectingHom
      (SmallModelGLocalization.supported.{max w v} F)
      (CategoryTheory.SmallModel.functor.{max w v} F.toFunctor) n)
        (DFunLike.congr_fun (standardComparison_K_square.{w,max w v} D (n+1)) a))
end Quillen.SmallModelBoundaryNaturality.Universe
