/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.TheoremB.Comparison
public import Quillen.Topology.HomotopyFiber.Map

/-!
# Naturality of the actual comma-to-fiber comparison

These identities identify the continuous maps and their path coordinates,
rather than only comparing abstract homotopy types.
-/
@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial Topology unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

namespace Quillen

/-- The categorical nerve-cylinder construction commutes with precomposition. -/
theorem naturalTransformationNerveCylinder_whiskerLeft
    {A C D : Type u} [SmallCategory A] [SmallCategory C] [SmallCategory D]
    (K : A ⥤ C) {F G : C ⥤ D} (α : F ⟶ G) :
    naturalTransformationNerveCylinder (Functor.whiskerLeft K α) =
      nerveMap K ▷ Δ[1] ≫ naturalTransformationNerveCylinder α := by
  have hc : naturalTransformationCylinderFunctor (Functor.whiskerLeft K α) =
      (𝟭 (Fin 2)).prod K ⋙ naturalTransformationCylinderFunctor α := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ rfl rfl ?_
    ext a
    simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
      ComposableArrows.mk₁, ComposableArrows.hom]
  ext n z
  change _ ⋙ naturalTransformationCylinderFunctor (Functor.whiskerLeft K α) =
    _ ⋙ naturalTransformationCylinderFunctor α
  rw [hc]
  rfl

/-- The categorical nerve-cylinder construction commutes with postcomposition. -/
theorem naturalTransformationNerveCylinder_whiskerRight
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    {F G : C ⥤ D} (α : F ⟶ G) (K : D ⥤ E) :
    naturalTransformationNerveCylinder (Functor.whiskerRight α K) =
      naturalTransformationNerveCylinder α ≫ nerveMap K := by
  have hc : naturalTransformationCylinderFunctor (Functor.whiskerRight α K) =
      naturalTransformationCylinderFunctor α ⋙ K := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ ?_ ?_ ?_
    · refine CategoryTheory.Functor.ext (fun a ↦ rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁]
    · refine CategoryTheory.Functor.ext (fun a ↦ rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁]
    · ext a
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁, ComposableArrows.hom]
  ext n z
  change _ ⋙ naturalTransformationCylinderFunctor (Functor.whiskerRight α K) =
    (_ ⋙ naturalTransformationCylinderFunctor α) ⋙ K
  rw [hc]
  rfl

/-- Precomposing a natural transformation precomposes its actual realized homotopy. -/
theorem classifyingSpaceNaturalTransformationHomotopy_whiskerLeft
    {A C D : Type u} [SmallCategory A] [SmallCategory C] [SmallCategory D]
    (K : A ⥤ C) {F G : C ⥤ D} (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerLeft K α) (t, x) =
      classifyingSpaceNaturalTransformationHomotopy α (t, classifyingSpaceMap K x) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (Functor.whiskerLeft K α))
    ((realizationCylinderIso (nerve A)).inv (x, ULift.up t)) = _
  rw [naturalTransformationNerveCylinder_whiskerLeft, Functor.map_comp, TopCat.comp_app]
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (nerveMap K)) (x, ULift.up t)
  exact congrArg (SSet.toTop.map (naturalTransformationNerveCylinder α)) hn

/-- Postcomposing a natural transformation postcomposes its actual realized homotopy. -/
theorem classifyingSpaceNaturalTransformationHomotopy_whiskerRight
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    {F G : C ⥤ D} (α : F ⟶ G) (K : D ⥤ E)
    (t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerRight α K) (t, x) =
      classifyingSpaceMap K (classifyingSpaceNaturalTransformationHomotopy α (t, x)) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (Functor.whiskerRight α K))
    ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)) = _
  rw [naturalTransformationNerveCylinder_whiskerRight, Functor.map_comp, TopCat.comp_app]
  rfl

/-- The realized natural-transformation homotopy traverses its component edge
at every object vertex. -/
theorem classifyingSpaceNaturalTransformationHomotopy_vertex
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) (t : unitInterval) :
    classifyingSpaceNaturalTransformationHomotopy α (t, classifyingSpacePoint c) =
      classifyingSpacePath (α.app c) t := by
  let q := (realizationCylinderIso (Δ[0] : SSet.{u})).inv (default, ULift.up t)
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (nerveVertexMap c)) (default, ULift.up t)
  change SSet.toTop.map (nerveVertexMap c ▷ Δ[1]) q =
    (realizationCylinderIso (nerve C)).inv (classifyingSpacePoint c, ULift.up t) at hn
  change SSet.toTop.map (naturalTransformationNerveCylinder α)
    ((realizationCylinderIso (nerve C)).inv (classifyingSpacePoint c, ULift.up t)) = _
  rw [← hn]
  change (SSet.toTop.map (nerveVertexMap c ▷ Δ[1]) ≫
    SSet.toTop.map (naturalTransformationNerveCylinder α)) q = _
  rw [← Functor.map_comp, naturalTransformationNerveCylinder_vertex, Functor.map_comp,
    TopCat.comp_app]
  have hs : SSet.toTop.map (snd (Δ[0] : SSet.{u}) Δ[1]) q = realizationInterval t := by
    have hh := congrArg Prod.snd (ConcreteCategory.congr_hom
      (realizationCylinderIso (Δ[0] : SSet.{u})).inv_hom_id (default, ULift.up t))
    change SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (snd (Δ[0] : SSet.{u}) Δ[1]) q) = ULift.up t at hh
    apply (TopCat.homeoOfIso SSet.stdSimplex.toTopObjIsoI).injective
    exact hh.trans (ConcreteCategory.congr_hom SSet.stdSimplex.toTopObjIsoI.inv_hom_id _).symm
  rw [hs]
  rfl

namespace TheoremB

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- On a comma vertex the nullhomotopy is the realized structure arrow. -/
@[simp]
theorem commaNullhomotopy_vertex (d : D) (X : CostructuredArrow F d) (t : unitInterval) :
    commaNullhomotopy F d (t, classifyingSpacePoint X) = classifyingSpacePath X.hom t :=
  classifyingSpaceNaturalTransformationHomotopy_vertex (commaTransformation F d) X t

section Postcomposition

variable {E : Type u} [SmallCategory E] (K : D ⥤ E)

/-- Applying a functor to the target gives the corresponding map of actual
homotopy fibers, including the required vertex endpoint equality. -/
def postFiberMap (d : D) :
    C(HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d),
      HomotopyFiber (classifyingSpaceMap (F ⋙ K)).hom (classifyingSpacePoint (K.obj d))) where
  toFun z := ⟨(z.1.1, (classifyingSpaceMap K).hom.comp z.1.2),
    (congrArg (classifyingSpaceMap K) z.2.1).trans (by
      rw [classifyingSpaceMap_comp]
      rfl),
    (congrArg (classifyingSpaceMap K) z.2.2).trans (classifyingSpaceMap_point K d)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact (ContinuousMap.continuous_postcomp (classifyingSpaceMap K).hom).comp (by fun_prop)

/-- Target functors commute with the actual nullhomotopies supplied by comma arrows. -/
theorem commaNullhomotopy_post (d : D) (t : unitInterval)
    (x : ClassifyingSpace (CostructuredArrow F d)) :
    commaNullhomotopy (F ⋙ K) (K.obj d)
      (t, classifyingSpaceMap (CostructuredArrow.post F K d) x) =
      classifyingSpaceMap K (commaNullhomotopy F d (t, x)) := by
  change classifyingSpaceNaturalTransformationHomotopy
    (commaTransformation (F ⋙ K) (K.obj d))
    (t, classifyingSpaceMap (CostructuredArrow.post F K d) x) =
    classifyingSpaceMap K
      (classifyingSpaceNaturalTransformationHomotopy (commaTransformation F d) (t, x))
  rw [← classifyingSpaceNaturalTransformationHomotopy_whiskerLeft,
    ← classifyingSpaceNaturalTransformationHomotopy_whiskerRight]
  have hc : naturalTransformationCylinderFunctor
      (Functor.whiskerLeft (CostructuredArrow.post F K d)
        (commaTransformation (F ⋙ K) (K.obj d))) =
      naturalTransformationCylinderFunctor
        (Functor.whiskerRight (commaTransformation F d) K) := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ rfl ?_ ?_
    · refine CategoryTheory.Functor.ext (fun a ↦ rfl) ?_
      intro a b f
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
        Functor.uncurry, ComposableArrows.mk₁]
    · ext a
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
        Functor.uncurry, ComposableArrows.mk₁, ComposableArrows.hom, commaTransformation,
          CostructuredArrow.post]
  have hn : naturalTransformationNerveCylinder
      (Functor.whiskerLeft (CostructuredArrow.post F K d)
        (commaTransformation (F ⋙ K) (K.obj d))) =
      naturalTransformationNerveCylinder
        (Functor.whiskerRight (commaTransformation F d) K) := by
    ext n z
    change _ ⋙ naturalTransformationCylinderFunctor _ =
      _ ⋙ naturalTransformationCylinderFunctor _
    rw [hc]
  change SSet.toTop.map (naturalTransformationNerveCylinder
    (Functor.whiskerLeft (CostructuredArrow.post F K d)
      (commaTransformation (F ⋙ K) (K.obj d)))) _ =
    SSet.toTop.map (naturalTransformationNerveCylinder
      (Functor.whiskerRight (commaTransformation F d) K)) _
  rw [hn]

/-- The canonical comma-to-fiber map commutes strictly with postcomposition,
including its path coordinate. -/
theorem fiberComparison_post (d : D) :
    (fiberComparison (F ⋙ K) (K.obj d)).comp
      (classifyingSpaceMap (CostructuredArrow.post F K d)).hom =
      (postFiberMap F K d).comp (fiberComparison F d) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · change classifyingSpaceMap (CostructuredArrow.proj (F ⋙ K) (K.obj d))
      (classifyingSpaceMap (CostructuredArrow.post F K d) x) =
        classifyingSpaceMap (CostructuredArrow.proj F d) x
    change (classifyingSpaceMap (CostructuredArrow.post F K d) ≫
      classifyingSpaceMap (CostructuredArrow.proj (F ⋙ K) (K.obj d))) x = _
    rw [← classifyingSpaceMap_comp]
    rfl
  · apply ContinuousMap.ext
    intro t
    exact commaNullhomotopy_post F K d t x

end Postcomposition

end TheoremB
end Quillen
