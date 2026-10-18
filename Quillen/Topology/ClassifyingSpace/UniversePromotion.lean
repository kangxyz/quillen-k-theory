/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.UniverseLift
public import Quillen.Topology.Realization.HomotopyBridge
public import Quillen.Topology.ClassifyingSpace.UniverseMap
public import Quillen.CategoryTheory.TheoremB.Naturality
public import Quillen.CategoryTheory.TheoremB.NaturalTransformationFiberLift
public import Quillen.Topology.HomotopyFiber.Map
public import Quillen.Aglib.CategoryTheory.Comma.UniverseLift

/-!
# Whole natural-transformation cylinders across universe promotion

Lifting a small category into a larger common universe preserves the entire
original realized natural-transformation homotopy, including its interval
parameter. The proof compares the two projections of the actual cylinder
isomorphism on original simplices, then retains the categorical cylinder.

The current consumer is the original SmallModel localization boundary:
its canonical zero-nullhomotopy must survive the lower-to-upper Q-row lift.
No boundary comparison or equality inferred only from vertices is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Convexity
open scoped Simplicial Topology unitInterval
namespace Quillen.UniversePromotion

/-- Lift a simplicial cylinder without changing its original interval simplex. -/
private def cylinderUniverseMap {X : SSet.{u}} {Y : SSet.{v}} (f : SimplicialUniverseMap X Y) :
    SimplicialUniverseMap (X ⊗ (Δ[1] : SSet.{u})) (Y ⊗ (Δ[1] : SSet.{v})) where
  app n z := (f.app n z.1, ULift.up z.2.down)
  naturality a z := Prod.ext (f.naturality a z.1) rfl

/-- Ordinary realization retains the original characteristic map of each simplex. -/
private theorem realizationMap_simplex {X Y : SSet.{u}} (f : X ⟶ Y) (n : SimplexCategory)
    (x : X.obj (op n)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    SSet.toTop.map f (realizationSimplex x t) = realizationSimplex (f.app (op n) x) t := by
  have h := realizationUniverseMap_simplex (SimplicialUniverseMap.ofHom f) n x t
  rw [realizationUniverseMap_ofHom] at h
  exact h

/-- The original realized interval coordinate is independent of its ambient universe. -/
private theorem intervalCoordinate_simplex (n : SimplexCategory)
    (a : (Δ[1] : SSet.{u}).obj (op n)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    (SSet.stdSimplex.toTopObjIsoI.hom (realizationSimplex a t)).down =
      StdSimplex.homeomorphI (StdSimplex.map a.down.toOrderHom t) := by
  have ha : SSet.yonedaEquiv.symm a = SSet.stdSimplex.map a.down := by
    ext m b
    rfl
  change (SSet.stdSimplex.toTopObjIsoI.hom
    (SSet.toTop.map (SSet.yonedaEquiv.symm a) ((SimplexCategory.toTopHomeo n).symm t))).down = _
  rw [ha]
  change StdSimplex.homeomorphI (SimplexCategory.toTopHomeo ⦋1⦌
    (SSet.toTop.map (SSet.stdSimplex.map a.down) ((SimplexCategory.toTopHomeo n).symm t))) = _
  rw [SimplexCategory.toTopHomeo_naturality_apply, Homeomorph.apply_symm_apply]
  rfl

/-- The actual cylinder comparison preserves both original product coordinates across
universes. -/
private theorem cylinderComparison_universe {X : SSet.{u}} {Y : SSet.{v}}
    (f : SimplicialUniverseMap X Y) (z : |X ⊗ (Δ[1] : SSet.{u})|) :
    (realizationCylinderIso Y).hom (realizationUniverseMap (cylinderUniverseMap f) z) =
      (realizationUniverseMap f ((realizationCylinderIso X).hom z).1,
        ULift.up (((realizationCylinderIso X).hom z).2.down)) := by
  have h : (fun z : |X ⊗ (Δ[1] : SSet.{u})| =>
      (realizationCylinderIso Y).hom (realizationUniverseMap (cylinderUniverseMap f) z)) =
    (fun z : |X ⊗ (Δ[1] : SSet.{u})| =>
      (realizationUniverseMap f ((realizationCylinderIso X).hom z).1,
        ULift.up (((realizationCylinderIso X).hom z).2.down))) := by
    apply realization_ext
    intro n x t
    rw [realizationUniverseMap_simplex]
    apply Prod.ext
    · change SSet.toTop.map (fst Y Δ[1])
        (realizationSimplex ((cylinderUniverseMap f).app (op n) x) t) =
      realizationUniverseMap f (SSet.toTop.map (fst X Δ[1]) (realizationSimplex x t))
      rw [realizationMap_simplex, realizationMap_simplex, realizationUniverseMap_simplex]
      rfl
    · apply ULift.ext
      change (SSet.stdSimplex.toTopObjIsoI.hom
        (SSet.toTop.map (snd Y Δ[1])
          (realizationSimplex ((cylinderUniverseMap f).app (op n) x) t))).down =
        (SSet.stdSimplex.toTopObjIsoI.hom
          (SSet.toTop.map (snd X Δ[1]) (realizationSimplex x t))).down
      rw [realizationMap_simplex, realizationMap_simplex,
        intervalCoordinate_simplex, intervalCoordinate_simplex]
      rfl
  exact congrFun h z


/-- The inverse cylinder comparison retains the whole original interval parameter across
universes. -/
private theorem cylinderInverse_universe {X : SSet.{u}} {Y : SSet.{v}}
    (f : SimplicialUniverseMap X Y) (x : |X|) (t : unitInterval) :
    realizationUniverseMap (cylinderUniverseMap f)
      ((realizationCylinderIso X).inv (x, ULift.up t)) =
      (realizationCylinderIso Y).inv (realizationUniverseMap f x, ULift.up t) := by
  apply (TopCat.homeoOfIso (realizationCylinderIso Y)).injective
  change (realizationCylinderIso Y).hom
      (realizationUniverseMap (cylinderUniverseMap f)
        ((realizationCylinderIso X).inv (x, ULift.up t))) =
    (realizationCylinderIso Y).hom
      ((realizationCylinderIso Y).inv (realizationUniverseMap f x, ULift.up t))
  have hx := ConcreteCategory.congr_hom (realizationCylinderIso X).inv_hom_id (x, ULift.up t)
  have hy := ConcreteCategory.congr_hom (realizationCylinderIso Y).inv_hom_id
    (realizationUniverseMap f x, ULift.up t)
  change (realizationCylinderIso X).hom ((realizationCylinderIso X).inv (x, ULift.up t)) =
    (x, ULift.up t) at hx
  change (realizationCylinderIso Y).hom
      ((realizationCylinderIso Y).inv (realizationUniverseMap f x, ULift.up t)) =
    (realizationUniverseMap f x, ULift.up t) at hy
  rw [cylinderComparison_universe, hx, hy]

end Quillen.UniversePromotion

namespace Quillen.UniversePromotion
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- The original natural transformation with both categorical universes lifted. -/
def liftTransformation {F G : C ⥤ D} (α : F ⟶ G) :
    universeLiftFunctor.{u,u,u,u,max u v} F ⟶ universeLiftFunctor.{u,u,u,u,max u v} G :=
  Functor.whiskerLeft AsSmall.down (Functor.whiskerRight α AsSmall.up)

/-- The actual categorical cylinder commutes with the displayed universe lift. -/
private theorem liftedCylinderFunctorSquare {F G : C ⥤ D} (α : F ⟶ G) :
    ((𝟭 (Fin 2)).prod (AsSmall.up : C ⥤ AsSmall.{max u v} C)) ⋙
      naturalTransformationCylinderFunctor (liftTransformation.{u,v} α) =
    naturalTransformationCylinderFunctor α ⋙ (AsSmall.up : D ⥤ AsSmall.{max u v} D) := by
  apply Functor.curry_obj_injective
  refine ComposableArrows.ext₁ rfl rfl ?_
  ext a
  apply ULift.ext
  simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
    Functor.uncurry, ComposableArrows.mk₁, ComposableArrows.hom,
    liftTransformation, universeLiftFunctor, AsSmall.down, AsSmall.up, down_comp]

/-- The complete realized nerve cylinder commutes with the original universe maps. -/
private theorem naturalCylinder_lift_map {F G : C ⥤ D} (α : F ⟶ G) :
    (classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v} D)).comp
      (SSet.toTop.map (naturalTransformationNerveCylinder α)).hom =
    (SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v} α))).hom.comp
      (realizationUniverseMap (cylinderUniverseMap
        (nerveUniverseMap (AsSmall.up : C ⥤ AsSmall.{max u v} C)))) := by
  apply DFunLike.coe_injective
  apply realization_ext
  intro n z t
  change realizationUniverseMap (nerveUniverseMap (AsSmall.up : D ⥤ AsSmall.{max u v} D))
      (SSet.toTop.map (naturalTransformationNerveCylinder α) (realizationSimplex z t)) =
    SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v} α))
      (realizationUniverseMap (cylinderUniverseMap
        (nerveUniverseMap (AsSmall.up : C ⥤ AsSmall.{max u v} C))) (realizationSimplex z t))
  rw [realizationMap_simplex, realizationUniverseMap_simplex,
    realizationUniverseMap_simplex, realizationMap_simplex]
  apply congrArg (fun b => realizationSimplex b t)
  change (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
      (naturalTransformationCylinderFunctor α ⋙ AsSmall.up) =
    (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
      (((𝟭 (Fin 2)).prod (AsSmall.up : C ⥤ AsSmall.{max u v} C)) ⋙
        naturalTransformationCylinderFunctor (liftTransformation.{u,v} α))
  rw [liftedCylinderFunctorSquare]

/-- Lifting preserves every point of the original natural-transformation homotopy and its
interval parameter. -/
theorem naturalTransformationHomotopy_up {F G : C ⥤ D} (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy (liftTransformation.{u,v} α)
      (t,classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v} C) x) =
    classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v} D)
      (classifyingSpaceNaturalTransformationHomotopy α (t,x)) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v} α))
      ((realizationCylinderIso (nerve (AsSmall.{max u v} C))).inv
        (realizationUniverseMap (nerveUniverseMap (AsSmall.up : C ⥤ AsSmall.{max u v} C)) x,
          ULift.up t)) =
    classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v} D)
      (SSet.toTop.map (naturalTransformationNerveCylinder α)
        ((realizationCylinderIso (nerve C)).inv (x,ULift.up t)))
  rw [← cylinderInverse_universe]
  exact (ContinuousMap.congr_fun (naturalCylinder_lift_map.{u,v} α)
    ((realizationCylinderIso (nerve C)).inv (x,ULift.up t))).symm

end Quillen.UniversePromotion


namespace Quillen.UniversePromotion
variable {A C D : Type u} [SmallCategory A] [SmallCategory C] [SmallCategory D]

/-- The original row map commutes strictly with the actual universe maps. -/
theorem liftedRowSquare (F : C ⥤ D) :
    (classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v} D)).comp
      (classifyingSpaceMap F).hom =
    (classifyingSpaceMap (universeLiftFunctor.{u,u,u,u,max u v} F)).hom.comp
      (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v} C)) := by
  rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_eq,
    ← classifyingSpaceMapUniversal_comp, ← classifyingSpaceMapUniversal_comp]
  rfl

/-- Promote a row fiber by the actual universe maps on its source and stored path. -/
def rowFiberUp (F : C ⥤ D) (d : D) :
    C(HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d),
      HomotopyFiber (classifyingSpaceMap (universeLiftFunctor.{u,u,u,u,max u v} F)).hom
        (classifyingSpacePoint (AsSmall.up.obj d))) where
  toFun z := ⟨(classifyingSpaceMapUniversal AsSmall.up z.val.1,
    (classifyingSpaceMapUniversal AsSmall.up).comp z.val.2),
    (congrArg (classifyingSpaceMapUniversal AsSmall.up) z.property.1).trans
      (ContinuousMap.congr_fun (liftedRowSquare.{u,v} F) z.val.1),
    (congrArg (classifyingSpaceMapUniversal AsSmall.up) z.property.2).trans
      (classifyingSpaceMapUniversal_point AsSmall.up d)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact (ContinuousMap.continuous_postcomp (classifyingSpaceMapUniversal AsSmall.up)).comp
        (continuous_snd.comp continuous_subtype_val)

/-- The original null transformation on the promoted categorical row. -/
def liftNullTransformation (P : A ⥤ C) (F : C ⥤ D) (d : D)
    (ε : P ⋙ F ⟶ (Functor.const A).obj d) :
    universeLiftFunctor.{u,u,u,u,max u v} P ⋙ universeLiftFunctor.{u,u,u,u,max u v} F ⟶
      (Functor.const (AsSmall.{max u v} A)).obj (AsSmall.up.obj d) :=
  liftTransformation.{u,v} ε

/-- The complete natural-transformation fiber lift commutes with universe promotion. -/
theorem rowFiberUp_naturalLift (P : A ⥤ C) (F : C ⥤ D) (d : D)
    (ε : P ⋙ F ⟶ (Functor.const A).obj d) :
    (rowFiberUp.{u,v} F d).comp (TheoremB.naturalTransformationFiberLift P F d ε) =
    (TheoremB.naturalTransformationFiberLift (universeLiftFunctor.{u,u,u,u,max u v} P)
      (universeLiftFunctor.{u,u,u,u,max u v} F)
      (AsSmall.up.obj d) (liftNullTransformation.{u,v} P F d ε)).comp
        (classifyingSpaceMapUniversal (AsSmall.up : A ⥤ AsSmall.{max u v} A)) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · exact ContinuousMap.congr_fun (liftedRowSquare.{u,v} P) z
  · apply ContinuousMap.ext
    intro t
    exact (naturalTransformationHomotopy_up.{u,v} ε t z).symm

end Quillen.UniversePromotion
