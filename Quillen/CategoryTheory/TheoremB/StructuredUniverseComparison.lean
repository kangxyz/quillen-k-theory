/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.TheoremB.StructuredFullWeakComparison
public import Quillen.CategoryTheory.Comma.StructuredUniverseLift
public import Quillen.Topology.ClassifyingSpace.UniverseHomotopyTracks

/-!
# The original structured Theorem B comparison in arbitrary universes

The comparison is the lift of the original structured projection using the
reversed realization of its original structure-arrow transformation. Its full
weak-equivalence theorem allows independent object and morphism universes and
arbitrary target objects, including empty comma categories. Strict universe
lifting identifies this prescribed map with the common-universe comparison;
no abstract comparison map or unspecified basepoint path is substituted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u₁ v₁ u₂ v₂
namespace Quillen

attribute [simp] classifyingSpaceUniversalHomotopy_vertex_track

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A constant functor realizes to the constant map, in independent universes. -/
@[simp] theorem classifyingSpaceMapUniversal_const (d : D) :
    classifyingSpaceMapUniversal ((Functor.const C).obj d) =
      ContinuousMap.const (ClassifyingSpace C) (classifyingSpacePoint d) := by
  let U : C ⥤ AsSmall.{max u₁ v₁ u₂ v₂} C := AsSmall.up
  let V : AsSmall.{max u₁ v₁ u₂ v₂} D ⥤ D := AsSmall.down
  let K : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D :=
    (Functor.const _).obj (AsSmall.up.obj d)
  have h : (U ⋙ K) ⋙ V = (Functor.const C).obj d := rfl
  rw [← h, classifyingSpaceMapUniversal_comp, classifyingSpaceMapUniversal_comp,
    classifyingSpaceMapUniversal_eq K]
  ext x
  change classifyingSpaceMapUniversal V (classifyingSpaceMap K
    (classifyingSpaceMapUniversal U x)) = classifyingSpacePoint d
  rw [show classifyingSpaceMap K = TopCat.const (classifyingSpacePoint (AsSmall.up.obj d))
    from classifyingSpaceMap_const_direct _]
  exact classifyingSpaceMapUniversal_point V _

/-- In common small universes, the universal homotopy is the original homotopy
at every point and every interval parameter. -/
theorem classifyingSpaceUniversalHomotopy_eq {A B : Type u₁}
    [SmallCategory A] [SmallCategory B] {F G : A ⥤ B} (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceUniversalHomotopy α (t, x) =
      classifyingSpaceNaturalTransformationHomotopy α (t, x) := by
  let U : A ⥤ AsSmall.{u₁} A := AsSmall.up
  let V : AsSmall.{u₁} B ⥤ B := AsSmall.down
  change classifyingSpaceMapUniversal V
    (classifyingSpaceNaturalTransformationHomotopy
      (Functor.whiskerLeft AsSmall.down (Functor.whiskerRight α AsSmall.up))
      (t, classifyingSpaceMapUniversal U x)) = _
  rw [classifyingSpaceNaturalTransformationHomotopy_whiskerLeft,
    classifyingSpaceNaturalTransformationHomotopy_whiskerRight]
  have hx : classifyingSpaceMap (AsSmall.down : AsSmall.{u₁} A ⥤ A)
      (classifyingSpaceMapUniversal U x) = x := by
    change (classifyingSpaceMap (AsSmall.down : AsSmall.{u₁} A ⥤ A)).hom
      (classifyingSpaceMapUniversal U x) = x
    rw [← classifyingSpaceMapUniversal_eq]
    change ((classifyingSpaceMapUniversal AsSmall.down).comp
      (classifyingSpaceMapUniversal U)) x = x
    rw [← classifyingSpaceMapUniversal_comp]
    change classifyingSpaceMapUniversal (𝟭 A) x = x
    rw [classifyingSpaceMapUniversal_id]
    rfl
  rw [hx]
  change ((classifyingSpaceMapUniversal V).comp
    (classifyingSpaceMap (AsSmall.up : B ⥤ AsSmall.{u₁} B)).hom) _ = _
  rw [← classifyingSpaceMapUniversal_eq (AsSmall.up : B ⥤ AsSmall.{u₁} B)]
  rw [← classifyingSpaceMapUniversal_comp]
  change classifyingSpaceMapUniversal (𝟭 B) _ = _
  rw [classifyingSpaceMapUniversal_id]
  rfl

namespace TheoremB
variable (F : C ⥤ D)

/-- The original component arrows in the structured comma, without universe restrictions. -/
@[simps] def structuredCommaTransformationUniversal (d : D) :
    (Functor.const (StructuredArrow d F)).obj d ⟶ StructuredArrow.proj d F ⋙ F where
  app X := X.hom
  naturality X Y f := by simp

/-- Reverse the actual realized structure arrows to obtain paths from `F(x)` to `d`. -/
def structuredCommaNullhomotopyUniversal (d : D) :
    ((classifyingSpaceMapUniversal F).comp
      (classifyingSpaceMapUniversal (StructuredArrow.proj d F))).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint d)) :=
  (classifyingSpaceUniversalHomotopy (structuredCommaTransformationUniversal F d)).symm.cast
    (classifyingSpaceMapUniversal_comp _ _) (classifyingSpaceMapUniversal_const _)

/-- The original structured projection, lifted by its reversed structure-arrow homotopy. -/
def structuredFiberComparisonUniversal (d : D) :
    C(ClassifyingSpace (StructuredArrow d F),
      HomotopyFiber (classifyingSpaceMapUniversal F) (classifyingSpacePoint d)) :=
  HomotopyFiber.lift _ _ (classifyingSpaceMapUniversal (StructuredArrow.proj d F))
    (structuredCommaNullhomotopyUniversal F d)

@[simp] theorem structuredFiberComparisonUniversal_projection (d : D) :
    (HomotopyFiber.projection (classifyingSpaceMapUniversal F) (classifyingSpacePoint d)).comp
      (structuredFiberComparisonUniversal F d) =
        classifyingSpaceMapUniversal (StructuredArrow.proj d F) :=
  HomotopyFiber.projection_lift _ _ _ _

/-- The full path coordinate remains the reversed original structure-arrow homotopy. -/
@[simp] theorem structuredFiberComparisonUniversal_path (d : D)
    (x : ClassifyingSpace (StructuredArrow d F)) (t : unitInterval) :
    (structuredFiberComparisonUniversal F d x).1.2 t =
      classifyingSpaceUniversalHomotopy (structuredCommaTransformationUniversal F d)
        (unitInterval.symm t, x) := rfl

/-- At every object vertex, the comparison retains the exact reversed original arrow path. -/
theorem structuredFiberComparisonUniversal_vertex_path (d : D)
    (X : StructuredArrow d F) (t : unitInterval) :
    (structuredFiberComparisonUniversal F d (classifyingSpacePoint X)).1.2 t =
      classifyingSpacePath X.hom (unitInterval.symm t) := by
  rw [structuredFiberComparisonUniversal_path, classifyingSpaceUniversalHomotopy_vertex_track]
  rfl

/-- An identity structured arrow gives the exact constant-path basepoint. -/
@[simp] theorem structuredFiberComparisonUniversal_identity (c : C) :
    structuredFiberComparisonUniversal F (F.obj c)
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) =
      HomotopyFiber.basepoint (classifyingSpaceMapUniversal F) (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMapUniversal_point F c) := by
  apply Subtype.ext
  apply Prod.ext
  · exact classifyingSpaceMapUniversal_point (StructuredArrow.proj (F.obj c) F) _
  · apply ContinuousMap.ext
    intro t
    rw [structuredFiberComparisonUniversal_vertex_path]
    exact congrArg (fun p : Path (classifyingSpacePoint (F.obj c))
      (classifyingSpacePoint (F.obj c)) ↦ p (unitInterval.symm t))
        (classifyingSpacePath_id (F.obj c))

/-- In common small universes, both coordinates are exactly those of the existing
structured comparison, rather than merely homotopic choices of paths. -/
theorem structuredFiberComparisonUniversal_val_eq {A B : Type u₁}
    [SmallCategory A] [SmallCategory B] (G : A ⥤ B) (d : B)
    (x : ClassifyingSpace (StructuredArrow d G)) :
    (structuredFiberComparisonUniversal G d x).val = (structuredFiberComparison G d x).val := by
  apply Prod.ext
  · exact ContinuousMap.congr_fun (classifyingSpaceMapUniversal_eq (StructuredArrow.proj d G)) x
  · apply ContinuousMap.ext
    intro t
    change classifyingSpaceUniversalHomotopy (structuredCommaTransformationUniversal G d)
      (unitInterval.symm t, x) = _
    rw [classifyingSpaceUniversalHomotopy_eq]
    rfl

/-- Every original structured transition is a weak equivalence in its original universes. -/
def StructuredTransitionWeakEquivalencesUniversal : Prop :=
  ∀ ⦃d e : D⦄ (f : d ⟶ e), IsWeakHomotopyEquivalence
    (classifyingSpaceMapUniversal (StructuredArrow.map (T := F) f))

/-- Original structured transitions pass to their common-universe lift. -/
theorem structuredTransitionWeakEquivalences_universeLift
    (h : StructuredTransitionWeakEquivalencesUniversal F) :
    StructuredTransitionWeakEquivalences
      (universeLiftFunctor.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F) := by
  intro d e f
  have hu := isWeakHomotopyEquivalence_of_homotopyEquiv
    (structuredArrowUniverseHomeomorph.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂}
      F (ULift.down e)).toHomotopyEquiv
  have hv := isWeakHomotopyEquivalence_of_homotopyEquiv
    (structuredArrowUniverseHomeomorph.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂}
      F (ULift.down d)).toHomotopyEquiv
  have ht := hv.comp (h (ULift.down f))
  change IsWeakHomotopyEquivalence
    ((classifyingSpaceMapUniversal (structuredArrowUniverseUp F (ULift.down d))).comp
      (classifyingSpaceMapUniversal (StructuredArrow.map (ULift.down f)))) at ht
  rw [← classifyingSpaceMapUniversal_comp, ← structuredArrowUniverseUp_map,
    classifyingSpaceMapUniversal_comp] at ht
  have he := ht.of_comp_left hu
  change IsWeakHomotopyEquivalence (classifyingSpaceMap (StructuredArrow.map f)).hom
  simpa only [classifyingSpaceMapUniversal_eq, AsSmall.up, ULift.up_down] using he

/-- Universe lifting gives the actual homeomorphism of the original path-space fibers. -/
def structuredComparisonUniverseFiberHomeomorph (d : D) :
    HomotopyFiber (classifyingSpaceMapUniversal F) (classifyingSpacePoint d) ≃ₜ
      HomotopyFiber
        (classifyingSpaceMap (universeLiftFunctor.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F)).hom
        (classifyingSpacePoint (AsSmall.up.obj d)) :=
  (HomotopyFiber.homeomorphOfSquare (classifyingSpaceMapUniversal F)
    (classifyingSpaceMap (universeLiftFunctor.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F)).hom
    (classifyingSpaceUniverseHomeomorph.{u₁, v₁, max u₁ v₁ u₂ v₂} C)
    (classifyingSpaceUniverseHomeomorph.{u₂, v₂, max u₁ v₁ u₂ v₂} D)
    (by
      change (classifyingSpaceMapUniversal AsSmall.up).comp (classifyingSpaceMapUniversal F) =
        (classifyingSpaceMap (universeLiftFunctor F)).hom.comp
          (classifyingSpaceMapUniversal AsSmall.up)
      rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_comp,
        ← classifyingSpaceMapUniversal_comp]
      rfl) (classifyingSpacePoint d)).trans
    (fiberEndpointHomeomorph _ (classifyingSpaceUniverseHomeomorph_point D d))

/-- Lifting identifies the complete original structure-arrow homotopy with the
common-universe structure-arrow homotopy, including its interval parameter. -/
theorem structuredCommaUniversalHomotopy_universeLift (d : D)
    (x : ClassifyingSpace (StructuredArrow d F)) (t : unitInterval) :
    classifyingSpaceUniversalHomotopy (structuredCommaTransformationUniversal F d) (t, x) =
      (classifyingSpaceUniverseHomeomorph.{u₂, v₂, max u₁ v₁ u₂ v₂} D).symm
        (classifyingSpaceNaturalTransformationHomotopy
          (structuredCommaTransformation
            (universeLiftFunctor.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F)
            (AsSmall.up.obj d))
          (t, structuredArrowUniverseHomeomorph F d x)) := by
  let K : AsSmall.{max u₁ v₁ u₂ v₂} (StructuredArrow d F) ⥤
      StructuredArrow (AsSmall.up.obj d)
        (universeLiftFunctor.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F) :=
    AsSmall.down ⋙ structuredArrowUniverseUp F d
  let α := structuredCommaTransformation
    (universeLiftFunctor.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F) (AsSmall.up.obj d)
  change classifyingSpaceMapUniversal AsSmall.down
    (classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerLeft K α)
      (t, classifyingSpaceMapUniversal AsSmall.up x)) =
    classifyingSpaceMapUniversal AsSmall.down
      (classifyingSpaceNaturalTransformationHomotopy α
        (t, classifyingSpaceMapUniversal (structuredArrowUniverseUp F d) x))
  rw [classifyingSpaceNaturalTransformationHomotopy_whiskerLeft]
  apply congrArg (classifyingSpaceMapUniversal
    (AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} D ⥤ D))
  apply congrArg (fun y ↦ classifyingSpaceNaturalTransformationHomotopy α (t, y))
  change (classifyingSpaceMap K).hom (classifyingSpaceMapUniversal AsSmall.up x) =
    classifyingSpaceMapUniversal (structuredArrowUniverseUp F d) x
  rw [← classifyingSpaceMapUniversal_eq]
  change ((classifyingSpaceMapUniversal K).comp
    (classifyingSpaceMapUniversal AsSmall.up)) x = _
  rw [← classifyingSpaceMapUniversal_comp]
  rfl

/-- The canonical universe square commutes for the original structured comparison,
including its full path coordinate. -/
theorem structuredFiberComparisonUniversal_universeLift (d : D) :
    (structuredComparisonUniverseFiberHomeomorph F d : C(_, _)).comp
        (structuredFiberComparisonUniversal F d) =
      (structuredFiberComparison
        (universeLiftFunctor.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F) (AsSmall.up.obj d)).comp
        (structuredArrowUniverseHomeomorph F d : C(_, _)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · change ((classifyingSpaceMapUniversal AsSmall.up).comp
        (classifyingSpaceMapUniversal (StructuredArrow.proj d F))) x =
      ((classifyingSpaceMap (StructuredArrow.proj (AsSmall.up.obj d)
        (universeLiftFunctor F))).hom.comp
          (classifyingSpaceMapUniversal (structuredArrowUniverseUp F d))) x
    rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_comp,
      ← classifyingSpaceMapUniversal_comp, structuredArrowUniverseUp_proj]
  · apply ContinuousMap.ext
    intro t
    change classifyingSpaceUniverseHomeomorph D
      (classifyingSpaceUniversalHomotopy (structuredCommaTransformationUniversal F d)
        (unitInterval.symm t, x)) = _
    rw [structuredCommaUniversalHomotopy_universeLift, Homeomorph.apply_symm_apply]
    rfl

/-- The original structured comparison is a full weak equivalence at every target
object in independent universes, under weak equivalence of its original transitions. -/
theorem structuredFiberComparisonUniversal_isWeakHomotopyEquivalence
    (h : StructuredTransitionWeakEquivalencesUniversal F) (d : D) :
    IsWeakHomotopyEquivalence (structuredFiberComparisonUniversal F d) := by
  have hc := (structuredFiberComparison_isWeakHomotopyEquivalence
    (universeLiftFunctor.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F)
      (structuredTransitionWeakEquivalences_universeLift F h) (AsSmall.up.obj d)).comp
        (isWeakHomotopyEquivalence_of_homotopyEquiv
          (structuredArrowUniverseHomeomorph F d).toHomotopyEquiv)
  change IsWeakHomotopyEquivalence
    ((structuredFiberComparison
      (universeLiftFunctor.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F) (AsSmall.up.obj d)).comp
      (structuredArrowUniverseHomeomorph F d :
        C(ClassifyingSpace (StructuredArrow d F), _))) at hc
  rw [← structuredFiberComparisonUniversal_universeLift] at hc
  exact hc.of_comp_right (isWeakHomotopyEquivalence_of_homotopyEquiv
    (structuredComparisonUniverseFiberHomeomorph F d).toHomotopyEquiv)

end TheoremB
end Quillen
