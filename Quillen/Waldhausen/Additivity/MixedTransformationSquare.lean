/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.MixedTransformation
public import Quillen.Waldhausen.Additivity.NormalizedMixedHomotopy
public import Quillen.Waldhausen.Additivity.SubdivisionBasepoint
public import Quillen.Topology.Realization.HomotopyNaturality

/-!
# The actual two-time middle deformation square

The original minimum-cut input cylinder is followed by the actual weak-grid transformation
cylinder. Both independent times, the original subdivided source, and the exact identity and
separated cut faces are retained. Endpoint naturality triangles and the reversed-prefix/suffix
pasting of the final based-additivity square are separate constructions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Quillen.MixedOrdinalCylinder
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G H F' G' H' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')
  (ηF : F ⟶ F') (ηG : G ⟶ G') (haη : a ≫ ηG = ηF ≫ a')

private theorem normalizedPushoutApp_heq {f g : Arrow C} (h : f = g) :
    HEq ((normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app f)
      ((normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app g) := by
  subst g
  rfl

/-- The actual pushout transformation on the unchanged identity-interval family. -/
def normalizedIdentityTransformationFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((bisimplicialSSet V).obj n).obj m) :
    (((normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration).app n).app m A).1 ⟶
      (((normalizedIdentityMap V W a' hs'.exactF hs'.exactG hs'.cofibration).app n).app m A).1 :=
  Functor.whiskerLeft (intervalArrows (𝟙 n.unop) (𝟙 n.unop) (fun _ ↦ le_rfl) A.1)
    (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')

/-- Every component preserves the actual identity Arrow under reindexing. -/
theorem normalizedIdentityTransformationFamily_reindex {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n') (A : (TheoremA.diagonalSSet (bisimplicialSSet V)).obj n)
    (x : Grid₂ n'.unop n'.unop) :
    HEq ((normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη n' n'
        ((TheoremA.diagonalSSet (bisimplicialSSet V)).map α A)).app x)
      ((normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη n n A).app
        ((gridMap₂ α.unop α.unop).obj x)) := by
  apply normalizedPushoutApp_heq V W a a' b b' hs hs' ηF ηG haη
  rfl

/-- The actual pushout transformation on the unchanged separated-half family. -/
def normalizedSeparatedTransformationFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m) :
    (((normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration).app n).app m A).1 ⟶
      (((normalizedSeparatedMap V W a' hs'.exactF hs'.exactG hs'.cofibration).app n).app m A).1 :=
  Functor.whiskerLeft
    (intervalArrows (Edgewise.left n.unop n.unop) (Edgewise.right n.unop n.unop)
      (left_le_right n.unop) A.1)
    (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')

/-- The separated family retains the original subdivision and actual Arrow reindexing. -/
theorem normalizedSeparatedTransformationFamily_reindex {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n')
    (A : (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)).obj n)
    (x : Grid₂ n'.unop n'.unop) :
    HEq ((normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη n' n'
        ((TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)).map α A)).app x)
      ((normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη n n A).app
        ((gridMap₂ α.unop α.unop).obj x)) := by
  apply normalizedPushoutApp_heq V W a a' b b' hs hs' ηF ηG haη
  exact (congrArg (fun T ↦ T.obj x)
    (separatedIntervalArrows_reindex α.unop α.unop A.1)).symm

variable (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X))

/-- The original weak-grid cylinder at the actual identity endpoint. -/
def normalizedIdentityTransformationHomotopy :
    SSet.Homotopy
      (TheoremA.diagonalMap (normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration))
      (TheoremA.diagonalMap (normalizedIdentityMap V W a' hs'.exactF hs'.exactG hs'.cofibration)) :=
  diagonalWeakGridHomotopy W _ _
    (normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (fun _n _m _A _x ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (normalizedIdentityTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)

/-- The original weak-grid cylinder at the actual separated endpoint. -/
def normalizedSeparatedTransformationHomotopy :
    SSet.Homotopy
      (TheoremA.diagonalMap (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration))
      (TheoremA.diagonalMap
        (normalizedSeparatedMap V W a' hs'.exactF hs'.exactG hs'.cofibration)) :=
  diagonalWeakGridHomotopy W _ _
    (normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (fun _n _m _A _x ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (normalizedSeparatedTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)

/-- Zero-cut restriction identifies the entire original transformation cylinder. -/
theorem normalizedMixedTransformationHomotopy_zero :
    TheoremA.diagonalMap (outerZeroSection (bisimplicialSSet V)) ▷ Δ[1] ≫
        (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h =
      (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h := by
  ext n z
  apply Subtype.ext
  exact congrArg
    (fun T ↦ nerveCylinderDiagram (Functor.whiskerLeft T
      (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')) z.2.down)
    (mixedIntervalArrows_zero z.1.1)

/-- One-cut restriction identifies the entire unchanged separated transformation cylinder. -/
theorem normalizedMixedTransformationHomotopy_one :
    TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V)) ▷ Δ[1] ≫
        (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h =
      (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h := by
  ext n z
  apply Subtype.ext
  exact congrArg
    (fun T ↦ nerveCylinderDiagram (Functor.whiskerLeft T
      (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')) z.2.down)
    (mixedIntervalArrows_one z.1.1)

/-- The entire zero-cut transformation track realizes on the unchanged ordinary diagonal. -/
theorem normalizedMixedTransformationRealizationHomotopy_zero (t : unitInterval)
    (y : |TheoremA.diagonalSSet (bisimplicialSSet V)|) :
    realizationSimplicialHomotopy
      (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (t, SSet.toTop.map (TheoremA.diagonalMap (outerZeroSection (bisimplicialSSet V))) y) =
    realizationSimplicialHomotopy
      (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (t, y) := by
  simpa only [CategoryTheory.Functor.map_id, TopCat.id_app] using
    realizationSimplicialHomotopy_naturality
      (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (TheoremA.diagonalMap (outerZeroSection (bisimplicialSSet V))) (𝟙 _)
      (by simpa only [Category.comp_id] using
        (normalizedMixedTransformationHomotopy_zero V W a a' b b' hs hs'
          ηF ηG haη hηF hηG)) t y

/-- The original minimum-cut cylinder on the actual subdivided source. -/
def mixedTransformationInputCylinder :
    TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1] ⟶
      TheoremA.diagonalSSet (outerCylinder (bisimplicialSSet V)) :=
  TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V)) ▷ Δ[1] ≫
    (outerContraction (bisimplicialSSet V)).h

/-- The original minimum-cut zero face is horizontal restriction followed by the zero section. -/
theorem mixedTransformationInputCylinder_zero :
    SSet.ι₀ ≫ mixedTransformationInputCylinder V =
      TheoremA.diagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) ≫
        TheoremA.diagonalMap (outerZeroSection (bisimplicialSSet V)) := by
  simp only [mixedTransformationInputCylinder, SSet.ι₀_comp_assoc, SSet.Homotopy.h₀]
  change TheoremA.diagonalFunctor.map
    (outerOneSection (bisimplicialSSet V) ≫ outerProjection (bisimplicialSSet V) ≫
      outerZeroSection (bisimplicialSSet V)) = _
  rw [← Category.assoc, outerOneSection_projection]
  rfl

/-- The original minimum-cut one face is the unchanged one-section inclusion. -/
theorem mixedTransformationInputCylinder_one :
    SSet.ι₁ ≫ mixedTransformationInputCylinder V =
      TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V)) := by
  simp only [mixedTransformationInputCylinder, SSet.ι₁_comp_assoc, SSet.Homotopy.h₁,
    Category.comp_id]

/-- The literal two-time middle square: mixed time first, then transformation time simplicially. -/
def normalizedMixedTransformationSquare :
    (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1]) ⊗ Δ[1] ⟶
      TheoremA.diagonalSSet (bisimplicialSSet W) :=
  mixedTransformationInputCylinder V ▷ Δ[1] ≫
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h

/-- Transformation time zero is precisely the old original mixed deformation cylinder. -/
theorem normalizedMixedTransformationSquare_transformation_zero :
    SSet.ι₀ ≫ normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      (normalizedMixedEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration).h := by
  simp only [normalizedMixedTransformationSquare, SSet.ι₀_comp_assoc, SSet.Homotopy.h₀]
  rfl

/-- Transformation time one is precisely the primed original mixed deformation cylinder. -/
theorem normalizedMixedTransformationSquare_transformation_one :
    SSet.ι₁ ≫ normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      (normalizedMixedEndpointHomotopy V W a' hs'.exactF hs'.exactG hs'.cofibration).h := by
  simp only [normalizedMixedTransformationSquare, SSet.ι₁_comp_assoc, SSet.Homotopy.h₁]
  rfl

/-- Mixed time zero is the whole identity transformation cylinder on actual horizontal
restriction. -/
theorem normalizedMixedTransformationSquare_mixed_zero :
    (SSet.ι₀ ▷ Δ[1]) ≫
        normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      TheoremA.diagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) ▷
          Δ[1] ≫
        (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h := by
  rw [normalizedMixedTransformationSquare, ← Category.assoc, ← comp_whiskerRight,
    mixedTransformationInputCylinder_zero, comp_whiskerRight, Category.assoc,
    normalizedMixedTransformationHomotopy_zero]

/-- Mixed time one is the whole separated transformation cylinder on the original subdivision. -/
theorem normalizedMixedTransformationSquare_mixed_one :
    (SSet.ι₁ ▷ Δ[1]) ≫
        normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h := by
  rw [normalizedMixedTransformationSquare, ← Category.assoc, ← comp_whiskerRight,
    mixedTransformationInputCylinder_one, normalizedMixedTransformationHomotopy_one]

/-- Every cut and both independent simplicial times keep the original chosen zero. -/
theorem normalizedMixedTransformationSquare_fixed_zero :
    ((SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) ≫
        normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      CartesianMonoidalCategory.fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) := by
  ext n z
  apply Subtype.ext
  exact normalizedMixedTransformation_nerveCylinder_zero V W a a' b b' hs hs' ηF ηG haη
    (minCut (oneCut n.unop) z.1.2.down) z.2.down

/-- The actual two-time realization. The tuple order is transformation, mixed, then native input. -/
def normalizedMixedTransformationRealizationSquare :
    C(unitInterval × (unitInterval ×
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|),
      |TheoremA.diagonalSSet (bisimplicialSSet W)|) where
  toFun z := realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (z.1, realizationSimplicialHomotopy (outerContraction (bisimplicialSSet V))
        (z.2.1, SSet.toTop.map
          (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V))) z.2.2))
  continuous_toFun :=
    (realizationSimplicialHomotopy
      (normalizedMixedTransformationHomotopy V W a a' b b' hs hs'
        ηF ηG haη hηF hηG)).continuous.comp
      (continuous_fst.prodMk
        ((realizationSimplicialHomotopy (outerContraction (bisimplicialSSet V))).continuous.comp
          ((continuous_fst.comp continuous_snd).prodMk
            ((SSet.toTop.map
              (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V)))).hom.continuous.comp
                (continuous_snd.comp continuous_snd)))))

/-- The full two-time map is the realization of the literal square through the two original
inverse cylinder isomorphisms, without a global product-realization inverse. -/
theorem normalizedMixedTransformationRealizationSquare_apply (t s : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (t, (s, x)) =
      SSet.toTop.map
        (normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG)
        ((realizationCylinderIso
          (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1])).inv
          ((realizationCylinderIso
            (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V))).inv
              (x, ULift.up s), ULift.up t)) := by
  let p := (realizationCylinderIso
    (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V))).inv
      (x, ULift.up s)
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality
      (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V)))) (x, ULift.up s)
  change SSet.toTop.map
    (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V)) ▷ Δ[1]) p =
      (realizationCylinderIso (TheoremA.diagonalSSet (outerCylinder (bisimplicialSSet V)))).inv
        (SSet.toTop.map (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V))) x,
          ULift.up s) at hn
  have hi : realizationSimplicialHomotopy (outerContraction (bisimplicialSSet V))
      (s, SSet.toTop.map (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V))) x) =
        SSet.toTop.map (mixedTransformationInputCylinder V) p := by
    change SSet.toTop.map (outerContraction (bisimplicialSSet V)).h _ = _
    rw [← hn, mixedTransformationInputCylinder, Functor.map_comp, TopCat.comp_app]
  have ho := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (mixedTransformationInputCylinder V)) (p, ULift.up t)
  change SSet.toTop.map (mixedTransformationInputCylinder V ▷ Δ[1])
      ((realizationCylinderIso
        (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1])).inv
          (p, ULift.up t)) =
    (realizationCylinderIso (TheoremA.diagonalSSet (outerCylinder (bisimplicialSSet V)))).inv
      (SSet.toTop.map (mixedTransformationInputCylinder V) p, ULift.up t) at ho
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [hi]
  change SSet.toTop.map
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h _ = _
  rw [← ho, normalizedMixedTransformationSquare, Functor.map_comp, TopCat.comp_app]

/-- Transformation time zero is the entire old normalized mixed realization. -/
theorem normalizedMixedTransformationRealizationSquare_transformation_zero (s : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (0, (s, x)) =
      realizationSimplicialHomotopy
        (normalizedMixedEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration) (s, x) := by
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [ContinuousMap.Homotopy.apply_zero]
  exact realizationSimplicialHomotopy_naturality
    (outerContraction (bisimplicialSSet V))
    (normalizedMixedEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration)
    (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V)))
    (TheoremA.diagonalMap (normalizedMixedMap V W a hs.exactF hs.exactG hs.cofibration))
    rfl s x

/-- Transformation time one is the entire primed old normalized mixed realization. -/
theorem normalizedMixedTransformationRealizationSquare_transformation_one (s : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (1, (s, x)) =
      realizationSimplicialHomotopy
        (normalizedMixedEndpointHomotopy V W a' hs'.exactF hs'.exactG hs'.cofibration) (s, x) := by
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [ContinuousMap.Homotopy.apply_one]
  exact realizationSimplicialHomotopy_naturality
    (outerContraction (bisimplicialSSet V))
    (normalizedMixedEndpointHomotopy V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V)))
    (TheoremA.diagonalMap (normalizedMixedMap V W a' hs'.exactF hs'.exactG hs'.cofibration))
    rfl s x

/-- Mixed time zero is the full identity-endpoint transformation on actual horizontal
restriction. -/
theorem normalizedMixedTransformationRealizationSquare_mixed_zero (t : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (t, (0, x)) =
      realizationSimplicialHomotopy
        (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
        (t, SSet.toTop.map
          (TheoremA.diagonalMap
            (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))) x) := by
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [ContinuousMap.Homotopy.apply_zero]
  have hp := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ SSet.toTop.map (TheoremA.diagonalMap f))
      (outerOneSection_projection (bisimplicialSSet V))) x
  change (TheoremA.diagonalFunctor ⋙ SSet.toTop).map
    (outerOneSection (bisimplicialSSet V) ≫ outerProjection (bisimplicialSSet V)) x = _ at hp
  rw [Functor.map_comp, TopCat.comp_app] at hp
  change SSet.toTop.map (TheoremA.diagonalMap (outerProjection (bisimplicialSSet V)))
      (SSet.toTop.map (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V))) x) = _ at hp
  rw [SSet.toTop.map_comp]
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (t, SSet.toTop.map (TheoremA.diagonalMap (outerZeroSection (bisimplicialSSet V))) _) = _
  refine (congrArg (fun y ↦ realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (t, SSet.toTop.map (TheoremA.diagonalMap (outerZeroSection (bisimplicialSSet V))) y))
        hp).trans ?_
  exact normalizedMixedTransformationRealizationHomotopy_zero V W a a' b b' hs hs'
    ηF ηG haη hηF hηG t _

/-- Mixed time one is the full unchanged separated-endpoint transformation. -/
theorem normalizedMixedTransformationRealizationSquare_mixed_one (t : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (t, (1, x)) =
      realizationSimplicialHomotopy
        (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
        (t, x) := by
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [ContinuousMap.Homotopy.apply_one, SSet.toTop.map_id]
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (t, SSet.toTop.map (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V))) x) = _
  simpa only [CategoryTheory.Functor.map_id, TopCat.id_app] using
    realizationSimplicialHomotopy_naturality
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V))) (𝟙 _)
    (by simpa only [Category.comp_id] using
      normalizedMixedTransformationHomotopy_one V W a a' b b' hs hs' ηF ηG haη hηF hηG) t x

/-- Both full continuous times fix the actual subdivided zero input. -/
theorem normalizedMixedTransformationRealizationSquare_fixed_zero (t s : unitInterval) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (t, (s, subdivisionBasepoint V)) = realizationPoint (diagonalZeroVertex W) := by
  rw [normalizedMixedTransformationRealizationSquare_apply]
  let p := (realizationCylinderIso (Δ[0] : SSet.{max u v})).inv (default, ULift.up s)
  let z := (realizationCylinderIso (Δ[0] ⊗ Δ[1] : SSet.{max u v})).inv (p, ULift.up t)
  have hi := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (SSet.yonedaEquiv.symm (subdivisionZeroVertex V)))
    (default, ULift.up s)
  change SSet.toTop.map (SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) p =
    (realizationCylinderIso
      (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V))).inv
      (subdivisionBasepoint V, ULift.up s) at hi
  have ho := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality
      (SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1])) (p, ULift.up t)
  change SSet.toTop.map
    ((SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) z =
      (realizationCylinderIso
        (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1])).inv
        (SSet.toTop.map (SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) p,
          ULift.up t) at ho
  change SSet.toTop.map
    (normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [← hi, ← ho]
  change (SSet.toTop.map ((SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) ≫
    SSet.toTop.map
      (normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG)) z = _
  rw [← Functor.map_comp, normalizedMixedTransformationSquare_fixed_zero,
    Functor.map_comp, Functor.map_comp]
  change SSet.toTop.map (SSet.yonedaEquiv.symm (diagonalZeroVertex W)) _ = _
  exact congrArg (fun y : |(Δ[0] : SSet.{max u v})| ↦
    SSet.toTop.map (SSet.yonedaEquiv.symm (diagonalZeroVertex W)) y)
      (Subsingleton.elim _ default)

end Quillen.Waldhausen.Additivity
