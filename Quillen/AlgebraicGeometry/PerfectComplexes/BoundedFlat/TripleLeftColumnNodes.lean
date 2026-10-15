/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0SourceNode

/-! Full dependent nodes of the original triple's left binary column. -/
@[expose] public section

open Quillen.PerfectComplexes.BassReferenceMerge

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
open BassReferenceMerge

/-- The canonical model morphism of one original normalized pullback. -/
def normalizedMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modelOf (boundedFlatPerfectWaldhausen Y) ⟶ modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact f) (boundedFlatNormalizedPullback_obj_zero _)

/-- The source, geometric intermediate, and target of the binary normalization simplex, each with
its comparison from the source.
-/
def binaryNodes {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : Fin 3 →
    Σ F : modelOf (boundedFlatPerfectWaldhausen Z) ⟶ modelOf (boundedFlatPerfectWaldhausen X),
      (BinaryNormalizationSimplex.sourceMap f g).functor ≅ F.functor :=
  ![⟨BinaryNormalizationSimplex.sourceMap f g, Iso.refl _⟩,
    ⟨BinaryNormalizationSimplex.intermediateMap f g, BinaryNormalizationSimplex.first f g⟩,
    ⟨BinaryNormalizationSimplex.targetMap f g, BinaryNormalizationSimplex.total f g⟩]

variable {X Y Z T : Scheme.{u}}
  (F : modelOf (boundedFlatPerfectWaldhausen T) ⟶ modelOf (boundedFlatPerfectWaldhausen X))
  (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  (e : F.functor = (NormalizedTripleSimplex.sourceMap f g h).functor)

/-- The vertex indices `2, 3, 7` selecting the left binary column of the split triple simplex. -/
def leftIndex : Fin 3 → Fin 8 := ![2, 3, 7]

/-- The full original left-column nodes, with the original common reference retained. -/
def tripleLeftNode (i : Fin 3) :
    Σ G : modelOf (boundedFlatPerfectWaldhausen T) ⟶ modelOf (boundedFlatPerfectWaldhausen X),
      F.functor ≅ G.functor :=
  ⟨SplitTripleSimplex.vertices f g h (leftIndex i),
    eqToIso e ≪≫ SplitTripleSimplex.references f g h (leftIndex i)⟩

/-- The same binary column after literal normalized postcomposition. -/
def binaryColumnNode (i : Fin 3) :
    Σ G : modelOf (boundedFlatPerfectWaldhausen T) ⟶ modelOf (boundedFlatPerfectWaldhausen X),
      F.functor ≅ G.functor :=
  ⟨(binaryNodes g h i).1 ≫ normalizedMap f,
    (eqToIso e ≪≫ BinaryNormalizationSimplex.total f (g ≫ h)) ≪≫
      isoWhiskerRight (binaryNodes g h i).2 (normalizedMap f).functor⟩

theorem triple_left_column_functor (i : Fin 3) :
    (tripleLeftNode F f g h e i).1.functor = (binaryColumnNode F f g h e i).1.functor := by
  fin_cases i <;> rfl

/-- The actual triple's full left binary column equals its postcomposed original binary nodes. -/
theorem triple_left_column (i : Fin 3) :
    tripleLeftNode F f g h e i = binaryColumnNode F f g h e i := by
  fin_cases i
  · apply Sigma.ext (Model.Hom.ext (triple_left_column_functor F f g h e 0))
    apply heq_of_eq
    change eqToIso e ≪≫ BinaryNormalizationSimplex.total f (g ≫ h) =
      (eqToIso e ≪≫ BinaryNormalizationSimplex.total f (g ≫ h)) ≪≫
        isoWhiskerRight (Iso.refl (BinaryNormalizationSimplex.sourceMap g h).functor)
          (normalizedMap f).functor
    rw [isoWhiskerRight_refl]
    exact (Iso.trans_refl (eqToIso e ≪≫ BinaryNormalizationSimplex.total f (g ≫ h))).symm
  · apply Sigma.ext (Model.Hom.ext (triple_left_column_functor F f g h e 1))
    apply heq_of_eq
    change eqToIso e ≪≫ (smallIso (boundedFlatNormalizedPullbackCompIso f (g ≫ h)) ≪≫
        smallIso (isoWhiskerRight (BinaryNormalizationSimplex.geometricIso g h)
          (boundedFlatNormalizedPullback f))) =
      (eqToIso e ≪≫ smallIso (boundedFlatNormalizedPullbackCompIso f (g ≫ h))) ≪≫
        isoWhiskerRight (smallIso (BinaryNormalizationSimplex.geometricIso g h))
          (AsSmall.down ⋙ boundedFlatNormalizedPullback f ⋙ AsSmall.up)
    rw [smallIso_postcomp, Iso.trans_assoc]
  · apply Sigma.ext (Model.Hom.ext (triple_left_column_functor F f g h e 2))
    apply heq_of_eq
    have ha : Functor.associator (boundedFlatNormalizedPullback h)
        (boundedFlatNormalizedPullback g) (boundedFlatNormalizedPullback f) = Iso.refl _ := rfl
    change eqToIso e ≪≫ (smallIso (boundedFlatNormalizedPullbackCompIso f (g ≫ h)) ≪≫
        smallIso (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso g h)
          (boundedFlatNormalizedPullback f) ≪≫
            Functor.associator (boundedFlatNormalizedPullback h)
              (boundedFlatNormalizedPullback g) (boundedFlatNormalizedPullback f))) =
      (eqToIso e ≪≫ smallIso (boundedFlatNormalizedPullbackCompIso f (g ≫ h))) ≪≫
        isoWhiskerRight (smallIso (boundedFlatNormalizedPullbackCompIso g h))
          (AsSmall.down ⋙ boundedFlatNormalizedPullback f ⋙ AsSmall.up)
    rw [ha, Iso.trans_refl, smallIso_postcomp, Iso.trans_assoc]

/-- Actual equality of the postcomposition map preserves the complete anchored binary column. -/
theorem binaryColumnNode_congr {f' : X ⟶ Y} (hf : f = f')
    (e' : F.functor = (NormalizedTripleSimplex.sourceMap f' g h).functor) (i : Fin 3) :
    binaryColumnNode F f g h e i = binaryColumnNode F f' g h e' i := by
  subst f'
  rfl

end Quillen.PerfectComplexes.BassH0Merge
