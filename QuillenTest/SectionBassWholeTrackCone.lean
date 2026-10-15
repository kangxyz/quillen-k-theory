/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassWholeTrackCone

/-!
# Original whole-track and independent-loop consumers at finite Bass stages

The actual supplied square track is retained through its first and second cylinder halves.
Stable equivalence uses only original stable sides, with every row-excision input discharged.
The parameter-loop consumer keeps independent homotopy, structure and loop times visible.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum
open scoped unitInterval
universe u
namespace QuillenTest.SectionBassWholeTrackCone

open Quillen
variable (i j i' j' : ℕ) (R S R' S' : CommRingCat.{u})
  (f : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram j).obj S)
  (g : (boundedFlatAffineSectionBassDiagram i').obj R' ⟶
    (boundedFlatAffineSectionBassDiagram j').obj S')
  (a : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram i').obj R')
  (b : (boundedFlatAffineSectionBassDiagram j).obj S ⟶
    (boundedFlatAffineSectionBassDiagram j').obj S')
  (H : Homotopy (f ≫ b) (a ≫ g))

/-- The actual whole-track cone comparison is invertible in every negative stable degree. -/
theorem negative_original_cone_iso (ha : IsStableEquivalence a) (hb : IsStableEquivalence b)
    (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map (mappingConeSquareMap f g a b H)) :=
  boundedFlatAffineSectionBass_wholeTrackCone_isStableEquivalence
    i j i' j' R S R' S' f g a b H ha hb _

/-- The same original full-track cone map remains stable after actual parameter looping. -/
theorem negative_original_looped_cone_iso
    (ha : IsStableEquivalence a) (hb : IsStableEquivalence b) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (parameterLoopingMap (mappingConeSquareMap f g a b H))) :=
  boundedFlatAffineSectionBass_loopedWholeTrackCone_isStableEquivalence
    i j i' j' R S R' S' f g a b H ha hb _

/-- The first original cylinder half keeps every supplied track value, not only its endpoints. -/
theorem original_first_half (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionBassDiagram i).obj R).space n) :
    (mappingConeSquareMap f g a b H).map n
      (ReducedMappingCone.cylinder (((boundedFlatAffineSectionBassDiagram i).obj R).point n)
        (((boundedFlatAffineSectionBassDiagram j).obj S).point n) (f.map n)
          (⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x)) =
      (mappingConeInclusion g).map n (H.level n (t, x)) :=
  mappingConeSquareMap_first_half f g a b H n t x

/-- The original target cylinder remains the entire second half on the actual source image. -/
theorem original_second_half (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionBassDiagram i).obj R).space n) :
    (mappingConeSquareMap f g a b H).map n
      (ReducedMappingCone.cylinder (((boundedFlatAffineSectionBassDiagram i).obj R).point n)
        (((boundedFlatAffineSectionBassDiagram j).obj S).point n) (f.map n)
          (⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x)) =
      ReducedMappingCone.cylinder (((boundedFlatAffineSectionBassDiagram i').obj R').point n)
        (((boundedFlatAffineSectionBassDiagram j').obj S').point n) (g.map n) (t, a.map n x) :=
  mappingConeSquareMap_second_half f g a b H n t x

/-- Homotopy time, structure time and actual loop time stay independently visible after looping. -/
theorem original_three_parameters (n : ℕ) (t r s : unitInterval)
    (γ : Path (((boundedFlatAffineSectionBassDiagram i).obj R).point n)
      (((boundedFlatAffineSectionBassDiagram i).obj R).point n)) :
    let τ : unitInterval := ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
    (Path.toContinuousMap (show Path ((mappingCone g).point (n + 1))
      ((mappingCone g).point (n + 1)) from
        (parameterLoopingMap (mappingConeSquareMap f g a b H)).map (n + 1)
          ((parameterLooping (mappingCone f)).structureMap n
            ((parameterLoopingMap ((mappingConeHomotopy f).at τ)).map n γ) r))) s =
      (mappingConeInclusion g).map (n + 1) (H.level (n + 1)
        (t, ((boundedFlatAffineSectionBassDiagram i).obj R).structureMap n (γ s) r)) := by
  exact mappingConeSquareMap_first_half f g a b H (n + 1) t
    (((boundedFlatAffineSectionBassDiagram i).obj R).structureMap n (γ s) r)

end QuillenTest.SectionBassWholeTrackCone
