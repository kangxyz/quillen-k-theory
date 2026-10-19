/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictDiagramIndexRow
public import Quillen.KTheory.Bass.TwoChartStableSequence

/-!
# Original target inclusions and signed shifts under index and row transport

The actual index-plus-row square preserves the original cone inclusion followed
by the inverse signed parameter shift. Its rightmost corner is the original
index arrow followed by the specified row map. The first two finite row
isomorphisms retain exactly these squares; no seed assumption is needed.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen.LoopPrespectrum

universe u₁ v₁ u₂ v₂ w

namespace Quillen.KTheory.Bass.StrictDiagramIndexRow

/-- The unchanged target inclusion followed by the genuine inverse signed shift. -/
def targetShift (S : Arrow (Arrow LoopPrespectrum.{w})) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).obj S.right.right ⟶
      (stableHomotopyFunctor d).obj (strictSquareLoopedConeFunctor.obj S) :=
  (stableHomotopyFunctor (d + 1)).map (mappingConeInclusion (StrictSquare.comparison S)) ≫
    (parameterStableHomotopyIso (mappingCone (StrictSquare.comparison S)) d).inv

/-- Every actual strict square map preserves both original arrows in the target shift. -/
@[reassoc]
theorem targetShift_naturality {S T : Arrow (Arrow LoopPrespectrum.{w})}
    (a : S ⟶ T) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map a.right.right ≫ targetShift T d =
      targetShift S d ≫ (stableHomotopyFunctor d).map (strictSquareLoopedConeFunctor.map a) := by
  dsimp only [targetShift]
  rw [Quillen.Bass.TwoChartStable.comparisonConeMap_inclusion_assoc]
  simp only [Category.assoc]
  exact congrArg (fun k => (stableHomotopyFunctor (d + 1)).map
    (mappingConeInclusion (StrictSquare.comparison S)) ≫ k)
      (Quillen.Bass.TwoChartStable.bassMap_shift_inv a d).symm

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)
    {F : D ⥤ LoopPrespectrum.{w}} {G : C ⥤ LoopPrespectrum.{w}}
    (ρ : K ⋙ F ≅ G)

/-- Actual coefficient arrows preserve the unchanged target inclusion and signed shift. -/
@[reassoc]
theorem diagram_targetShift_naturality {X Y : D} (f : X ⟶ Y) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (F.map (Q₂.map f).right.right) ≫
        targetShift (F.mapArrow.mapArrow.obj (Q₂.obj Y)) d =
      targetShift (F.mapArrow.mapArrow.obj (Q₂.obj X)) d ≫
        (stableHomotopyFunctor d).map (((strictDiagramFunctor Q₂).obj F).map f) :=
  targetShift_naturality (F.mapArrow.mapArrow.map (Q₂.map f)) d

/-- The actual four-corner map first transports the index, then the specified row. -/
def targetSquare (X : C) :
    F.mapArrow.mapArrow.obj (Q₂.obj (K.obj X)) ⟶ G.mapArrow.mapArrow.obj (Q₁.obj X) :=
  F.mapArrow.mapArrow.map (α.hom.app X) ≫
    (((Functor.mapArrowFunctor (Arrow C) (Arrow LoopPrespectrum.{w})).map
      ((Functor.mapArrowFunctor C LoopPrespectrum.{w}).map ρ.hom)).app (Q₁.obj X))

/-- The original Laurent corner retains the actual index and row maps in their order. -/
theorem targetSquare_right_right (X : C) :
    (targetSquare K Q₁ Q₂ α ρ X).right.right =
      F.map (α.hom.app X).right.right ≫ ρ.hom.app (Q₁.obj X).right.right := rfl

/-- The first finite isomorphism acts by the same complete strict-square map. -/
theorem finiteIso_one_hom_app (X : C) :
    (finiteIso K Q₁ Q₂ α ρ 1).hom.app X =
      strictSquareLoopedConeFunctor.map (targetSquare K Q₁ Q₂ α ρ X) := by
  simp only [finiteIso, StrictDiagramIndexChange.iterateIso, Iso.trans_hom,
    Functor.mapIso_hom, strictDiagramIterate, Functor.comp_map, Functor.id_map,
    Iso.refl_hom, NatTrans.comp_app]
  rw [StrictDiagramIndexChange.iso_hom_app, targetSquare,
    CategoryTheory.Functor.map_comp]
  rfl

/-- The actual first finite index-plus-row map preserves the original signed representative. -/
@[reassoc]
theorem finiteIso_one_targetShift (X : C) (d : ℤ) :
    targetShift (F.mapArrow.mapArrow.obj (Q₂.obj (K.obj X))) d ≫
        (stableHomotopyFunctor d).map ((finiteIso K Q₁ Q₂ α ρ 1).hom.app X) =
      (stableHomotopyFunctor (d + 1)).map
          (F.map (α.hom.app X).right.right ≫ ρ.hom.app (Q₁.obj X).right.right) ≫
        targetShift (G.mapArrow.mapArrow.obj (Q₁.obj X)) d := by
  rw [finiteIso_one_hom_app]
  exact (targetShift_naturality (targetSquare K Q₁ Q₂ α ρ X) d).symm

/-- The second finite comparison is the same first-step construction on the actual first rows. -/
theorem finiteIso_two_hom :
    (finiteIso K Q₁ Q₂ α ρ 2).hom =
      (finiteIso K Q₁ Q₂ α (finiteIso K Q₁ Q₂ α ρ 1) 1).hom := by
  simp only [finiteIso, StrictDiagramIndexChange.iterateIso, Iso.trans_hom,
    Functor.mapIso_hom, strictDiagramIterate, Functor.comp_map, Functor.id_map,
    Iso.refl_hom, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, CategoryTheory.Functor.map_comp, Category.assoc]

end Quillen.KTheory.Bass.StrictDiagramIndexRow
