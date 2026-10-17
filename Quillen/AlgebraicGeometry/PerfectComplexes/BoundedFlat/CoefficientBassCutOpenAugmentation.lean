/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeTree

/-! Attach both original polynomial sheets to a carrier retaining its whole Laurent summand. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenAugmentation
open CutOpenCarrier

/-- Change only the left summand of an original double cylinder, with its exact attachment. -/
def changeLeft {X Y Y' Z : SSet.{u}} (f : X ⟶ Y) (f' : X ⟶ Y') (g : X ⟶ Z)
    (j : Y ⟶ Y') (h : f ≫ j = f') :
    DoubleCylinder.simplicial f g ⟶ DoubleCylinder.simplicial f' g :=
  (DoubleCylinder.simplicial_isPushout f g).desc
    (DoubleCylinder.simplicialCylinder f' g)
    (coprod.desc (j ≫ FourEdgeTree.left f' g) (FourEdgeTree.right f' g)) (by
      apply coprod.hom_ext
      · simpa [DoubleCylinder.simplicialEndpoints, Category.assoc, ← h] using
          FourEdgeTree.cylinder_zero f' g
      · simpa [DoubleCylinder.simplicialEndpoints, Category.assoc] using
          FourEdgeTree.cylinder_one f' g)

@[reassoc] theorem changeLeft_left {X Y Y' Z : SSet.{u}}
    (f : X ⟶ Y) (f' : X ⟶ Y') (g : X ⟶ Z) (j : Y ⟶ Y') (h : f ≫ j = f') :
    FourEdgeTree.left f g ≫ changeLeft f f' g j h = j ≫ FourEdgeTree.left f' g := by
  change coprod.inl ≫ (DoubleCylinder.simplicialEnds f g ≫ _) = _
  dsimp only [changeLeft]
  rw [(DoubleCylinder.simplicial_isPushout f g).inr_desc]
  exact coprod.inl_desc _ _

@[reassoc] theorem changeLeft_right {X Y Y' Z : SSet.{u}}
    (f : X ⟶ Y) (f' : X ⟶ Y') (g : X ⟶ Z) (j : Y ⟶ Y') (h : f ≫ j = f') :
    FourEdgeTree.right f g ≫ changeLeft f f' g j h = FourEdgeTree.right f' g := by
  change coprod.inr ≫ (DoubleCylinder.simplicialEnds f g ≫ _) = _
  dsimp only [changeLeft]
  rw [(DoubleCylinder.simplicial_isPushout f g).inr_desc]
  exact coprod.inr_desc _ _

@[reassoc] theorem changeLeft_cylinder {X Y Y' Z : SSet.{u}}
    (f : X ⟶ Y) (f' : X ⟶ Y') (g : X ⟶ Z) (j : Y ⟶ Y') (h : f ≫ j = f') :
    DoubleCylinder.simplicialCylinder f g ≫ changeLeft f f' g j h =
      DoubleCylinder.simplicialCylinder f' g :=
  (DoubleCylinder.simplicial_isPushout f g).inl_desc _ _ _

variable {V W T : Model.{u}} (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (ε₀ ε₁ : G.functor ≅ (F ≫ J).functor) (B : SSet.{u}) (j : parameterSSet G ⟶ B)

/-- The ordinary sheet attaches through the prescribed original Laurent map. -/
def first : SSet.{u} := DoubleCylinder.simplicial (attaching F J G ε₀ ≫ j) (erase F)
/-- Include the supplied base carrier into the first attached polynomial sheet. -/
def baseFirst : B ⟶ first F J G ε₀ B j :=
  FourEdgeTree.left (attaching F J G ε₀ ≫ j) (erase F)
/-- Include the first sheet's separate tip into the first double cylinder. -/
def firstTip : tipSSet ⟶ first F J G ε₀ B j :=
  FourEdgeTree.right (attaching F J G ε₀ ≫ j) (erase F)

/-- The shifted sheet retains its exact shifted reference and its own terminal tip. -/
def secondAttaching : parameterSSet F ⟶ first F J G ε₀ B j :=
  attaching F J G ε₁ ≫ j ≫ baseFirst F J G ε₀ B j
/-- Attach the second polynomial sheet to the first augmented carrier by its prescribed anchor. -/
def simplicial : SSet.{u} :=
  DoubleCylinder.simplicial (secondAttaching F J G ε₀ ε₁ B j) (erase F)
/-- Include the entire first augmented sheet into the two-sheet simplicial carrier. -/
def firstIn : first F J G ε₀ B j ⟶ simplicial F J G ε₀ ε₁ B j :=
  FourEdgeTree.left (secondAttaching F J G ε₀ ε₁ B j) (erase F)
/-- Include the second sheet's separate tip into the two-sheet simplicial carrier. -/
def secondTip : tipSSet ⟶ simplicial F J G ε₀ ε₁ B j :=
  FourEdgeTree.right (secondAttaching F J G ε₀ ε₁ B j) (erase F)
/-- Include the supplied base carrier through both successive sheet attachments. -/
def baseIn : B ⟶ simplicial F J G ε₀ ε₁ B j :=
  baseFirst F J G ε₀ B j ≫ firstIn F J G ε₀ ε₁ B j

/-- The ordinary source sheet maps by its literal cylinder coordinate. -/
def firstMap : CutOpenCarrier.firstSimplicial F J G ε₀ ⟶ first F J G ε₀ B j :=
  changeLeft (attaching F J G ε₀) (attaching F J G ε₀ ≫ j) (erase F) j rfl

@[reassoc] theorem firstMap_left :
    CutOpenCarrier.left₀ F J G ε₀ ≫ firstMap F J G ε₀ B j = j ≫ baseFirst F J G ε₀ B j :=
  changeLeft_left _ _ _ _ _

/-- The original two-tip carrier maps into the augmentation without identifying its tips. -/
def map : CutOpenCarrier.simplicial F J G ε₀ ε₁ ⟶ simplicial F J G ε₀ ε₁ B j :=
  changeLeft (CutOpenCarrier.secondAttaching F J G ε₀ ε₁)
    (secondAttaching F J G ε₀ ε₁ B j) (erase F) (firstMap F J G ε₀ B j) (by
      dsimp only [CutOpenCarrier.secondAttaching, secondAttaching]
      rw [Category.assoc, firstMap_left])

@[reassoc] theorem map_first :
    CutOpenCarrier.left₁ F J G ε₀ ε₁ ≫ map F J G ε₀ ε₁ B j =
      firstMap F J G ε₀ B j ≫ firstIn F J G ε₀ ε₁ B j :=
  changeLeft_left _ _ _ _ _

@[reassoc] theorem map_tipPlus :
    CutOpenCarrier.right₁ F J G ε₀ ε₁ ≫ map F J G ε₀ ε₁ B j =
      secondTip F J G ε₀ ε₁ B j := changeLeft_right _ _ _ _ _

@[reassoc] theorem map_tipMinus :
    CutOpenCarrier.right₀ F J G ε₀ ≫ CutOpenCarrier.left₁ F J G ε₀ ε₁ ≫
        map F J G ε₀ ε₁ B j = firstTip F J G ε₀ B j ≫ firstIn F J G ε₀ ε₁ B j := by
  rw [map_first, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ firstIn F J G ε₀ ε₁ B j)
    (changeLeft_right (attaching F J G ε₀) (attaching F J G ε₀ ≫ j) (erase F) j rfl)

@[reassoc] theorem map_laurent :
    CutOpenCarrier.left₀ F J G ε₀ ≫ CutOpenCarrier.left₁ F J G ε₀ ε₁ ≫
        map F J G ε₀ ε₁ B j = j ≫ baseIn F J G ε₀ ε₁ B j := by
  rw [map_first, ← Category.assoc, firstMap_left]
  rfl

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenAugmentation
