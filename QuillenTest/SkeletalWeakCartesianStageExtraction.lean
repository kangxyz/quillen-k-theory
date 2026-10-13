/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.TheoremB.SkeletalWeakCartesianStageExtraction

/-!
# General coefficient characteristic extraction regressions

Both diagrams and their arbitrary transformation remain visible. These
consumers check genuine component cartesianness, weakness of the original
characteristic map, dimension zero, and every value of the stored path.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Opposite
open Quillen Quillen.TheoremA Quillen.CartesianRealization.Skeletal
open scoped Simplicial Topology unitInterval
universe u
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

example {n : ℕ} (s : (nerve D).nonDegenerate n) :
    realizationFunctor.map (bisimplicialSigmaι (replacementCell H) s) ≫ cellProjection η n =
      realizationFunctor.map (outerProductCoefficientMap (K := (Δ[n] : SSet.{u}))
        (η.app (s.1.obj 0))) ≫ realizationFunctor.map (bisimplicialSigmaι (replacementCell J) s) :=
  coefficientComponentCell_square η s

example (n : ℕ) (s : (nerve D).nonDegenerate n) :
    WeakCartesian (realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) (η.app (s.1.obj 0)))).hom (cellProjection η n).hom
      (realizationFunctor.map (bisimplicialSigmaι (replacementCell H) s)).hom
      (realizationFunctor.map (bisimplicialSigmaι (replacementCell J) s)).hom
      (congrArg TopCat.Hom.hom (coefficientComponentCell_square η s)) :=
  (coefficientComponentCell_cartesian η n s).weak

example (n : ℕ)
    (h : WeakCartesian (cellProjection η n).hom (stageProjection η (n+1)).hom
      (characteristicLeg H n).hom (characteristicLeg J n).hom
      (congrArg TopCat.Hom.hom (cellCharacteristicSquare η n)))
    (s : (nerve D).nonDegenerate n) :
    ChartWeakCartesian η ((nerve D).skeleton (n+1)) s.1 ((nerve D).mem_skeleton s.1) :=
  coefficientComponentCharacteristic_weakCartesian η n h s

example (n : ℕ)
    (h : WeakCartesian (cellProjection η n).hom (stageProjection η (n+1)).hom
      (characteristicLeg H n).hom (characteristicLeg J n).hom
      (congrArg TopCat.Hom.hom (cellCharacteristicSquare η n)))
    (s : (nerve D).nonDegenerate n) :
    IsWeakHomotopyEquivalence (HomotopyPullback.comparison (stageProjection η (n+1)).hom
      (realizationFunctor.map (replacementCellCharacteristic J s)).hom
      (realizationFunctor.map (outerProductCoefficientMap
        (K := (Δ[n] : SSet.{u})) (η.app (s.1.obj 0)))).hom
      (realizationFunctor.map (replacementCellCharacteristic H s)).hom
      (congrArg TopCat.Hom.hom (coefficientComponentCharacteristic_square η s))) :=
  coefficientComponentCharacteristic_weakCartesian η n h s

example
    (h : WeakCartesian (cellProjection η 0).hom (stageProjection η 1).hom
      (characteristicLeg H 0).hom (characteristicLeg J 0).hom
      (congrArg TopCat.Hom.hom (cellCharacteristicSquare η 0)))
    (s : (nerve D).nonDegenerate 0) :
    ChartWeakCartesian η ((nerve D).skeleton 1) s.1 ((nerve D).mem_skeleton s.1) :=
  coefficientComponentCharacteristic_weakCartesian η 0 h s

example (n : ℕ) (s : (nerve D).nonDegenerate n)
    (x : realizationFunctor.obj (replacementCell H s)) (τ : unitInterval) :
    (HomotopyPullback.comparison (stageProjection η (n+1)).hom
      (realizationFunctor.map (replacementCellCharacteristic J s)).hom
      (realizationFunctor.map (outerProductCoefficientMap
        (K := (Δ[n] : SSet.{u})) (η.app (s.1.obj 0)))).hom
      (realizationFunctor.map (replacementCellCharacteristic H s)).hom
      (congrArg TopCat.Hom.hom (coefficientComponentCharacteristic_square η s)) x).val.2.2 τ =
      realizationFunctor.map (replacementCellCharacteristic J s)
        (realizationFunctor.map (outerProductCoefficientMap
          (K := (Δ[n] : SSet.{u})) (η.app (s.1.obj 0))) x) := rfl
