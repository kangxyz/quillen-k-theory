/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSpanPolynomial
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgePath
public import Quillen.Topology.DoubleMappingCylinder.HomotopyDescent
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeCompactFamily

/-!
# The original coefficient span map in the target reference tree

The first two source quarter-cells lie in the positive polynomial nerve, the third traverses
one entire target overlap, and the fourth lies in the negative polynomial nerve. These are
exactly the original asymmetric half/quarter/quarter clock of mapSquareHomotopy.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetSpan
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier FourEdgeTree

private theorem descent_left {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    {T : Type u} [TopologicalSpace T] (l : C(|Y|, T)) (r : C(|Z|, T))
    (H : (l.comp (SSet.toTop.map f).hom).Homotopy (r.comp (SSet.toTop.map g).hom))
    (y : |Y|) :
    DoubleCylinder.homotopyDesc _ _ (DoubleCylinder.realized_isPushout f g) l r H
      (SSet.toTop.map (FourEdgeTree.left f g) y) = l y := by
  rw [FourEdgeTree.left, SetDescent.eval_realized_left]
  exact congrArg (fun k : C(|Y|, T) ↦ k y)
    (DoubleCylinder.homotopyDesc_left _ _ (DoubleCylinder.realized_isPushout f g) l r H)

private theorem descent_right {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    {T : Type u} [TopologicalSpace T] (l : C(|Y|, T)) (r : C(|Z|, T))
    (H : (l.comp (SSet.toTop.map f).hom).Homotopy (r.comp (SSet.toTop.map g).hom))
    (y : |Z|) :
    DoubleCylinder.homotopyDesc _ _ (DoubleCylinder.realized_isPushout f g) l r H
      (SSet.toTop.map (FourEdgeTree.right f g) y) = r y := by
  rw [FourEdgeTree.right, SetDescent.eval_realized_right]
  exact congrArg (fun k : C(|Z|, T) ↦ k y)
    (DoubleCylinder.homotopyDesc_right _ _ (DoubleCylinder.realized_isPushout f g) l r H)

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "Ja" => normalizedMap (polynomialProjection P a)
local notation "Jb" => normalizedMap (polynomialProjection P b)
local notation "T" => FourEdgeTree.space (input P f E) Jb

/-- The two distinct target polynomial summands retain the full coefficient node map. -/
def plusMap : C(|parameterSSet (E ≫ Ja)|, T) :=
  (SSet.toTop.map (plusVertex (input P f E) Jb)).hom.comp (polynomialMap P f E)
/-- Place the postcomposed polynomial reference in the target tree at its minus vertex. -/
def minusMap : C(|parameterSSet (E ≫ Ja)|, T) :=
  (SSet.toTop.map (minusVertex (input P f E) Jb)).hom.comp (polynomialMap P f E)

/-- The same original polynomial square takes values in either distinct target summand. -/
def plusSquare : C(|parameterSSet E| × I, T) :=
  (SSet.toTop.map (plusVertex (input P f E) Jb)).hom.comp (polynomialSquare P f E)
/-- Place the whole polynomial square at the target tree's minus vertex. -/
def minusSquare : C(|parameterSSet E| × I, T) :=
  (SSet.toTop.map (minusVertex (input P f E) Jb)).hom.comp (polynomialSquare P f E)

/-- The middle term is the entire target overlap after the original coefficient map. -/
def central : C(|parameterSSet E| × I, T) :=
  ⟨fun z ↦ FourEdgeTree.overlap (input P f E) Jb
    (mapParameter (postcompNode (normalizedMap (coefficientMap P f))) z.1, z.2), by fun_prop⟩

theorem central_zero (y : |parameterSSet E|) :
    central P f E (y, 0) = plusSquare P f E (y, 1) := by
  change FourEdgeTree.overlap _ _ (_, 0) =
    SSet.toTop.map (plusVertex (input P f E) Jb) (polynomialSquare P f E (y, 1))
  rw [FourEdgeTree.overlap_zero, polynomialSquare_one]
  rfl

theorem central_one (y : |parameterSSet E|) :
    central P f E (y, 1) = minusSquare P f E (y, 1) := by
  change FourEdgeTree.overlap _ _ (_, 1) =
    SSet.toTop.map (minusVertex (input P f E) Jb) (polynomialSquare P f E (y, 1))
  rw [FourEdgeTree.overlap_one, polynomialSquare_one]
  rfl

/-- The original one vertex lies halfway through the positive polynomial square. -/
def oneValue : C(|parameterSSet E|, T) :=
  ⟨fun y ↦ plusSquare P f E (y, lower 1), by fun_prop⟩
/-- The original zero vertex now lies at the positive endpoint of the target overlap. -/
def zeroValue : C(|parameterSSet E|, T) :=
  ⟨fun y ↦ plusSquare P f E (y, 1), by fun_prop⟩
/-- The original three vertex lies at the negative endpoint of the target overlap. -/
def threeValue : C(|parameterSSet E|, T) :=
  ⟨fun y ↦ minusSquare P f E (y, 1), by fun_prop⟩

/-- The first source quarter is the first reversed half of the positive square. -/
def firstHomotopy :
    ((oneValue P f E).comp (SSet.toTop.map (𝟙 (parameterSSet E))).hom).Homotopy
      ((plusMap P f E).comp (SSet.toTop.map (attachment E Ja)).hom) where
  toContinuousMap := ⟨fun z ↦ plusSquare P f E (z.2, lower (unitInterval.symm z.1)), by fun_prop⟩
  map_zero_left y := by
    rw [SSet.toTop.map_id]
    change plusSquare P f E (y, lower (unitInterval.symm 0)) =
      plusSquare P f E (y, lower 1)
    rw [unitInterval.symm_zero]
  map_one_left y := by
    change plusSquare P f E (y, lower (unitInterval.symm 1)) = _
    rw [unitInterval.symm_one]
    have h : lower (0 : I) = 0 := by apply Subtype.ext; norm_num [lower]
    rw [h]
    change SSet.toTop.map (plusVertex (input P f E) Jb) (polynomialSquare P f E (y, 0)) = _
    rw [polynomialSquare_zero]
    rfl

/-- Descend the first target cylinder from its original one-end, plus-end and homotopy data. -/
def firstValue : C(|FourEdgeTree.first E Ja|, T) :=
  DoubleCylinder.homotopyDesc _ _ (DoubleCylinder.realized_isPushout (𝟙 _) (attachment E Ja))
    (oneValue P f E) (plusMap P f E) (firstHomotopy P f E)
theorem firstValue_one (y : |parameterSSet E|) :
    firstValue P f E (SSet.toTop.map (firstOne E Ja) y) = oneValue P f E y :=
  descent_left _ _ _ _ _ y

theorem firstValue_plus (y : |parameterSSet (E ≫ Ja)|) :
    firstValue P f E (SSet.toTop.map (firstPlus E Ja) y) = plusMap P f E y :=
  descent_right _ _ _ _ _ y

/-- The second source quarter retains the second reversed half of the positive square. -/
def secondHomotopy :
    ((zeroValue P f E).comp (SSet.toTop.map (𝟙 (parameterSSet E))).hom).Homotopy
      ((firstValue P f E).comp (SSet.toTop.map (firstOne E Ja)).hom) where
  toContinuousMap := ⟨fun z ↦ plusSquare P f E (z.2, unitInterval.symm (lower z.1)), by fun_prop⟩
  map_zero_left y := by
    rw [SSet.toTop.map_id]
    change plusSquare P f E (y, unitInterval.symm (lower 0)) = plusSquare P f E (y, 1)
    have h : lower (0 : I) = 0 := by apply Subtype.ext; norm_num [lower]
    rw [h, unitInterval.symm_zero]
  map_one_left y := by
    change plusSquare P f E (y, unitInterval.symm (lower 1)) =
      firstValue P f E (SSet.toTop.map (firstOne E Ja) y)
    rw [firstValue_one]
    change plusSquare P f E (y, unitInterval.symm (lower 1)) = plusSquare P f E (y, lower 1)
    apply congrArg (fun t ↦ plusSquare P f E (y, t))
    apply Subtype.ext
    norm_num [lower]

/-- Descend the second target cylinder using the zero-end value and the entire first value. -/
def secondValue : C(|FourEdgeTree.second E Ja|, T) :=
  DoubleCylinder.homotopyDesc _ _ (DoubleCylinder.realized_isPushout (𝟙 _) (firstOne E Ja))
    (zeroValue P f E) (firstValue P f E) (secondHomotopy P f E)
theorem secondValue_zero (y : |parameterSSet E|) :
    secondValue P f E (SSet.toTop.map (secondZero E Ja) y) = zeroValue P f E y :=
  descent_left _ _ _ _ _ y

theorem secondValue_first (y : |FourEdgeTree.first E Ja|) :
    secondValue P f E (SSet.toTop.map (firstInSecond E Ja) y) = firstValue P f E y :=
  descent_right _ _ _ _ _ y

/-- The third source quarter is exactly the complete target overlap at its original speed. -/
def thirdHomotopy :
    ((secondValue P f E).comp (SSet.toTop.map (secondZero E Ja)).hom).Homotopy
      ((threeValue P f E).comp (SSet.toTop.map (𝟙 (parameterSSet E))).hom) where
  toContinuousMap := ⟨fun z ↦ central P f E (z.2, z.1), by fun_prop⟩
  map_zero_left y := (central_zero P f E y).trans (secondValue_zero P f E y).symm
  map_one_left y := by rw [SSet.toTop.map_id]; exact central_one P f E y

/-- Descend the third target cylinder using the entire second value and the three-end value. -/
def thirdValue : C(|FourEdgeTree.third E Ja|, T) :=
  DoubleCylinder.homotopyDesc _ _ (DoubleCylinder.realized_isPushout (secondZero E Ja) (𝟙 _))
    (secondValue P f E) (threeValue P f E) (thirdHomotopy P f E)
theorem thirdValue_three (y : |parameterSSet E|) :
    thirdValue P f E (SSet.toTop.map (thirdThree E Ja) y) = threeValue P f E y :=
  descent_right _ _ _ _ _ y

theorem thirdValue_second (y : |FourEdgeTree.second E Ja|) :
    thirdValue P f E (SSet.toTop.map (secondInThird E Ja) y) = secondValue P f E y :=
  descent_left _ _ _ _ _ y

/-- The last source quarter is the complete reversed negative polynomial square. -/
def fourthHomotopy :
    ((thirdValue P f E).comp (SSet.toTop.map (thirdThree E Ja)).hom).Homotopy
      ((minusMap P f E).comp (SSet.toTop.map (attachment E Ja)).hom) where
  toContinuousMap := ⟨fun z ↦ minusSquare P f E (z.2, unitInterval.symm z.1), by fun_prop⟩
  map_zero_left y := by
    change minusSquare P f E (y, unitInterval.symm 0) =
      thirdValue P f E (SSet.toTop.map (thirdThree E Ja) y)
    rw [unitInterval.symm_zero, thirdValue_three]
    rfl
  map_one_left y := by
    change minusSquare P f E (y, unitInterval.symm 1) = _
    rw [unitInterval.symm_one]
    change SSet.toTop.map (minusVertex (input P f E) Jb) (polynomialSquare P f E (y, 0)) = _
    rw [polynomialSquare_zero]
    rfl

/-- The actual target-tree input for the second half of the original cone map. -/
def treeMap : C(FourEdgeTree.space E Ja, T) :=
  DoubleCylinder.homotopyDesc _ _
    (DoubleCylinder.realized_isPushout (thirdThree E Ja) (attachment E Ja))
    (thirdValue P f E) (minusMap P f E) (fourthHomotopy P f E)

theorem treeMap_third (y : |FourEdgeTree.third E Ja|) :
    treeMap P f E (SSet.toTop.map (thirdInTree E Ja) y) = thirdValue P f E y :=
  descent_left _ _ _ _ _ y

theorem treeMap_minus (y : |parameterSSet (E ≫ Ja)|) :
    treeMap P f E (SSet.toTop.map (minusVertex E Ja) y) = minusMap P f E y :=
  descent_right _ _ _ _ _ y

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetSpan
