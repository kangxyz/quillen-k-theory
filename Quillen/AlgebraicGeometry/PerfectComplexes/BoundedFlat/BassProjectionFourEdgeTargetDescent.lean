/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetCharts
public import Quillen.Topology.DoubleMappingCylinder.HomotopyDescent

/-!
# Descent of the six prescribed ordinary target cells

Comparison time is curried into a path space. Four applications of the existing displayed
homotopy descent then retain the genuine polynomial endpoints and all four original overlap
cells. No continuity assertion about the unrestricted native evaluator is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
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
local notation "J" => normalizedMap (polynomialProjection P a)
local notation "L" => |parameterSSet (reference P f E)|

/-- Keep the independent comparison coordinate in a continuous path space. -/
def value (t : I) : C(|parameterSSet E|, C(I, L)) :=
  ContinuousMap.curry ⟨fun z ↦ overlap P f E (z.1, (z.2, t)), by fun_prop⟩

/-- Both polynomial sectors have their own original chart square and anchor. -/
def chartValue (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    C(|parameterSSet (E ≫ J)|, C(I, L)) :=
  ContinuousMap.curry (chart P f E α ha)

/-- The interval of an overlap edge is independent of comparison time. -/
def edgeValue (clock : C(I, I)) : C(I × |parameterSSet E|, C(I, L)) :=
  ContinuousMap.curry ⟨fun z ↦ cell P f E clock (z.1.2, (z.2, z.1.1)), by fun_prop⟩

/-- Exact first edge homotopy, from vertex one to the positive polynomial sector. -/
def firstHomotopy :
    ((value P f E (clock12 0)).comp (SSet.toTop.map (𝟙 (parameterSSet E))).hom).Homotopy
      ((chartValue P f E (underToLaurent R) (laurentPlus_projection P a)).comp
        (SSet.toTop.map (attachment E J)).hom) where
  toContinuousMap := edgeValue P f E clock12
  map_zero_left y := by rw [SSet.toTop.map_id]; ext s; rfl
  map_one_left y := by
    ext s
    exact (cell12_endpoint P f E y s).trans (chart_plus_polynomial P f E y s).symm

/-- The first original realized double cylinder descends the prescribed homotopy. -/
def firstValue : C(|FourEdgeTree.first E J|, C(I, L)) :=
  DoubleCylinder.homotopyDesc _ _ (DoubleCylinder.realized_isPushout (𝟙 _) (attachment E J))
    (value P f E (clock12 0))
    (chartValue P f E (underToLaurent R) (laurentPlus_projection P a)) (firstHomotopy P f E)

theorem firstValue_one (y : |parameterSSet E|) :
    firstValue P f E (SSet.toTop.map (firstOne E J) y) = value P f E (clock12 0) y :=
  descent_left _ _ _ _ _ y

theorem firstValue_plus (y : |parameterSSet (E ≫ J)|) :
    firstValue P f E (SSet.toTop.map (firstPlus E J) y) =
      chartValue P f E (underToLaurent R) (laurentPlus_projection P a) y :=
  descent_right _ _ _ _ _ y

/-- Exact second edge homotopy, including its original descending quarter clock. -/
def secondHomotopy :
    ((value P f E (clock01 0)).comp (SSet.toTop.map (𝟙 (parameterSSet E))).hom).Homotopy
      ((firstValue P f E).comp (SSet.toTop.map (firstOne E J)).hom) where
  toContinuousMap := edgeValue P f E clock01
  map_zero_left y := by rw [SSet.toTop.map_id]; ext s; rfl
  map_one_left y := by
    apply ContinuousMap.ext
    intro s
    exact (seam_one P f E y s).trans
      (congrArg (fun k : C(I, L) ↦ k s) (firstValue_one P f E y)).symm

/-- The second original cylinder retains the whole first branch as its endpoint. -/
def secondValue : C(|FourEdgeTree.second E J|, C(I, L)) :=
  DoubleCylinder.homotopyDesc _ _ (DoubleCylinder.realized_isPushout (𝟙 _) (firstOne E J))
    (value P f E (clock01 0)) (firstValue P f E) (secondHomotopy P f E)

theorem secondValue_zero (y : |parameterSSet E|) :
    secondValue P f E (SSet.toTop.map (secondZero E J) y) = value P f E (clock01 0) y :=
  descent_left _ _ _ _ _ y

theorem secondValue_first (y : |FourEdgeTree.first E J|) :
    secondValue P f E (SSet.toTop.map (firstInSecond E J) y) = firstValue P f E y :=
  descent_right _ _ _ _ _ y

/-- Exact third edge homotopy, with the common whole central vertex. -/
def thirdHomotopy :
    ((secondValue P f E).comp (SSet.toTop.map (secondZero E J)).hom).Homotopy
      ((value P f E (clock03 1)).comp (SSet.toTop.map (𝟙 (parameterSSet E))).hom) where
  toContinuousMap := edgeValue P f E clock03
  map_zero_left y := by
    apply ContinuousMap.ext
    intro s
    exact (seam_zero P f E y s).trans
      (congrArg (fun k : C(I, L) ↦ k s) (secondValue_zero P f E y)).symm
  map_one_left y := by rw [SSet.toTop.map_id]; ext s; rfl

/-- The third original cylinder keeps the full earlier subtree. -/
def thirdValue : C(|FourEdgeTree.third E J|, C(I, L)) :=
  DoubleCylinder.homotopyDesc _ _ (DoubleCylinder.realized_isPushout (secondZero E J) (𝟙 _))
    (secondValue P f E) (value P f E (clock03 1)) (thirdHomotopy P f E)

theorem thirdValue_second (y : |FourEdgeTree.second E J|) :
    thirdValue P f E (SSet.toTop.map (secondInThird E J) y) = secondValue P f E y :=
  descent_left _ _ _ _ _ y

theorem thirdValue_three (y : |parameterSSet E|) :
    thirdValue P f E (SSet.toTop.map (thirdThree E J) y) = value P f E (clock03 1) y :=
  descent_right _ _ _ _ _ y

/-- The fourth edge meets the separate inverse polynomial chart at its exact endpoint. -/
def fourthHomotopy :
    ((thirdValue P f E).comp (SSet.toTop.map (thirdThree E J)).hom).Homotopy
      ((chartValue P f E (underToLaurentInvert R) (laurentMinus_projection P a)).comp
        (SSet.toTop.map (attachment E J)).hom) where
  toContinuousMap := edgeValue P f E clock34
  map_zero_left y := by
    apply ContinuousMap.ext
    intro s
    exact (seam_three P f E y s).trans
      (congrArg (fun k : C(I, L) ↦ k s) (thirdValue_three P f E y)).symm
  map_one_left y := by
    ext s
    exact (cell34_endpoint P f E y s).trans (chart_minus_polynomial P f E y s).symm

/-- The prescribed target surface descends on the entire ordinary reference tree. -/
def treeValue : C(FourEdgeTree.space E J, C(I, L)) :=
  DoubleCylinder.homotopyDesc _ _
    (DoubleCylinder.realized_isPushout (thirdThree E J) (attachment E J))
    (thirdValue P f E)
    (chartValue P f E (underToLaurentInvert R) (laurentMinus_projection P a))
    (fourthHomotopy P f E)

theorem treeValue_third (y : |FourEdgeTree.third E J|) :
    treeValue P f E (SSet.toTop.map (thirdInTree E J) y) = thirdValue P f E y :=
  descent_left _ _ _ _ _ y

theorem treeValue_minus (y : |parameterSSet (E ≫ J)|) :
    treeValue P f E (SSet.toTop.map (minusVertex E J) y) =
      chartValue P f E (underToLaurentInvert R) (laurentMinus_projection P a) y :=
  descent_right _ _ _ _ _ y

/-- The two independent coordinates of the original target surface remain continuous. -/
def tree : C(FourEdgeTree.space E J × I, L) := ContinuousMap.uncurry (treeValue P f E)

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
