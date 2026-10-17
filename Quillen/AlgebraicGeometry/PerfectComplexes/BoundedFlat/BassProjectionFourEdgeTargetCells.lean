/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetDescent

/-!
# The six complete original restrictions of the descended target surface

The two whole polynomial summands and four oriented cylinders recover their prescribed
nerve-valued families. Comparison time remains independent of every original edge clock.
These equalities are proved directly from the displayed pushout descents.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier FourEdgeTree

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => normalizedMap (polynomialProjection P a)
local notation "L" => |parameterSSet (reference P f E)|

/-- The original second subtree is unchanged after the two subsequent descents. -/
theorem treeValue_second (y : |FourEdgeTree.second E J|) :
    treeValue P f E (SSet.toTop.map (secondInTree E J) y) = secondValue P f E y := by
  rw [secondInTree, realized_comp, treeValue_third, thirdValue_second]

/-- The entire first branch survives all three subsequent attachments. -/
theorem treeValue_first (y : |FourEdgeTree.first E J|) :
    treeValue P f E (SSet.toTop.map (firstInTree E J) y) = firstValue P f E y := by
  rw [firstInTree, realized_comp, treeValue_second, secondValue_first]

/-- The original positive polynomial summand retains its complete chart-valued path. -/
theorem treeValue_plus (y : |parameterSSet (E ≫ J)|) :
    treeValue P f E (SSet.toTop.map (plusVertex E J) y) =
      chartValue P f E (underToLaurent R) (laurentPlus_projection P a) y := by
  rw [plusVertex, realized_comp, treeValue_first, firstValue_plus]

/-- The first full oriented cylinder keeps its original descending normalization clock. -/
theorem treeValue_edge12 (y : |parameterSSet E|) (t : I) :
    treeValue P f E (realizedEdge (edge12 E J) (y, t)) =
      edgeValue P f E clock12 (t, y) := by
  rw [edge12, realizedEdge_comp]
  change treeValue P f E (SSet.toTop.map (firstInTree E J)
    (DoubleCylinder.realizedCylinder (𝟙 _) (attachment E J) (y, ULift.up t))) = _
  rw [treeValue_first]
  exact DoubleCylinder.homotopyDesc_apply_cylinder _ _
    (DoubleCylinder.realized_isPushout (𝟙 _) (attachment E J))
    (value P f E (clock12 0))
    (chartValue P f E (underToLaurent R) (laurentPlus_projection P a))
    (firstHomotopy P f E) t y

/-- The second full oriented cylinder keeps its original descending geometric clock. -/
theorem treeValue_edge01 (y : |parameterSSet E|) (t : I) :
    treeValue P f E (realizedEdge (edge01 E J) (y, t)) =
      edgeValue P f E clock01 (t, y) := by
  rw [edge01, realizedEdge_comp]
  change treeValue P f E (SSet.toTop.map (secondInTree E J)
    (DoubleCylinder.realizedCylinder (𝟙 _) (firstOne E J) (y, ULift.up t))) = _
  rw [treeValue_second]
  exact DoubleCylinder.homotopyDesc_apply_cylinder _ _
    (DoubleCylinder.realized_isPushout (𝟙 _) (firstOne E J))
    (value P f E (clock01 0)) (firstValue P f E) (secondHomotopy P f E) t y

/-- The third full oriented cylinder keeps its original forward inverse geometric clock. -/
theorem treeValue_edge03 (y : |parameterSSet E|) (t : I) :
    treeValue P f E (realizedEdge (edge03 E J) (y, t)) =
      edgeValue P f E clock03 (t, y) := by
  rw [edge03, realizedEdge_comp]
  change treeValue P f E (SSet.toTop.map (thirdInTree E J)
    (DoubleCylinder.realizedCylinder (secondZero E J) (𝟙 _) (y, ULift.up t))) = _
  rw [treeValue_third]
  exact DoubleCylinder.homotopyDesc_apply_cylinder _ _
    (DoubleCylinder.realized_isPushout (secondZero E J) (𝟙 _))
    (secondValue P f E) (value P f E (clock03 1)) (thirdHomotopy P f E) t y

/-- The fourth full oriented cylinder keeps its separate inverse normalization clock. -/
theorem treeValue_edge34 (y : |parameterSSet E|) (t : I) :
    treeValue P f E (realizedEdge (edge34 E J) (y, t)) =
      edgeValue P f E clock34 (t, y) := by
  change treeValue P f E
    (DoubleCylinder.realizedCylinder (thirdThree E J) (attachment E J) (y, ULift.up t)) = _
  exact DoubleCylinder.homotopyDesc_apply_cylinder _ _
    (DoubleCylinder.realized_isPushout (thirdThree E J) (attachment E J))
    (thirdValue P f E)
    (chartValue P f E (underToLaurentInvert R) (laurentMinus_projection P a))
    (fourthHomotopy P f E) t y

/-- The entire positive polynomial sector has the genuine polynomial-source chart family. -/
theorem tree_plus (y : |parameterSSet (E ≫ J)|) (s : I) :
    tree P f E (SSet.toTop.map (plusVertex E J) y, s) =
      chart P f E (underToLaurent R) (laurentPlus_projection P a) (y, s) :=
  congrArg (fun k : C(I, L) ↦ k s) (treeValue_plus P f E y)

/-- The entire inverse polynomial sector retains its separate source projection equality. -/
theorem tree_minus (y : |parameterSSet (E ≫ J)|) (s : I) :
    tree P f E (SSet.toTop.map (minusVertex E J) y, s) =
      chart P f E (underToLaurentInvert R) (laurentMinus_projection P a) (y, s) :=
  congrArg (fun k : C(I, L) ↦ k s) (treeValue_minus P f E y)

/-- The positive normalization cell is unchanged at every comparison and edge time. -/
theorem tree_edge12 (y : |parameterSSet E|) (s t : I) :
    tree P f E (realizedEdge (edge12 E J) (y, t), s) =
      cell P f E clock12 (y, (s, t)) :=
  congrArg (fun k : C(I, L) ↦ k s) (treeValue_edge12 P f E y t)

/-- The positive geometric cell retains the original descending quarter. -/
theorem tree_edge01 (y : |parameterSSet E|) (s t : I) :
    tree P f E (realizedEdge (edge01 E J) (y, t), s) =
      cell P f E clock01 (y, (s, t)) :=
  congrArg (fun k : C(I, L) ↦ k s) (treeValue_edge01 P f E y t)

/-- The inverse geometric cell retains the original forward quarter. -/
theorem tree_edge03 (y : |parameterSSet E|) (s t : I) :
    tree P f E (realizedEdge (edge03 E J) (y, t), s) =
      cell P f E clock03 (y, (s, t)) :=
  congrArg (fun k : C(I, L) ↦ k s) (treeValue_edge03 P f E y t)

/-- The inverse normalization cell keeps its full independent comparison time. -/
theorem tree_edge34 (y : |parameterSSet E|) (s t : I) :
    tree P f E (realizedEdge (edge34 E J) (y, t), s) =
      cell P f E clock34 (y, (s, t)) :=
  congrArg (fun k : C(I, L) ↦ k s) (treeValue_edge34 P f E y t)

/-- The whole initial H0 row keeps both original source-chart paths and their common seam. -/
theorem overlap_zero (y : |parameterSSet E|) (t : I) :
    overlap P f E (y, (0, t)) =
    FiniteParameter.parameter E (reference P f E) (nodes P f E)
      (y, ((ProjectionRectangleParameters.D BassH0Diagram.plusFace).symm.trans
        (ProjectionRectangleParameters.D BassH0Diagram.minusFace)) t) := by
  change FiniteParameter.parameter E (reference P f E) (nodes P f E)
    (y, BassH0Diagram.parameter (0, t)) = _
  rw [BassH0Diagram.parameter_zero]

/-- The whole terminal H0 row retains both polynomial-square paths and the two chart paths. -/
theorem overlap_one (y : |parameterSSet E|) (t : I) :
    overlap P f E (y, (1, t)) =
    FiniteParameter.parameter E (reference P f E) (nodes P f E)
      (y, ((ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace).trans
        (((ProjectionRectangleParameters.K BassH0Diagram.plusFace).symm.trans
          (ProjectionRectangleParameters.K BassH0Diagram.minusFace)).trans
            (ProjectionRectangleParameters.Ppath BassH0Diagram.minusFace).symm)) t) := by
  change FiniteParameter.parameter E (reference P f E) (nodes P f E)
    (y, BassH0Diagram.parameter (1, t)) = _
  rw [BassH0Diagram.parameter_one]

/-- The entire original four-quarter overlap recovers H0 with both full coordinates unchanged. -/
theorem tree_overlap (y : |parameterSSet E|) (s t : I) :
    tree P f E (FourEdgeTree.overlap E J (y, t), s) = overlap P f E (y, (s, t)) := by
  rcases cover t with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · rcases cover (unitInterval.symm u) with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hu : u = unitInterval.symm (lower r) := by
        rw [hr, unitInterval.symm_symm]
      rw [hu, overlap_quarter01, tree_edge01]
      rfl
    · have hu : u = unitInterval.symm (upper r) := by
        rw [hr, unitInterval.symm_symm]
      rw [hu, overlap_quarter12, tree_edge12]
      rfl
  · rcases cover u with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · rw [overlap_quarter03, tree_edge03]
      rfl
    · rw [overlap_quarter34, tree_edge34]
      rfl

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
