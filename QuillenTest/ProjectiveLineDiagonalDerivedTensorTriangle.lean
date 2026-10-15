/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalDerivedTensorTriangle
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of the genuine derived diagonal tensor triangle

Check right-unit naturality, actual quotient chart maps, the installed derived
unit, the literal derived third vertex and recovery of the original connecting
morphism. Nonreduced and zero rings retain the same original construction.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.ProjectiveLine

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry DerivedCategory CategoryTheory.Pretriangulated
open SheafOfModulesOfCommRing AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
namespace QuillenTest.ProjectiveLineDiagonalDerivedTensorTriangle

open Quillen

/-- Standard original ambient derived categories. -/
local instance derivedTensorStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The actual right unit is natural in an arbitrary original module arrow. -/
theorem original_right_unit_naturality {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    ((tensorFunctor X.sheaf).map f).app (SheafOfModules.unit X.ringCatSheaf) ≫
        (tensorRightUnitIso X.sheaf).hom.app N =
      (tensorRightUnitIso X.sheaf).hom.app M ≫ f :=
  (tensorRightUnitIso X.sheaf).hom.naturality f

/-- The positive tensor chart uses the actual quotient row trivialization. -/
theorem original_positive_chart (R : CommRingCat.{u}) (E : (twoChartLine R).Modules) :
    (quotientTensorPlusIso R E).hom =
      (tensorRestrictionIso (plusChart R) E (tautologicalQuotientLine R)).inv ≫
        (moduleTensorLeftFunctor (Spec (.of (Polynomial R))) (E.restrict (plusChart R))).map
          (tautologicalQuotientPlusIso R).hom ≫
        (tensorRightUnitIso (Spec (.of (Polynomial R))).sheaf).hom.app
          (E.restrict (plusChart R)) := rfl

/-- The negative tensor chart uses the actual negative quotient row trivialization. -/
theorem original_negative_chart (R : CommRingCat.{u}) (E : (twoChartLine R).Modules) :
    (quotientTensorMinusIso R E).hom =
      (tensorRestrictionIso (minusChart R) E (tautologicalQuotientLine R)).inv ≫
        (moduleTensorLeftFunctor (Spec (.of (Polynomial R))) (E.restrict (minusChart R))).map
          (tautologicalQuotientMinusIso R).hom ≫
        (tensorRightUnitIso (Spec (.of (Polynomial R))).sheaf).hom.app
          (E.restrict (minusChart R)) := rfl

/-- The derived comparison is literally the original single comparison and installed unit. -/
theorem original_diagonal_derived_unit (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    (diagonalQuotientTensorDerivedIso R E).hom =
      DerivedCategory.Plus.Q.map (pushforwardSingleZeroPlusIso (relativeDiagonal R) _).inv ≫
        (derivedPushforwardPlusUnit (relativeDiagonal R)).app
          (singleZeroPlus (twoChartLine R)
            ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R))) :=
  diagonalQuotientTensorDerivedIso_hom R E

/-- The third vertex is the original bounded-below derived direct image in the ambient category. -/
theorem original_derived_vertex (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    (diagonalDerivedTensorTriangle R E).obj₃ =
      DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (relativeDiagonal R)).obj
        (DerivedCategory.Plus.Q.obj (singleZeroPlus (twoChartLine R)
          ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R))))) := rfl

/-- The actual derived comparison recovers the original supported connecting map. -/
theorem original_connecting_recovered (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    (diagonalSupportedDerivedVertexIso R E).hom ≫ (diagonalDerivedTensorTriangle R E).mor₃ =
      (diagonalSupportedTensorTriangle R E).mor₃ := by
  simp [diagonalDerivedTensorTriangle]

/-- The original negative-line derived triangle is distinguished over a nonreduced base. -/
theorem nonreduced_derived_triangle :
    diagonalDerivedTensorTriangle (CommRingCat.of (ZMod 4))
      (tautologicalLine (CommRingCat.of (ZMod 4))) ∈
        distTriang (DerivedCategory (relativeSquare (CommRingCat.of (ZMod 4))).Modules) :=
  diagonalDerivedTensorTriangle_distinguished _ _

/-- The same original derived triangle remains distinguished over the zero ring. -/
theorem zero_ring_derived_triangle :
    diagonalDerivedTensorTriangle (CommRingCat.of (ZMod 1))
      (tautologicalLine (CommRingCat.of (ZMod 1))) ∈
        distTriang (DerivedCategory (relativeSquare (CommRingCat.of (ZMod 1))).Modules) :=
  diagonalDerivedTensorTriangle_distinguished _ _

end QuillenTest.ProjectiveLineDiagonalDerivedTensorTriangle
