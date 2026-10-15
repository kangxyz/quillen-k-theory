/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological
public import Mathlib.Data.ZMod.Basic

/-! Actual coordinate projections, transition units and zero-ring tautological consumers. -/
@[expose] public section

open ModuleCat
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.ProjectiveLineTautological

variable (R : CommRingCat.{u})

/-- The first global coordinate becomes the actual positive-chart trivialization. -/
theorem positive_first_coordinate :
    (Scheme.Modules.restrictFunctor (plusChart R)).map
        (tautologicalLineInclusion R) ≫
      (Scheme.Modules.restrictFunctor (plusChart R)).map prod.fst =
    (tautologicalLinePlusIso R).hom ≫ (Scheme.Modules.restrictUnitIso (plusChart R)).inv := by
  rw [tautologicalLineInclusion_plus, Category.assoc, firstColumn_fst]

/-- The other global coordinate is multiplied by the original polynomial section. -/
theorem positive_second_coordinate :
    (Scheme.Modules.restrictFunctor (plusChart R)).map
        (tautologicalLineInclusion R) ≫
      (Scheme.Modules.restrictFunctor (plusChart R)).map prod.snd =
    (tautologicalLinePlusIso R).hom ≫
      unitMul _ (polynomialCoordinate R) ≫ (Scheme.Modules.restrictUnitIso (plusChart R)).inv := by
  rw [tautologicalLineInclusion_plus, Category.assoc, firstColumn_snd]

/-- The second global coordinate gives the original negative-chart trivialization. -/
theorem negative_second_coordinate :
    (Scheme.Modules.restrictFunctor (minusChart R)).map
        (tautologicalLineInclusion R) ≫
      (Scheme.Modules.restrictFunctor (minusChart R)).map prod.snd =
    (tautologicalLineMinusIso R).hom ≫ (Scheme.Modules.restrictUnitIso (minusChart R)).inv := by
  rw [tautologicalLineInclusion_minus, Category.assoc, secondColumn_snd]

/-- Equality after the actual inclusion detects equality of sheaf arrows. -/
theorem inclusion_detects_equality {M : (twoChartLine R).Modules}
    (f g : M ⟶ tautologicalLine R)
    (h : f ≫ tautologicalLineInclusion R = g ≫ tautologicalLineInclusion R) : f = g :=
  (cancel_mono (tautologicalLineInclusion R)).mp h

/-- The genuine Laurent coordinates of the transition and its inverse multiply to one. -/
theorem original_transition_coordinates :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
        ((chart_isPullback R).isoPullback.hom.appTop.hom (↑(overlapCoordinateUnit R))) *
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
        ((chart_isPullback R).isoPullback.hom.appTop.hom (↑(overlapCoordinateUnit R)⁻¹)) = 1 := by
  rw [overlapCoordinateUnit_coordinates, overlapCoordinateUnit_inv_coordinates,
    ← LaurentPolynomial.T_add]
  norm_num

/-- In unit coordinates the actual gluing square is multiplication by the original overlap unit. -/
theorem original_transition_scalar :
    (Scheme.Modules.restrictFunctor (pullback.fst (plusChart R) (minusChart R))).map
        (tautologicalLinePlusIso R).hom ≫
      (Scheme.Modules.restrictUnitIso (pullback.fst (plusChart R) (minusChart R))).hom ≫
      unitMul _ (↑(overlapCoordinateUnit R)) =
    (AlgebraicGeometry.Scheme.Modules.Coherent.overlapRestrictIso (plusChart R) (minusChart
      R)).hom.app
        (tautologicalLine R) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd (plusChart R) (minusChart R))).map
        (tautologicalLineMinusIso R).hom ≫
      (Scheme.Modules.restrictUnitIso (pullback.snd (plusChart R) (minusChart R))).hom := by
  have h := congrArg
    (fun f => f ≫
      (Scheme.Modules.restrictUnitIso (pullback.snd (plusChart R) (minusChart R))).hom)
    (tautologicalLine_transition R)
  simpa only [columnTransition, Iso.trans_hom, Iso.symm_hom, unitMulIso,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- Finite local freeness retains nonreduced coefficient rings. -/
theorem nonreduced_base : IsFiniteLocallyFree (twoChartLine (.of (ZMod 4)))
    (tautologicalLine (.of (ZMod 4))) := inferInstance

/-- The original construction also covers the zero ring. -/
theorem zero_base : IsFiniteLocallyFree (twoChartLine (.of (ZMod 1)))
    (tautologicalLine (.of (ZMod 1))) := inferInstance

end QuillenTest.ProjectiveLineTautological
