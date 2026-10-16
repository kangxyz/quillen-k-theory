/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalQuotient
public import Mathlib.Data.ZMod.Basic
public import Aglib.AlgebraicGeometry.Modules.Restriction.Overlap

/-! Original quotient rows, cokernel factorization, inverse transition and zero-ring consumers. -/
@[expose] public section

open ModuleCat
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.ProjectiveLineTautologicalQuotient

open Quillen
variable (R : CommRingCat.{u})

/-- The displayed original arrows satisfy the exactness predicate. -/
theorem original_exact_sequence :
    (ShortComplex.mk (tautologicalLineInclusion R) (tautologicalQuotientMap R)
      (cokernel.condition _)).ShortExact := tautologicalSequence_shortExact R

/-- Every original arrow annihilating the subline factors uniquely through the original quotient. -/
theorem original_quotient_factorization {M : (twoChartLine R).Modules}
    (g : ((SheafOfModules.unit (twoChartLine R).ringCatSheaf : (twoChartLine R).Modules) ⨯
      SheafOfModules.unit (twoChartLine R).ringCatSheaf) ⟶ M)
    (hg : tautologicalLineInclusion R ≫ g = 0) :
    ∃! h : tautologicalQuotientLine R ⟶ M, tautologicalQuotientMap R ≫ h = g := by
  let := tautologicalQuotientMap_epi R
  refine ⟨cokernel.desc _ g hg, ?_, ?_⟩
  · exact cokernel.π_desc _ _ _
  · intro h hh
    apply (cancel_epi (tautologicalQuotientMap R)).mp
    exact hh.trans (cokernel.π_desc _ _ _).symm

/-- The actual positive quotient map has row coefficients `(-t, 1)`. -/
theorem positive_signed_row :
    (Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalQuotientMap R) ≫
        (tautologicalQuotientPlusIso R).hom =
      (Scheme.Modules.restrictFunctor (plusChart R)).map prod.snd ≫
          (Scheme.Modules.restrictUnitIso (plusChart R)).hom -
        (Scheme.Modules.restrictFunctor (plusChart R)).map prod.fst ≫
          (Scheme.Modules.restrictUnitIso (plusChart R)).hom ≫
            unitMul _ (polynomialCoordinate R) := by
  rw [tautologicalQuotientMap_plus, firstRow_eq]

/-- The actual negative quotient map has row coefficients `(-1, s)`. -/
theorem negative_signed_row :
    (Scheme.Modules.restrictFunctor (minusChart R)).map (tautologicalQuotientMap R) ≫
        (tautologicalQuotientMinusIso R).hom =
      (Scheme.Modules.restrictFunctor (minusChart R)).map prod.snd ≫
          (Scheme.Modules.restrictUnitIso (minusChart R)).hom ≫
            unitMul _ (polynomialCoordinate R) -
        (Scheme.Modules.restrictFunctor (minusChart R)).map prod.fst ≫
          (Scheme.Modules.restrictUnitIso (minusChart R)).hom := by
  rw [tautologicalQuotientMap_minus, secondRow_eq]

/-- In unit coordinates the gluing square multiplies by the inverse original overlap unit. -/
theorem original_transition_scalar :
    (Scheme.Modules.restrictFunctor (pullback.fst (plusChart R) (minusChart R))).map
        (tautologicalQuotientPlusIso R).hom ≫
      (Scheme.Modules.restrictUnitIso (pullback.fst (plusChart R) (minusChart R))).hom ≫
      unitMul _ (↑(overlapCoordinateUnit R)⁻¹) =
    (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso (plusChart R) (minusChart
      R)).hom.app
        (tautologicalQuotientLine R) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd (plusChart R) (minusChart R))).map
        (tautologicalQuotientMinusIso R).hom ≫
      (Scheme.Modules.restrictUnitIso (pullback.snd (plusChart R) (minusChart R))).hom := by
  have h := congrArg
    (fun f => f ≫
      (Scheme.Modules.restrictUnitIso (pullback.snd (plusChart R) (minusChart R))).hom)
    (tautologicalQuotientLine_transition R)
  simpa only [columnTransition, Iso.trans_hom, Iso.symm_hom, unitMulIso,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- The quotient line remains finite locally free over a nonreduced ring. -/
theorem nonreduced_base : IsFiniteLocallyFree (twoChartLine (.of (ZMod 4)))
    (tautologicalQuotientLine (.of (ZMod 4))) := inferInstance

/-- No nontriviality hypothesis is needed for the quotient construction. -/
theorem zero_base : IsFiniteLocallyFree (twoChartLine (.of (ZMod 1)))
    (tautologicalQuotientLine (.of (ZMod 1))) := inferInstance

end QuillenTest.ProjectiveLineTautologicalQuotient
