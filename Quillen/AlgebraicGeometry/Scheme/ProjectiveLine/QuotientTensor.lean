/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalQuotient

/-!
# Tensor with the actual quotient line

The two original quotient-line trivializations and actual tensor restriction
comparison identify tensor with the quotient line chartwise. These explicit
comparisons prove finite local freeness for a finite locally free coefficient
over every base ring, including the zero ring.
-/

@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry SheafOfModulesOfCommRing
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
/-- The original positive chart trivialization of tensor with the quotient line. -/
def quotientTensorPlusIso (R : CommRingCat.{u}) (E : (twoChartLine R).Modules) :
    ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R)).restrict
      (plusChart R) ≅ E.restrict (plusChart R) :=
  (tensorRestrictionIso (plusChart R) E (tautologicalQuotientLine R)).symm ≪≫
    (moduleTensorLeftFunctor (Spec (.of (Polynomial R))) (E.restrict (plusChart R))).mapIso
      (tautologicalQuotientPlusIso R) ≪≫
    (tensorRightUnitIso (Spec (.of (Polynomial R))).sheaf).app (E.restrict (plusChart R))
/-- The original negative chart trivialization of tensor with the quotient line. -/
def quotientTensorMinusIso (R : CommRingCat.{u}) (E : (twoChartLine R).Modules) :
    ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R)).restrict
      (minusChart R) ≅ E.restrict (minusChart R) :=
  (tensorRestrictionIso (minusChart R) E (tautologicalQuotientLine R)).symm ≪≫
    (moduleTensorLeftFunctor (Spec (.of (Polynomial R))) (E.restrict (minusChart R))).mapIso
      (tautologicalQuotientMinusIso R) ≪≫
    (tensorRightUnitIso (Spec (.of (Polynomial R))).sheaf).app (E.restrict (minusChart R))
/-- The original tensor with the quotient line preserves finite local freeness. -/
instance quotientTensor_finiteLocallyFree (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    IsFiniteLocallyFree (twoChartLine R)
      ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R)) := by
  let charts : Bool → (Spec (.of (Polynomial R)) ⟶ twoChartLine R) :=
    fun b => if b then plusChart R else minusChart R
  have hi : ∀ b, IsOpenImmersion (charts b) := by
    intro b
    cases b <;> dsimp [charts] <;> infer_instance
  let := hi
  apply finiteLocallyFree_of_affineCharts _
    (fun _ : Bool => CommRingCat.of (Polynomial R)) charts
  · intro x
    have hx : x ∈ (plusChart R).opensRange ⊔ (minusChart R).opensRange := by
      rw [chart_ranges_cover]; trivial
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · intro b
    cases b
    · exact finiteLocallyFree_of_iso (quotientTensorMinusIso R E).symm
    · exact finiteLocallyFree_of_iso (quotientTensorPlusIso R E).symm
end AlgebraicGeometry.Scheme.ProjectiveLine
