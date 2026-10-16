/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalGenerationEndpoints
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalCoefficientFunctors
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineTensor
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect

/-! # Original tautological tensor preserves intrinsic perfect D+

Use actual local line trivializations on an arbitrary bounded-below representative.
No global strict model or quasicoherent representative is selected here.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.PerfectComplexes

open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance derivedLinePerfectStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- Actual right tensor with the original tautological line preserves local perfection. -/
theorem locallyPerfect_original_tautologicalRightTensor
    (K : CochainComplex (twoChartLine R).Modules ℤ)
    (hK : locallyPerfect (twoChartLine R) K) :
    locallyPerfect (twoChartLine R)
      (((moduleTensorRightFunctor (twoChartLine R)
        (tautologicalLine R)).mapHomologicalComplex (.up ℤ)).obj K) := by
  let e : ∀ b : Bool, (tautologicalLine R).restrict (polynomialChart R b) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf := by
    intro b
    cases b
    · exact tautologicalLineMinusIso R
    · exact tautologicalLinePlusIso R
  have h := locallyPerfect_tensorByLine (tautologicalLine R)
    (fun _ : Bool => Spec (.of (Polynomial R))) (polynomialChart R)
    (polynomialChart_cover R) e hK
  exact locallyPerfect_of_iso ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeftRightIso
    (tautologicalLine R)).app K) h

/-- The original exact quotient-free tautological tensor preserves intrinsic
perfectness on genuine D+ inputs by its installed exact unit and local trivializations. -/
theorem perfect_derivedTautologicalRightTensor
    (K : DerivedCategory.Plus (twoChartLine R).Modules)
    (hK : perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj K)) :
    perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj
      ((moduleTensorRightFunctor (twoChartLine R)
        (tautologicalLine R)).rightDerivedFunctorPlus.obj K)) := by
  let T := moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R)
  let := T.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let := Localization.essSurj DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (twoChartLine R).Modules)
  let P := DerivedCategory.Plus.Q.objPreimage K
  let eP := DerivedCategory.Plus.Q.objObjPreimageIso K
  have hP : locallyPerfect (twoChartLine R) P.obj :=
    (perfectDerivedObjects_toDerived_iff (twoChartLine R) P.obj).mp
      ((perfectDerivedObjects (twoChartLine R)).prop_of_iso
        (DerivedCategory.Plus.ι.mapIso eP.symm) hK)
  have ht := locallyPerfect_original_tautologicalRightTensor R P.obj hP
  let e : DerivedCategory.Plus.Q.obj (T.mapCochainComplexPlus.obj P) ≅
      T.rightDerivedFunctorPlus.obj K :=
    asIso (T.rightDerivedFunctorPlusUnit.app P) ≪≫ T.rightDerivedFunctorPlus.mapIso eP
  exact (perfectDerivedObjects (twoChartLine R)).prop_of_iso
    (DerivedCategory.Plus.ι.mapIso e)
    ((perfectDerivedObjects_toDerived_iff (twoChartLine R) _).mpr ht)
end AlgebraicGeometry.Scheme.ProjectiveLine
