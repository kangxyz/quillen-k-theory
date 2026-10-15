/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.ComplexContraction
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.OriginalLineContraction

/-! # The original line contractions on actual cochain complexes

The termwise lifts retain the original determinant contraction and braiding.
The bounded-below lifts retain the original composition and identity comparisons.
-/

@[expose] public section
open Quillen
open Quillen.SchemeSheaf


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (cochainContractionIso cochainContractionIso_hom_f plusContractionIso
  plusContractionIso_hom_app plusContractionIso_hom_f)
end Quillen.SchemeSheaf

end


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

/-- Actual cochain contraction of L tensor (Q tensor K). -/
def originalLeftLineContractionComplexIso :=
  cochainContractionIso _ _ (originalLeftLineContractionIso R)

/-- Actual cochain contraction of L tensor (K tensor Q), with original braiding. -/
def originalRightLineContractionComplexIso :=
  cochainContractionIso _ _ (originalRightLineContractionIso R)

/-- Actual bounded-below contraction of L tensor (Q tensor K). -/
def originalLeftLineContractionPlusIso :=
  plusContractionIso _ _ (originalLeftLineContractionIso R)

/-- Actual bounded-below contraction of L tensor (K tensor Q), with original braiding. -/
def originalRightLineContractionPlusIso :=
  plusContractionIso _ _ (originalRightLineContractionIso R)

/-- The original associator, determinant pairing and left unit occur in every degree. -/
lemma originalLeftLineContractionPlusIso_hom_f
    (K : CochainComplex.Plus (twoChartLine R).Modules) (n : ℤ) :
    ((originalLeftLineContractionPlusIso R).hom.app K).hom.f n =
      (originalLineAssociatorIso R).hom.app (K.obj.X n) ≫
        (moduleTensorCoefficientMap (twoChartLine R) (tautologicalLinePairing R)).app
          (K.obj.X n) ≫
        (SheafOfModulesOfCommRing.tensorLeftUnitIso (twoChartLine R).sheaf).hom.app
          (K.obj.X n) := by
  exact (plusContractionIso_hom_f _ _ (originalLeftLineContractionIso R) K n).trans
    (originalLeftLineContractionIso_hom R (K.obj.X n))

/-- The right contraction first uses the original braiding inside the left tensor. -/
lemma originalRightLineContractionPlusIso_hom_f
    (K : CochainComplex.Plus (twoChartLine R).Modules) (n : ℤ) :
    ((originalRightLineContractionPlusIso R).hom.app K).hom.f n =
      (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
        ((moduleTensorSymmetryNatIso (twoChartLine R) (tautologicalQuotientLine R)).hom.app
          (K.obj.X n)) ≫
        (originalLeftLineContractionIso R).hom.app (K.obj.X n) := by
  exact (plusContractionIso_hom_f _ _ (originalRightLineContractionIso R) K n).trans rfl

end AlgebraicGeometry.Scheme.ProjectiveLine
