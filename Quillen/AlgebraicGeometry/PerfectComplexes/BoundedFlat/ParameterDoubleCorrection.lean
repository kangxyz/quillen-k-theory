/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDoubleCorrection
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentNegativeCorrection

/-!
# Original second negative-class correction from the actual quotient sign

The original finite-bottom class isomorphisms are left untouched. The fixed
quotient sign on the actual parameter Model row forces its finite correction
to be identity, and hence also the independently defined correction on the
original ambient or supported negative group. The quotient sign remains an
explicit input, discharged separately by the genuine two-unit calculation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.KTheory.Bass Quillen.KTheory.Bass.SchemeNaturalSeed
open Quillen.KTheory.Bass.GeometricConeInterchange
universe u
namespace Quillen.PerfectComplexes
open GlobalSectionChangeIndex

/-- The same original integral coefficient spectrum as an actual quasi-compact parameter. -/
def coefficientParameterScheme (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    QuasiCompactSchemes.{u}ᵒᵖ := op ⟨Spec a.right, inferInstance⟩

private theorem iso_conj_id {A B : AddCommGrpCat.{u + 1}}
    (e : A ≅ B) (q : B ≅ B) (h : q.hom = 𝟙 B) :
    (e ≪≫ q ≪≫ e.symm).hom = 𝟙 A := by
  change e.hom ≫ q.hom ≫ e.inv = 𝟙 A
  rw [h, Category.id_comp, e.hom_inv_id]

namespace GlobalParameterCoefficient
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [CompactSpace P.left]

/-- An identity finite correction stays identity under the unchanged original class comparison. -/
theorem negativeClassCorrection_hom_of_finite_id (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (h : (finiteStageStableIso (ParameterModels.ambient P.left) i
      (specUnder.obj a) (-(i : ℤ))).hom = 𝟙 _) :
    (negativeClassCorrection P i a).hom = 𝟙 _ :=
  iso_conj_id ((finiteNegativeKComparison P i).app a)
    (finiteStageStableIso (ParameterModels.ambient P.left) i (specUnder.obj a) (-(i : ℤ))) h

/-- The original ambient correction is trivial under the actual parameter quotient sign. -/
theorem negativeClassCorrection_two_hom_of_quotient_swap
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (h : PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableZero (parameterDiagram P)) (coefficientParameterScheme a) = -𝟙 _) :
    (negativeClassCorrection P 2 a).hom = 𝟙 _ := by
  apply negativeClassCorrection_hom_of_finite_id P 2 a
  exact finiteStageStableIso_two_negTwo_id_of_quotient_swap
    (ParameterModels.ambient P.left) (coefficientParameterScheme a) h

end GlobalParameterCoefficient

namespace GlobalSupportedParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- An identity supported finite correction preserves the unchanged original supported classes. -/
theorem negativeClassCorrection_hom_of_finite_id (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (h : (finiteStageStableIso (ParameterModels.supported f.left) i
      (specUnder.obj a) (-(i : ℤ))).hom = 𝟙 _) :
    (negativeClassCorrection f i a).hom = 𝟙 _ :=
  iso_conj_id ((finiteNegativeKComparison f i).app a)
    (finiteStageStableIso (ParameterModels.supported f.left) i (specUnder.obj a) (-(i : ℤ))) h

/-- The original supported correction is trivial under its own actual parameter quotient sign. -/
theorem negativeClassCorrection_two_hom_of_quotient_swap
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (h : PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableZero (parameterDiagram f)) (coefficientParameterScheme a) = -𝟙 _) :
    (negativeClassCorrection f 2 a).hom = 𝟙 _ := by
  apply negativeClassCorrection_hom_of_finite_id f 2 a
  exact finiteStageStableIso_two_negTwo_id_of_quotient_swap
    (ParameterModels.supported f.left) (coefficientParameterScheme a) h

end GlobalSupportedParameterCoefficient
end Quillen.PerfectComplexes
