/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeConjugationAllSign
public import Quillen.KTheory.Bass.SchemeAffineDoubleContractionSign
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterDoubleCorrection

/-!
# All original negative-class corrections from the actual coefficient swap sign

The actual integral-coefficient spectra determine the swap on affine parameters
through the canonical Spec–Gamma isomorphism. This genuine Laurent-closed family
feeds the original finite-word calculation. The original finite negative-class
isomorphisms are unchanged, both for ambient and for supported coefficients.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme PolynomialLaurent.Relative
open Quillen.KTheory.Bass.SchemeNaturalSeed Quillen.KTheory.Bass.GeometricConeInterchange
universe u
namespace Quillen.PerfectComplexes
open GlobalSectionChangeIndex

namespace GlobalParameterCoefficient
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [CompactSpace P.left]

/-- The actual affine coefficient swap sign makes every original ambient correction identity. -/
theorem negativeClassCorrection_hom_of_spec_swap
    (h : ∀ b, doubleContractionSwap (quasiCompactStableZero (parameterDiagram P))
      (coefficientParameterScheme b) = -𝟙 _)
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection P i a).hom = 𝟙 _ := by
  apply negativeClassCorrection_hom_of_finite_id P i a
  have : IsAffine (coefficientParameterScheme a).unop.obj :=
    inferInstanceAs (IsAffine (Spec a.right))
  exact finiteStageStableIso_neg_nat_id (fun X => IsAffine X.unop.obj)
    (ParameterModels.ambient P.left)
    (by
      intro X hX
      have : IsAffine X.unop.obj := hX
      exact doubleContractionSwap_neg_affine_of_under_spec
        (quasiCompactStableZero (parameterDiagram P)) h X)
    isAffine_laurent_parameter i (coefficientParameterScheme a) inferInstance

end GlobalParameterCoefficient

namespace GlobalSupportedParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The actual supported coefficient swap sign fixes every unchanged supported negative class. -/
theorem negativeClassCorrection_hom_of_spec_swap
    (h : ∀ b, doubleContractionSwap (quasiCompactStableZero (parameterDiagram f))
      (coefficientParameterScheme b) = -𝟙 _)
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection f i a).hom = 𝟙 _ := by
  apply negativeClassCorrection_hom_of_finite_id f i a
  have : IsAffine (coefficientParameterScheme a).unop.obj :=
    inferInstanceAs (IsAffine (Spec a.right))
  exact finiteStageStableIso_neg_nat_id (fun X => IsAffine X.unop.obj)
    (ParameterModels.supported f.left)
    (by
      intro X hX
      have : IsAffine X.unop.obj := hX
      exact doubleContractionSwap_neg_affine_of_under_spec
        (quasiCompactStableZero (parameterDiagram f)) h X)
    isAffine_laurent_parameter i (coefficientParameterScheme a) inferInstance

end GlobalSupportedParameterCoefficient
end Quillen.PerfectComplexes
