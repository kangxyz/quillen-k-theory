/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicNegativeBoundary
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicPerfectClasses

/-! # Original negative and zero classes of the actual basic row -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes ParameterNormalizedBasicLocalization GlobalSectionChangeIndex
namespace QuillenTest.NormalizedBasicOriginalClasses
universe u
attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace
attribute [local instance] GlobalSupportedParameterCoefficient.normalizedRowNegativeClass_isIso
attribute [local instance] basicNormalizedNegativeClass_isIso

private theorem remove_original_inverse {C : Type*} [Category C] {A B D : C}
    (a : A ⟶ D) (b : B ⟶ D) [IsIso b] (c : A ⟶ B)
    (h : a ≫ inv b = c) : a = c ≫ b := by
  have h' := congrArg (fun f => f ≫ b) h
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original N₁-to-N₂ square has no permutation or unrecorded sign in its class maps. -/
theorem original_first_negative_square (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    GlobalParameterCoefficient.normalizedRowNegativeClass
        (Over.mk (toIntegerBase U.toScheme)) 1 a ≫
      (negativeLocalizationDegreeIso 1).hom.app
        (ParameterTensorNormalizedRowPresentation.ambient U.toScheme (specUnder.obj a)) ≫
      basicSpecConnecting Q U a (-((1 + 1 : ℕ) : ℤ)) =
    boundedFlatCoefficientNegativeLocalizationConnecting (basicOverInclusion Q U) 1 a ≫
      GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
        (basicOverInclusion Q U) (1 + 1) a := by
  have : IsIso (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
      (basicOverInclusion Q U) (1 + 1) a) := basicNormalizedNegativeClass_isIso Q U (1 + 1) a
  apply remove_original_inverse _ _ _
  simpa only [Category.assoc] using basicNegativeConnecting_eq_original Q U 1 a

/-- Ambient K₀ keeps the original bottom map with only the original ambient compactness. -/
theorem original_ambient_zero (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    [CompactSpace P.left] (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (x : ((ParameterModels.ambient P.left).obj (specUnder.obj a)).waldhausen.K 0) :
    (normalizedFineAmbientComparison P a 0).hom
      (SchemeModelRowSeed.normalizedModelClass (ParameterModels.ambient P.left)
        (ParameterLaurentUnit.ambientUnit P.left)
        (ParameterLaurentUnit.ambientUnit_naturality P.left)
        (specUnder.obj a) 0 x) =
      (stableHomotopyFunctor 0).map
        ((boundedFlatCoefficientAmbientBassTelescopeInclusion P 0).app a)
        (((boundedFlatCoefficientAmbientBassBottomZeroNatIso P).hom.app a)
          (Additive.ofMul (boundedFlatCoefficientSectionPerfectKEquiv (op P, a) 0
            (Quillen.Waldhausen.KMap ((parameterCoefficientRestriction P).app a).exact 0 x)))) :=
  normalized_fine_ambient_originalZeroClass P a x

end QuillenTest.NormalizedBasicOriginalClasses
