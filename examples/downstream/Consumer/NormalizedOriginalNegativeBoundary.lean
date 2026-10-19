/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowBoundary

/-! Any incoming original negative class retains the actual signed row boundary. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open Quillen.PerfectComplexes.ParameterAuxiliaryNormalizedRowLocalization
universe u
namespace Consumer.NormalizedOriginalNegativeBoundary
attribute [local instance] supportObject_compactSpace
attribute [local instance] GlobalSupportedParameterCoefficient.normalizedRowNegativeClass_isIso
attribute [local instance] fiberNegativeFineClass_isIso

/-- Incoming original negative classes preserve the intrinsic signed boundary. -/
theorem originalBoundary_precompose {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) {A : AddCommGrpCat.{u + 1}}
    (g : A ⟶ (Bass.supportedNegativeKFunctor i).obj
      ((boundedFlatCoefficientQuasiCompactOpenPairRow
        (supportArrow P (inverseOpen f.left T))).obj a)) :
    letI : CompactSpace (unionOpen f.left T) := unionOpen_compactSpace f T;
    letI : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T;
    letI : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f;
    g ≫ (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
        (supportArrow P (inverseOpen f.left T)) i a ≫
      (negativeLocalizationDegreeIso i).hom.app
        (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
          (specUnder.obj a)) ≫
      normalizedPresentationConnecting f T a (-((i + 1 : ℕ) : ℤ)) ≫
      inv (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
        (supportArrow Q (unionOpen f.left T)) (i + 1) a)) =
      g ≫ (openNegativeFineClass f T i a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a) ≫
      boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (-((i + 1 : ℕ) : ℤ)) ≫
      inv (fiberNegativeFineClass f T (i + 1) a)) := by
  let := unionOpen_compactSpace f T
  let := inverseOpen_compactSpace f T
  let := open_quasiSeparatedSpace f
  exact congrArg (fun k => g ≫ k) (normalizedNegativeConnecting_eq_original f T i a)

end Consumer.NormalizedOriginalNegativeBoundary
