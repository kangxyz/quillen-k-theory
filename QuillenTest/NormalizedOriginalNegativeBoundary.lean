/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowBoundary

/-! The actual normalized row keeps its own boundary and arbitrary original negative classes. -/
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
namespace QuillenTest.NormalizedOriginalNegativeBoundary
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- Arbitrary incoming original fiber classes retain the fixed independent finite class map. -/
theorem originalClass_precompose (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    {A : AddCommGrpCat.{u + 1}}
    (g : A ⟶ (Bass.supportedNegativeKFunctor i).obj
      ((boundedFlatCoefficientQuasiCompactOpenPairRow
        (supportArrow Q (unionOpen f.left T))).obj a)) :
    g ≫ GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
        (supportArrow Q (unionOpen f.left T)) i a ≫
        (normalizedFineSupportComparison f T a (-(i : ℤ))).hom =
      g ≫ fiberNegativeFineClass f T i a := by
  exact congrArg (fun k => g ≫ k) (normalizedNegativeClass_fine_fiber f T i a)

end QuillenTest.NormalizedOriginalNegativeBoundary
