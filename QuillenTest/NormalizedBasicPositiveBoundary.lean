/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicPositiveBoundary

/-!
The intrinsic normalized basic boundary retains original finite K-one classes,
the original supported K-zero endpoint, and the absolute geometric kernel.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes ParameterNormalizedBasicLocalization GlobalSectionChangeIndex
open Quillen.PerfectComplexes.Bass Quillen.PerfectComplexes.Bass.SupportedLocalization
universe u
attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace
attribute [local instance] basicOriginalPair_source_compact basicOriginalPair_target_quasiSeparated

namespace QuillenTest.NormalizedBasicPositiveBoundary
variable (Q : Scheme.{u}) (U : Q.Opens)
  [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U]

/-- The finite K-one class reaches precisely the original supported negative-recursion seed. -/
theorem basic_Kone_original_Kzero
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (z : ((ParameterModels.ambient U.toScheme).obj (specUnder.obj a)).waldhausen.K (0 + 1)) :
    let : CompactSpace (space (op (Over.mk (toIntegerBase U.toScheme)), a)) :=
      compactSpace_space (op (Over.mk (toIntegerBase U.toScheme)), a)
    let : CompactSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
      compactSpace_space (op (Over.mk (toIntegerBase Q)), a)
    let : QuasiSeparatedSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
      quasiSeparatedSpace_space (op (Over.mk (toIntegerBase Q)), a)
    (normalizedFineSupportComparison (basicOverInclusion Q U) a ((0 : ℕ) : ℤ)).hom
      (basicSpecConnecting Q U a ((0 : ℕ) : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          (ParameterTensorNormalizedRowPresentation.ambient U.toScheme (specUnder.obj a)))
          (show ((0 + 1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) + 1 from rfl))
        (SchemeModelRowSeed.normalizedModelClass (ParameterModels.ambient U.toScheme)
          (ParameterLaurentUnit.ambientUnit U.toScheme)
          (ParameterLaurentUnit.ambientUnit_naturality U.toScheme)
          (specUnder.obj a) (0 + 1) z))) =
      -((stableHomotopyFunctor ((0 : ℕ) : ℤ)).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion (basicOverInclusion Q U) 0).app a)
        ((boundedFlatCoefficientSupportedBassBottomZeroIso (basicOverInclusion Q U) a).hom
          (Additive.ofMul (qcqsPerfectConnectingHom (schemeMap (basicOverInclusion Q U) a) 0
            (boundedFlatCoefficientSectionPerfectKEquiv
              (op (Over.mk (toIntegerBase U.toScheme)), a) (0 + 1)
            (Quillen.Waldhausen.KMap
              ((parameterCoefficientRestriction (Over.mk (toIntegerBase U.toScheme))).app a).exact
              (0 + 1) z)))))) := by
  let : CompactSpace (space (op (Over.mk (toIntegerBase U.toScheme)), a)) :=
    compactSpace_space (op (Over.mk (toIntegerBase U.toScheme)), a)
  let : CompactSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
    compactSpace_space (op (Over.mk (toIntegerBase Q)), a)
  let : QuasiSeparatedSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
    quasiSeparatedSpace_space (op (Over.mk (toIntegerBase Q)), a)
  have h := basicSpecConnecting_normalizedModelClass_sign Q U a 0 rfl z
  dsimp only at h ⊢
  simpa only [boundedFlatCoefficientSupportedKStableEquiv_zero] using h

end QuillenTest.NormalizedBasicPositiveBoundary
