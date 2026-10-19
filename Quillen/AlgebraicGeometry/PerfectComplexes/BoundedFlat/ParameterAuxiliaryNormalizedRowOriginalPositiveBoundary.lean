/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowPositiveBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryPerfectBoundaryProjection
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicSpec
public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedLocalizationBoundary

/-!
# Original geometric positive boundaries in the normalized auxiliary row

The original supported perfect boundary maps to the intrinsic normalized row
boundary under both actual coefficient projections, retaining the inverse-image
and union-support pair pullbacks and the explicit negative stabilization sign.
The canonical integral-base open inclusion specializes this formula at identity
coefficients without identifying either projection with an identity morphism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.ParameterAuxiliaryNormalizedRowLocalization
open GlobalSectionChangeIndex ParameterAuxiliarySupport
open ParameterNormalizedBasicLocalization Quillen.PerfectComplexes.Bass.SupportedLocalization

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- Both original projection pullbacks preserve the intrinsic normalized boundary and sign. -/
theorem normalizedPresentationConnecting_originalPerfectClass_sign
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectSupportedK (f.left ⁻¹ᵁ T).ι (n + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    (normalizedFineSupportComparison f T a (n : ℤ)).hom
      (normalizedPresentationConnecting f T a (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
            (specUnder.obj a))) κ)
          ((normalizedFineOpenComparison f T a ((n + 1 : ℕ) : ℤ)).inv
            ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
              ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
              (auxiliaryOpenPerfectStableEquiv f T a (n + 1)
                (Additive.ofMul (perfectSupportedKPullback
                  (qcSupportedBaseSquare (supportedPairTargetSquare (schemeMap f a) f.left
                    (supportRestrictionPair (projection (op Q, a)) T)
                    (projection (op P, a)) (schemeMap_projection f a))) (n + 1) x))))))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (auxiliaryFiberPerfectStableEquiv f T a n
          (Additive.ofMul (perfectSupportedKPullback
            (qcSupportedBaseSquare (supportedPairUnionSquare (schemeMap f a) f.left
              (supportRestrictionPair (projection (op Q, a)) T)
              (projection (op P, a)) (schemeMap_projection f a))) n
            (qcqsPerfectSupportedConnectingHom f.left T
              (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T))) n x))))) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  have hs := normalizedPresentationConnecting_perfectClass_sign f T a n κ
    (perfectSupportedKPullback
      (qcSupportedBaseSquare (supportedPairTargetSquare (schemeMap f a) f.left
        (supportRestrictionPair (projection (op Q, a)) T)
        (projection (op P, a)) (schemeMap_projection f a))) (n + 1) x)
  have hp := boundedFlatCoefficientAuxiliaryPerfectConnecting_projection f T a n x
  dsimp only at hs hp ⊢
  exact hs.trans (congrArg (fun y => -((stableHomotopyFunctor (n : ℤ)).map
    ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
    (auxiliaryFiberPerfectStableEquiv f T a n (Additive.ofMul y)))) hp.symm)

attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace

/-- Identity coefficients retain the original supported boundary and both projections. -/
theorem normalizedPresentationConnecting_identity_originalPerfectClass_sign
    (X : Scheme.{u}) (U T : X.Opens)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U] [CompactSpace T]
    (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectSupportedK (U.ι ⁻¹ᵁ T).ι (n + 1)) :
    let : CompactSpace (space (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient)) :=
      compactSpace_space (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient)
    let : CompactSpace (space (op (Over.mk (toIntegerBase X)), identityCoefficient)) :=
      compactSpace_space (op (Over.mk (toIntegerBase X)), identityCoefficient)
    let : QuasiSeparatedSpace (space (op (Over.mk (toIntegerBase X)), identityCoefficient)) :=
      quasiSeparatedSpace_space (op (Over.mk (toIntegerBase X)), identityCoefficient)
    (normalizedFineSupportComparison (basicOverInclusion X U) T identityCoefficient (n : ℤ)).hom
      (normalizedPresentationConnecting (basicOverInclusion X U) T identityCoefficient (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          (ParameterTensorNormalizedRowPresentation.supported (inverseOpen U.ι T).ι
            (specUnder.obj identityCoefficient))) κ)
          ((normalizedFineOpenComparison (basicOverInclusion X U) T identityCoefficient
            ((n + 1 : ℕ) : ℤ)).inv
            ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
              ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion
                (basicOverInclusion X U) T 0).app identityCoefficient)
              (auxiliaryOpenPerfectStableEquiv (basicOverInclusion X U) T identityCoefficient
                (n + 1) (Additive.ofMul (perfectSupportedKPullback
                  (qcSupportedBaseSquare (supportedPairTargetSquare
                    (schemeMap (basicOverInclusion X U) identityCoefficient) U.ι
                    (supportRestrictionPair
                      (projection (op (Over.mk (toIntegerBase X)), identityCoefficient)) T)
                    (projection (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient))
                    (schemeMap_projection (basicOverInclusion X U) identityCoefficient)))
                  (n + 1) x))))))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion
          (basicOverInclusion X U) T 0).app identityCoefficient)
        (auxiliaryFiberPerfectStableEquiv (basicOverInclusion X U) T identityCoefficient n
          (Additive.ofMul (perfectSupportedKPullback
            (qcSupportedBaseSquare (supportedPairUnionSquare
              (schemeMap (basicOverInclusion X U) identityCoefficient) U.ι
              (supportRestrictionPair
                (projection (op (Over.mk (toIntegerBase X)), identityCoefficient)) T)
              (projection (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient))
              (schemeMap_projection (basicOverInclusion X U) identityCoefficient))) n
            (qcqsPerfectSupportedConnectingHom U.ι T
              (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T))) n x))))) :=
  normalizedPresentationConnecting_originalPerfectClass_sign
    (basicOverInclusion X U) T identityCoefficient n κ x

end Quillen.PerfectComplexes.ParameterAuxiliaryNormalizedRowLocalization
