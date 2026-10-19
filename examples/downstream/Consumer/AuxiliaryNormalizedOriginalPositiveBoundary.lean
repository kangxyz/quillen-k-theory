/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowOriginalPositiveBoundary

/-!
The canonical open-scheme specialization annihilates original ambient supported
restrictions while retaining both actual identity-coefficient projections.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes ParameterAuxiliaryNormalizedRowLocalization
open GlobalSectionChangeIndex ParameterAuxiliarySupport ParameterNormalizedBasicLocalization
open Quillen.PerfectComplexes.Bass.SupportedLocalization
universe u
namespace Consumer.AuxiliaryNormalizedOriginalPositiveBoundary

private theorem zero_of_signed_image {A B : AddCommGrpCat.{u}} {C : Type*} [One C]
    (s : A ≅ B) (a : A) (g : C → B) (c : C)
    (h : s.hom a = -g c) (hg : g 1 = 0) (hc : c = 1) : a = 0 := by
  apply (ConcreteCategory.bijective_of_isIso s.hom).injective
  calc
    s.hom a = -g c := h
    _ = 0 := by rw [hc, hg, neg_zero]
    _ = s.hom 0 := (map_zero _).symm

attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace

/-- Original ambient supported restriction vanishes under the canonical normalized boundary. -/
theorem normalized_identity_originalSupportedRestriction_eq_zero
    (X : Scheme.{u}) (U T : X.Opens)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U] [CompactSpace T]
    (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectSupportedK T.ι (n + 1)) :
    let : CompactSpace (space (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient)) :=
      compactSpace_space (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient)
    let : CompactSpace (space (op (Over.mk (toIntegerBase X)), identityCoefficient)) :=
      compactSpace_space (op (Over.mk (toIntegerBase X)), identityCoefficient)
    let : QuasiSeparatedSpace (space (op (Over.mk (toIntegerBase X)), identityCoefficient)) :=
      quasiSeparatedSpace_space (op (Over.mk (toIntegerBase X)), identityCoefficient)
    normalizedPresentationConnecting (basicOverInclusion X U) T identityCoefficient (n : ℤ)
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
                (n + 1) (perfectSupportedKRestrict U.ι T (n + 1) x))))))) = 0 := by
  let : CompactSpace (space (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient)) :=
    compactSpace_space (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient)
  let : CompactSpace (space (op (Over.mk (toIntegerBase X)), identityCoefficient)) :=
    compactSpace_space (op (Over.mk (toIntegerBase X)), identityCoefficient)
  let : QuasiSeparatedSpace (space (op (Over.mk (toIntegerBase X)), identityCoefficient)) :=
    quasiSeparatedSpace_space (op (Over.mk (toIntegerBase X)), identityCoefficient)
  have hm : perfectSupportedKRestrict U.ι T (n + 1) x ∈
      (perfectSupportedKRestrict U.ι T (n + 1)).range := ⟨x, rfl⟩
  rw [range_qcqs_perfectSupportedKRestrict_eq_ker_qcqsPerfectSupportedConnectingHom U.ι T
    (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T))) n] at hm
  have hz : qcqsPerfectSupportedConnectingHom U.ι T
      (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T))) n
      (perfectSupportedKRestrict U.ι T (n + 1) x) = 1 := hm
  have h := normalizedPresentationConnecting_identity_originalPerfectClass_sign X U T n κ
    (perfectSupportedKRestrict U.ι T (n + 1) x)
  dsimp only at h ⊢
  exact zero_of_signed_image
    (normalizedFineSupportComparison (basicOverInclusion X U) T identityCoefficient (n : ℤ)) _
    (fun y => (stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion
        (basicOverInclusion X U) T 0).app identityCoefficient)
      (auxiliaryFiberPerfectStableEquiv (basicOverInclusion X U) T identityCoefficient n
        (Additive.ofMul (perfectSupportedKPullback
          (qcSupportedBaseSquare (supportedPairUnionSquare
            (schemeMap (basicOverInclusion X U) identityCoefficient) U.ι
            (supportRestrictionPair
              (projection (op (Over.mk (toIntegerBase X)), identityCoefficient)) T)
            (projection (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient))
            (schemeMap_projection (basicOverInclusion X U) identityCoefficient))) n y)))) _ h
    (by simp only [map_one, ofMul_one, map_zero]) hz

end Consumer.AuxiliaryNormalizedOriginalPositiveBoundary
