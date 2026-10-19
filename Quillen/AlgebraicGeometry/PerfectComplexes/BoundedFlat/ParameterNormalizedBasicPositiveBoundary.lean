/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicPerfectClasses
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientFinePerfectConnecting
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicOriginalBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalizationNaturality

/-!
# Original positive perfect boundaries in the intrinsic normalized basic row

The independently defined basic boundary carries the original perfect boundary
with its explicit negative sign. Both the actual finite normalized Model class
and the inverse-comparison expression for every original perfect class retain
the original stage-zero inclusions and signed-degree cast. Identity coefficients
retain both actual identity projections and the original open-pair pullbacks.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
open GlobalSectionChangeIndex ParameterLaurentTrack
open Quillen.PerfectComplexes.Bass Quillen.PerfectComplexes.Bass.SupportedLocalization
attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace
attribute [local instance] basicOriginalPair_source_compact basicOriginalPair_target_quasiSeparated
attribute [local instance] SupportedLocalization.localizationSourceCompact
  SupportedLocalization.localizationTargetCompact SupportedLocalization.localizationMapOpen

private theorem comparison_cast {E F : LoopPrespectrum.{u}}
    (e : ∀ d : ℤ, stableHomotopyGroup E d ≅ stableHomotopyGroup F d)
    {d k : ℤ} (h : d = k) (x : stableHomotopyGroup E d) :
    (e k).hom (eqToHom (congrArg (stableHomotopyGroup E) h) x) =
      eqToHom (congrArg (stableHomotopyGroup F) h) ((e d).hom x) := by
  subst k
  rfl


private theorem boundary_class_sign {E F S T : LoopPrespectrum.{u}}
    (e : ∀ d : ℤ, stableHomotopyGroup E d ≅ stableHomotopyGroup F d)
    {m k d : ℤ} (κ : m = k)
    (s : stableHomotopyGroup S d ≅ stableHomotopyGroup T d)
    (δ : stableHomotopyGroup E k ⟶ stableHomotopyGroup S d)
    (δf : stableHomotopyGroup F k ⟶ stableHomotopyGroup T d)
    (x : stableHomotopyGroup E m) (y : stableHomotopyGroup F m)
    (z : stableHomotopyGroup T d)
    (hδ : δ ≫ s.hom = (e k).hom ≫ δf)
    (hx : (e m).hom x = y)
    (hs : δf (eqToHom (congrArg (stableHomotopyGroup F) κ) y) = -z) :
    s.hom (δ (eqToHom (congrArg (stableHomotopyGroup E) κ) x)) = -z := by
  have hb := ConcreteCategory.congr_hom hδ
    (eqToHom (congrArg (stableHomotopyGroup E) κ) x)
  simp only [ConcreteCategory.comp_apply] at hb
  have hc := (comparison_cast e κ x).trans
    (congrArg (eqToHom (congrArg (stableHomotopyGroup F) κ)) hx)
  exact hb.trans ((congrArg δf hc).trans hs)

variable (Q : Scheme.{u}) (U : Q.Opens)
  [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U]

/-- Every original perfect class retains its signed boundary under the existing comparisons. -/
theorem basicSpecConnecting_perfectClass_sign
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectK (space (op (Over.mk (toIntegerBase U.toScheme)), a)) (n + 1)) :
    let : CompactSpace (space (op (Over.mk (toIntegerBase U.toScheme)), a)) :=
      compactSpace_space (op (Over.mk (toIntegerBase U.toScheme)), a)
    let : CompactSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
      compactSpace_space (op (Over.mk (toIntegerBase Q)), a)
    let : QuasiSeparatedSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
      quasiSeparatedSpace_space (op (Over.mk (toIntegerBase Q)), a)
    (normalizedFineSupportComparison (basicOverInclusion Q U) a (n : ℤ)).hom
      (basicSpecConnecting Q U a (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          (ParameterTensorNormalizedRowPresentation.ambient U.toScheme (specUnder.obj a))) κ)
        ((normalizedFineAmbientComparison (Over.mk (toIntegerBase U.toScheme)) a
          ((n + 1 : ℕ) : ℤ)).inv
          ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
            ((boundedFlatCoefficientFullOpenBassTelescopeInclusion
              (basicOverInclusion Q U) 0).app a)
            (boundedFlatCoefficientSectionPerfectKStableEquiv
              (op (Over.mk (toIntegerBase U.toScheme)), a) (n + 1)
              (Additive.ofMul x)))))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion (basicOverInclusion Q U) 0).app a)
        (boundedFlatCoefficientSupportedKStableEquiv (basicOverInclusion Q U) a n
          (Additive.ofMul (qcqsPerfectConnectingHom (schemeMap
            (basicOverInclusion Q U) a) n x)))) := by
  let : CompactSpace (space (op (Over.mk (toIntegerBase U.toScheme)), a)) :=
    compactSpace_space (op (Over.mk (toIntegerBase U.toScheme)), a)
  let : CompactSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
    compactSpace_space (op (Over.mk (toIntegerBase Q)), a)
  let : QuasiSeparatedSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
    quasiSeparatedSpace_space (op (Over.mk (toIntegerBase Q)), a)
  dsimp only
  exact boundary_class_sign
    (normalizedFineAmbientComparison (Over.mk (toIntegerBase U.toScheme)) a) κ
    (normalizedFineSupportComparison (basicOverInclusion Q U) a (n : ℤ))
    (basicSpecConnecting Q U a (n : ℤ))
    (boundedFlatCoefficientFineLocalizationConnecting (basicOverInclusion Q U) a (n : ℤ))
    _ _ _ (basicSpecConnecting_fine Q U a (n : ℤ))
    (Iso.inv_hom_id_apply _ _)
    (boundedFlatCoefficientFineConnecting_perfectClass_sign (basicOverInclusion Q U) a n κ x)

/-- The actual finite normalized class retains the original coefficient restriction and boundary. -/
theorem basicSpecConnecting_normalizedModelClass_sign
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (z : ((ParameterModels.ambient U.toScheme).obj (specUnder.obj a)).waldhausen.K (n + 1)) :
    let : CompactSpace (space (op (Over.mk (toIntegerBase U.toScheme)), a)) :=
      compactSpace_space (op (Over.mk (toIntegerBase U.toScheme)), a)
    let : CompactSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
      compactSpace_space (op (Over.mk (toIntegerBase Q)), a)
    let : QuasiSeparatedSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
      quasiSeparatedSpace_space (op (Over.mk (toIntegerBase Q)), a)
    (normalizedFineSupportComparison (basicOverInclusion Q U) a (n : ℤ)).hom
      (basicSpecConnecting Q U a (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          (ParameterTensorNormalizedRowPresentation.ambient U.toScheme (specUnder.obj a))) κ)
        (SchemeModelRowSeed.normalizedModelClass (ParameterModels.ambient U.toScheme)
          (ParameterLaurentUnit.ambientUnit U.toScheme)
          (ParameterLaurentUnit.ambientUnit_naturality U.toScheme)
          (specUnder.obj a) (n + 1) z))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion (basicOverInclusion Q U) 0).app a)
        (boundedFlatCoefficientSupportedKStableEquiv (basicOverInclusion Q U) a n
          (Additive.ofMul (qcqsPerfectConnectingHom (schemeMap (basicOverInclusion Q U) a) n
            (boundedFlatCoefficientSectionPerfectKEquiv
              (op (Over.mk (toIntegerBase U.toScheme)), a) (n + 1)
            (Quillen.Waldhausen.KMap
              ((parameterCoefficientRestriction (Over.mk (toIntegerBase U.toScheme))).app a).exact
              (n + 1) z)))))) := by
  let : CompactSpace (space (op (Over.mk (toIntegerBase U.toScheme)), a)) :=
    compactSpace_space (op (Over.mk (toIntegerBase U.toScheme)), a)
  let : CompactSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
    compactSpace_space (op (Over.mk (toIntegerBase Q)), a)
  let : QuasiSeparatedSpace (space (op (Over.mk (toIntegerBase Q)), a)) :=
    quasiSeparatedSpace_space (op (Over.mk (toIntegerBase Q)), a)
  dsimp only
  exact boundary_class_sign
    (normalizedFineAmbientComparison (Over.mk (toIntegerBase U.toScheme)) a) κ
    (normalizedFineSupportComparison (basicOverInclusion Q U) a (n : ℤ))
    (basicSpecConnecting Q U a (n : ℤ))
    (boundedFlatCoefficientFineLocalizationConnecting (basicOverInclusion Q U) a (n : ℤ))
    _ _ _ (basicSpecConnecting_fine Q U a (n : ℤ))
    (normalized_fine_ambient_perfectClass
      (Over.mk (toIntegerBase U.toScheme)) a (n + 1) z)
    (boundedFlatCoefficientFineConnecting_perfectClass_sign (basicOverInclusion Q U) a n κ
      (boundedFlatCoefficientSectionPerfectKEquiv
        (op (Over.mk (toIntegerBase U.toScheme)), a) (n + 1)
        (Quillen.Waldhausen.KMap
          ((parameterCoefficientRestriction (Over.mk (toIntegerBase U.toScheme))).app a).exact
          (n + 1) z)))

omit [QuasiSeparatedSpace Q] in
/-- The actual identity-base open pair retains compactness of its removed open. -/
theorem basicIdentityPair_source_compact :
    let : CompactSpace (localizationTarget (basicOriginalPair Q U)).left :=
      inferInstanceAs (CompactSpace Q)
    CompactSpace
      (((boundedFlatCoefficientQuasiCompactOpenPairRow
        (localizationMap (basicOriginalPair Q U))).obj identityCoefficient).unop.obj.obj.left) :=
  compactSpace_space (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient)

omit [CompactSpace U] in
/-- The actual identity-base open pair retains quasi-separatedness of its ambient scheme. -/
theorem basicIdentityPair_target_quasiSeparated :
    let : CompactSpace (localizationTarget (basicOriginalPair Q U)).left :=
      inferInstanceAs (CompactSpace Q)
    QuasiSeparatedSpace
      (((boundedFlatCoefficientQuasiCompactOpenPairRow
        (localizationMap (basicOriginalPair Q U))).obj identityCoefficient).unop.obj.obj.right) :=
  quasiSeparatedSpace_space (op (Over.mk (toIntegerBase Q)), identityCoefficient)

attribute [local instance] basicIdentityPair_source_compact basicIdentityPair_target_quasiSeparated

/-- The intrinsic integer-parameter boundary retains the original geometric open-pair boundary. -/
theorem basicConnecting_originalPerfectClass_sign
    (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectK U.toScheme (n + 1)) :
    (normalizedFineSupportComparison (basicOverInclusion Q U) identityCoefficient (n : ℤ)).hom
      (basicConnecting Q U (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          (ParameterTensorNormalizedRowPresentation.ambient U.toScheme
            (specUnder.obj identityCoefficient))) κ)
        ((normalizedFineAmbientComparison (Over.mk (toIntegerBase U.toScheme)) identityCoefficient
          ((n + 1 : ℕ) : ℤ)).inv
          ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
            ((boundedFlatCoefficientFullOpenBassTelescopeInclusion
              (basicOverInclusion Q U) 0).app identityCoefficient)
            (boundedFlatCoefficientSectionPerfectKStableEquiv
              (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient) (n + 1)
              (Additive.ofMul (perfectKPullback (identityPairIso
                (basicOriginalPair Q U)).hom.hom.hom.left (n + 1) x))))))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion
          (basicOverInclusion Q U) 0).app identityCoefficient)
        (boundedFlatCoefficientSupportedKStableEquiv (basicOverInclusion Q U) identityCoefficient n
          (Additive.ofMul (perfectSupportedKPullback (identityPairIso (basicOriginalPair Q U)).hom n
            (qcqsPerfectConnectingHom U.ι n x))))) := by
  let : CompactSpace (space (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient)) :=
    compactSpace_space (op (Over.mk (toIntegerBase U.toScheme)), identityCoefficient)
  let : CompactSpace (space (op (Over.mk (toIntegerBase Q)), identityCoefficient)) :=
    compactSpace_space (op (Over.mk (toIntegerBase Q)), identityCoefficient)
  let : QuasiSeparatedSpace (space (op (Over.mk (toIntegerBase Q)), identityCoefficient)) :=
    quasiSeparatedSpace_space (op (Over.mk (toIntegerBase Q)), identityCoefficient)
  have hn := DFunLike.congr_fun
    (qcqsPerfectConnectingHom_pullback (identityPairIso (basicOriginalPair Q U)).hom n) x
  change perfectSupportedKPullback (identityPairIso (basicOriginalPair Q U)).hom n
      (qcqsPerfectConnectingHom U.ι n x) =
    qcqsPerfectConnectingHom (schemeMap (basicOverInclusion Q U) identityCoefficient) n
      (perfectKPullback (identityPairIso (basicOriginalPair Q U)).hom.hom.hom.left
        (n + 1) x) at hn
  have hb := basicSpecConnecting_perfectClass_sign Q U identityCoefficient n κ (perfectKPullback
    (identityPairIso (basicOriginalPair Q U)).hom.hom.hom.left (n + 1) x)
  dsimp only at hb
  exact hb.trans (congrArg (fun y =>
    -((stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientSupportedBassTelescopeInclusion
        (basicOverInclusion Q U) 0).app identityCoefficient)
      (boundedFlatCoefficientSupportedKStableEquiv (basicOverInclusion Q U)
        identityCoefficient n (Additive.ofMul y)))) hn.symm)

end Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
