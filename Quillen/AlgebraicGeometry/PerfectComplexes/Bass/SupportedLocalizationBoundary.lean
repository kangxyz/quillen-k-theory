/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientNegativeLocalizationBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedLocalizationExactness
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization

/-!
# The negative localization sequence of the original open pair

The fixed signed fine boundary is transported through the actual identity-base
projection on both legs of the open pair. It sends the original open group in
degree `-i` to the original supported group in degree `-(i+1)`. Both adjacent
positions are exact for the original restriction and forget maps. At `i = 0`
this extends the original K₀ tail, without imposing surjectivity of restriction.
The positive geometric boundary is not identified with the fine boundary here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.Bass
variable (A : QuasiCompactOpenPairs.{u}) [CompactSpace A.obj.obj.left]

namespace SupportedLocalization

/-- The removed open over the canonical integral base. -/
abbrev localizationSource : Over (Spec (.of (ULift.{u} ℤ))) :=
  Over.mk (toIntegerBase A.obj.obj.left)

/-- The ambient scheme over the canonical integral base. -/
abbrev localizationTarget : Over (Spec (.of (ULift.{u} ℤ))) :=
  Over.mk (toIntegerBase A.obj.obj.right)

/-- The original open arrow over the canonical integral base. -/
def localizationMap : localizationSource A ⟶ localizationTarget A :=
  Over.homMk A.obj.obj.hom (toIntegerBase_naturality A.obj.obj.hom)

local instance localizationSourceCompact : CompactSpace (localizationSource A).left :=
  inferInstanceAs (CompactSpace A.obj.obj.left)

local instance localizationTargetCompact : CompactSpace (localizationTarget A).left :=
  inferInstanceAs (CompactSpace A.obj.obj.right)

local instance localizationMapOpen : IsOpenImmersion (localizationMap A).left := A.obj.property

/-- The identity algebra over the integral base. -/
abbrev identityCoefficient : Under (CommRingCat.of (ULift.{u} ℤ)) :=
  Under.mk (𝟙 _)

/-- Both actual identity projections form an isomorphism of the original open pairs. -/
def identityPairIso :
    ((boundedFlatCoefficientQuasiCompactOpenPairRow (localizationMap A)).obj
      identityCoefficient).unop ≅ A :=
  quasiCompactOpenPairProperty.isoMk (openPairProperty.isoMk
    (Arrow.isoMk (identityProjectionIso (localizationSource A))
      (identityProjectionIso (localizationTarget A))
      (identityProjectionIso_schemeMap (localizationMap A)).symm))

/-- The actual identity projection on the compact removed open. -/
def identityOpenIso :
    ((boundedFlatCoefficientQuasiCompactRow (localizationSource A)).obj
      identityCoefficient).unop ≅ (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) :=
  quasiCompactSchemeProperty.isoMk (identityProjectionIso (localizationSource A))

/-- Original supported groups map along the inverse-direction identity projection square. -/
def identitySupportGroupIso (i : ℕ) :=
  (supportedNegativeKFunctor i).mapIso (identityPairIso A).op

/-- Original ambient groups map along the identity projection. -/
def identityAmbientGroupIso (i : ℕ) :=
  (negativeKFunctor i).mapIso (quasiCompactOpenPairsBase.mapIso (identityPairIso A)).op

/-- Original open groups map along the identity projection. -/
def identityOpenGroupIso (i : ℕ) :=
  (negativeKFunctor i).mapIso (identityOpenIso A).op

omit [CompactSpace A.obj.obj.left] in
/-- The original support forget map retains the identity projection square. -/
theorem identityForget_square (i : ℕ) :
    supportedNegativeKForget A i ≫ (identityAmbientGroupIso A i).hom =
      (identitySupportGroupIso A i).hom ≫
        (supportedNegativeKForgetNat i).app
          ((boundedFlatCoefficientQuasiCompactOpenPairRow (localizationMap A)).obj
            identityCoefficient) :=
  ((supportedNegativeKForgetNat i).naturality (identityPairIso A).hom.op).symm

/-- The original restriction map retains both identity projection legs. -/
theorem identityRestriction_square (i : ℕ) :
    negativeKPullback (ObjectProperty.homMk A.obj.obj.hom :
        (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) i ≫ (identityOpenGroupIso A i).hom =
      (identityAmbientGroupIso A i).hom ≫
        (boundedFlatCoefficientOriginalNegativeKRestriction (localizationMap A) i).app
          identityCoefficient := by
  have hg : (ObjectProperty.homMk (schemeMap (localizationMap A) identityCoefficient) :
      ((boundedFlatCoefficientQuasiCompactRow (localizationSource A)).obj
        identityCoefficient).unop ⟶
      ((boundedFlatCoefficientQuasiCompactRow (localizationTarget A)).obj
        identityCoefficient).unop) ≫ quasiCompactOpenPairsBase.map (identityPairIso A).hom =
      (identityOpenIso A).hom ≫ (ObjectProperty.homMk A.obj.obj.hom :
        (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) := by
    apply ObjectProperty.hom_ext
    exact identityProjectionIso_schemeMap (localizationMap A)
  change (negativeKFunctor i).map _ ≫ (negativeKFunctor i).map _ =
    (negativeKFunctor i).map _ ≫ (negativeKFunctor i).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (negativeKFunctor i).map (congrArg Quiver.Hom.op hg.symm)

end SupportedLocalization
open SupportedLocalization

variable [QuasiSeparatedSpace A.obj.obj.right]

local instance supportedLocalizationTargetQuasiSeparated :
    QuasiSeparatedSpace (localizationTarget A).left :=
  inferInstanceAs (QuasiSeparatedSpace A.obj.obj.right)

attribute [local instance] SupportedLocalization.localizationSourceCompact
  SupportedLocalization.localizationTargetCompact SupportedLocalization.localizationMapOpen

/-- The fixed fine signed boundary on the original groups of the actual open pair. -/
def supportedNegativeLocalizationConnecting (i : ℕ) :
    negativeK (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) i ⟶
      supportedNegativeK A (i + 1) :=
  (identityOpenGroupIso A i).hom ≫
    boundedFlatCoefficientNegativeLocalizationConnecting (localizationMap A) i
      identityCoefficient ≫ (identitySupportGroupIso A (i + 1)).inv

/-- Restriction to the original open is exact before the fixed signed negative boundary. -/
theorem supportedNegativeLocalizationConnecting_exact_open (i : ℕ) :
    Function.Exact
      (negativeKPullback (ObjectProperty.homMk A.obj.obj.hom :
        (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) i)
      (supportedNegativeLocalizationConnecting A i) := by
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (identityAmbientGroupIso A i).addCommGroupIsoToAddEquiv
    (identityOpenGroupIso A i).addCommGroupIsoToAddEquiv
    (identitySupportGroupIso A (i + 1)).addCommGroupIsoToAddEquiv
    (H := boundedFlatCoefficientNegativeLocalizationConnecting_exact_open
      (localizationMap A) i identityCoefficient)
  · ext x
    exact (ConcreteCategory.congr_hom (identityRestriction_square A i) x).symm
  · ext x
    change _ = (identitySupportGroupIso A (i + 1)).hom
      (supportedNegativeLocalizationConnecting A i x)
    simp [supportedNegativeLocalizationConnecting]

/-- The original support-forgetting map is exact after the fixed signed negative boundary. -/
theorem supportedNegativeLocalizationConnecting_exact_supported (i : ℕ) :
    Function.Exact (supportedNegativeLocalizationConnecting A i)
      (supportedNegativeKForget A (i + 1)) := by
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (identityOpenGroupIso A i).addCommGroupIsoToAddEquiv
    (identitySupportGroupIso A (i + 1)).addCommGroupIsoToAddEquiv
    (identityAmbientGroupIso A (i + 1)).addCommGroupIsoToAddEquiv
    (H := boundedFlatCoefficientNegativeLocalizationConnecting_exact_supported
      (localizationMap A) i identityCoefficient)
  · ext x
    change _ = (identitySupportGroupIso A (i + 1)).hom
      (supportedNegativeLocalizationConnecting A i x)
    simp [supportedNegativeLocalizationConnecting]
  · ext x
    exact (ConcreteCategory.congr_hom (identityForget_square A (i + 1)) x).symm

/-- All recurring positions of the original nonpositive localization sequence are exact. -/
theorem supportedNegativeLocalizationLongExactSequence (i : ℕ) :
    Function.Exact
      (negativeKPullback (ObjectProperty.homMk A.obj.obj.hom :
        (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) i)
      (supportedNegativeLocalizationConnecting A i) ∧
    Function.Exact (supportedNegativeLocalizationConnecting A i)
      (supportedNegativeKForget A (i + 1)) ∧
    Function.Exact (supportedNegativeKForget A (i + 1))
      (negativeKPullback (ObjectProperty.homMk A.obj.obj.hom :
        (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) (i + 1)) :=
  ⟨supportedNegativeLocalizationConnecting_exact_open A i,
    supportedNegativeLocalizationConnecting_exact_supported A i,
    supportedNegativeK_localization_exact A (i + 1)⟩

omit [QuasiSeparatedSpace A.obj.obj.right] in
/-- At degree zero the original Bass restriction is the existing connective open restriction. -/
theorem supportedLocalization_restriction_zero (x : Additive (PerfectK A.obj.obj.right 0)) :
    negativeKPullback (ObjectProperty.homMk A.obj.obj.hom :
      (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
        quasiCompactOpenPairsBase.obj A) 0 x =
      Additive.ofMul (perfectKRestrict A.obj.obj.hom 0 x.toMul) := by
  change Additive.ofMul (perfectKPullback A.obj.obj.hom 0 x.toMul) = _
  rw [perfectKPullback_eq_restrict]

/-- The existing positive geometric boundary is exact against the literal original K₀ forget map.
-/
theorem supportedLocalization_positiveBoundary_exact_zero :
    Function.Exact (qcqsPerfectConnectingHom A.obj.obj.hom 0).toAdditive
      (supportedNegativeKForget A 0) := by
  have h := range_qcqsPerfectConnectingHom_eq_ker_perfectSupportedKMap A.obj.obj.hom 0
  intro y
  change perfectSupportedKMap A.obj.obj.hom 0 y.toMul = 1 ↔
    ∃ x : Additive (PerfectK A.obj.obj.left 1),
      Additive.ofMul (qcqsPerfectConnectingHom A.obj.obj.hom 0 x.toMul) = y
  constructor
  · intro hy
    have hm : y.toMul ∈ (qcqsPerfectConnectingHom A.obj.obj.hom 0).range := by
      rw [h]
      exact hy
    obtain ⟨x, hx⟩ := hm
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩
  · rintro ⟨x, rfl⟩
    have hm : qcqsPerfectConnectingHom A.obj.obj.hom 0 x.toMul ∈
        (qcqsPerfectConnectingHom A.obj.obj.hom 0).range := ⟨x.toMul, rfl⟩
    rw [h] at hm
    exact hm

/-- The original connective tail joins the negative sequence at the unchanged K₀ groups. -/
theorem supportedLocalization_zeroTail :
    Function.Exact (qcqsPerfectConnectingHom A.obj.obj.hom 0).toAdditive
      (supportedNegativeKForget A 0) ∧
    Function.Exact (supportedNegativeKForget A 0)
      (negativeKPullback (ObjectProperty.homMk A.obj.obj.hom :
        (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) 0) ∧
    Function.Exact
      (negativeKPullback (ObjectProperty.homMk A.obj.obj.hom :
        (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) 0)
      (supportedNegativeLocalizationConnecting A 0) ∧
    Function.Exact (supportedNegativeLocalizationConnecting A 0)
      (supportedNegativeKForget A 1) :=
  ⟨supportedLocalization_positiveBoundary_exact_zero A,
    supportedNegativeK_localization_exact A 0,
    supportedNegativeLocalizationConnecting_exact_open A 0,
    supportedNegativeLocalizationConnecting_exact_supported A 0⟩

end Quillen.PerfectComplexes.Bass
