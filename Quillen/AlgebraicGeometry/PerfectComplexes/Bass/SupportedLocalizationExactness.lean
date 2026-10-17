/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientNegativeLocalizationExactness
public import Aglib.AlgebraicGeometry.Products.IntegerBase

/-!
# Original supported negative-group localization exactness

For a qcqs ambient scheme and a compact removed open, the original supported
negative-group forget map has image equal to the kernel of the original open
pullback, in every nonpositive degree. The identity-coefficient projection is
lifted through both legs of the actual open pair, so the conclusion retains the
original groups and maps. In degree zero this is the supported K₀ image statement;
no surjectivity onto the open group or choice of connecting map is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.Bass

variable (A : QuasiCompactOpenPairs.{u}) [CompactSpace A.obj.obj.left]
  [QuasiSeparatedSpace A.obj.obj.right]

/-- The original supported negative forget map is exact against the original open pullback. -/
theorem supportedNegativeK_localization_exact (i : ℕ) :
    Function.Exact (supportedNegativeKForget A i)
      (negativeKPullback (ObjectProperty.homMk A.obj.obj.hom :
        (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) i) := by
  let R : CommRingCat.{u} := .of (ULift.{u} ℤ)
  let P : Over (Spec R) := Over.mk (toIntegerBase A.obj.obj.left)
  let Q : Over (Spec R) := Over.mk (toIntegerBase A.obj.obj.right)
  let f : P ⟶ Q := Over.homMk A.obj.obj.hom (toIntegerBase_naturality A.obj.obj.hom)
  let a : Under R := Under.mk (𝟙 R)
  let : IsOpenImmersion f.left := A.obj.property
  let : CompactSpace P.left := inferInstanceAs (CompactSpace A.obj.obj.left)
  let : CompactSpace Q.left := inferInstanceAs (CompactSpace A.obj.obj.right)
  let : QuasiSeparatedSpace Q.left := inferInstanceAs (QuasiSeparatedSpace A.obj.obj.right)
  let ePair : ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop ≅ A :=
    quasiCompactOpenPairProperty.isoMk (openPairProperty.isoMk
      (Arrow.isoMk (identityProjectionIso P) (identityProjectionIso Q)
        (identityProjectionIso_schemeMap f).symm))
  let eOpen : ((boundedFlatCoefficientQuasiCompactRow P).obj a).unop ≅
      (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) :=
    quasiCompactSchemeProperty.isoMk (identityProjectionIso P)
  let eS := (supportedNegativeKFunctor i).map ePair.hom.op
  let eQ := (negativeKFunctor i).map (quasiCompactOpenPairsBase.map ePair.hom).op
  let eP := (negativeKFunctor i).map eOpen.hom.op
  let j := supportedNegativeKForget A i
  let r := negativeKPullback (ObjectProperty.homMk A.obj.obj.hom :
    (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
      quasiCompactOpenPairsBase.obj A) i
  let j' := (supportedNegativeKForgetNat i).app
    ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a)
  let r' := (boundedFlatCoefficientOriginalNegativeKRestriction f i).app a
  have hj : j ≫ eQ = eS ≫ j' :=
    ((supportedNegativeKForgetNat i).naturality ePair.hom.op).symm
  have hg : (ObjectProperty.homMk (schemeMap f a) :
      ((boundedFlatCoefficientQuasiCompactRow P).obj a).unop ⟶
      ((boundedFlatCoefficientQuasiCompactRow Q).obj a).unop) ≫
        quasiCompactOpenPairsBase.map ePair.hom =
      eOpen.hom ≫ (ObjectProperty.homMk A.obj.obj.hom :
        (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) := by
    apply ObjectProperty.hom_ext
    exact identityProjectionIso_schemeMap f
  have hr : r ≫ eP = eQ ≫ r' := by
    change (negativeKFunctor i).map _ ≫ (negativeKFunctor i).map _ =
      (negativeKFunctor i).map _ ≫ (negativeKFunctor i).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (negativeKFunctor i).map (congrArg Quiver.Hom.op hg.symm)
  have he : Function.Exact j' r' :=
    boundedFlatCoefficientSupportedNegativeK_localization_exact f i a
  change Function.Exact j r
  intro y
  constructor
  · intro hy
    have hy' : r' (eQ y) = 0 := by
      calc
        _ = eP (r y) := (ConcreteCategory.congr_hom hr y).symm
        _ = 0 := by rw [hy, map_zero]
    obtain ⟨z, hz⟩ := (he (eQ y)).mp hy'
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso eS).surjective z
    refine ⟨x, (ConcreteCategory.bijective_of_isIso eQ).injective ?_⟩
    exact (ConcreteCategory.congr_hom hj x).trans hz
  · rintro ⟨x, rfl⟩
    apply (ConcreteCategory.bijective_of_isIso eP).injective
    calc
      _ = r' (eQ (j x)) := ConcreteCategory.congr_hom hr (j x)
      _ = r' (j' (eS x)) := congrArg r' (ConcreteCategory.congr_hom hj x)
      _ = 0 := he.apply_apply_eq_zero _
      _ = eP 0 := (map_zero eP.hom).symm

/-- The original supported K₀ classes map onto precisely the kernel of open restriction. -/
theorem supportedKZero_localization_exact :
    Function.Exact (supportedKZeroForget.app (op A))
      (perfectKZeroFunctor.map (ObjectProperty.homMk A.obj.obj.hom :
        (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A).op) :=
  supportedNegativeK_localization_exact A 0

end Quillen.PerfectComplexes.Bass
