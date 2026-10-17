/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientConeFunctor
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationConeFunctor
public import Quillen.Waldhausen.SplitComplexes.FactorizationCofiber
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence
public import Quillen.Waldhausen.Additivity.GroupFormula

/-!
# Global native coefficient-cone additivity

The actual coordinate, its literal factorization middle object and its original signed cone
form a cofibration sequence of exact functors. The weak middle projection proves that the
support-forgotten cone K-map is identity times inverse native negative tensor in every degree.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex Quillen.Waldhausen Quillen.Waldhausen.SplitFactorization
open Quillen.Waldhausen.GilletWaldhausen
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
variable (X : QuasiCompactSchemes.{u})

attribute [local instance] nativeNegativeTwist_additive

/-- The exact original left-tensor source of the tautological coefficient transformation. -/
def coefficientTensorFunctor : Perfect (nativeLineFunctor.obj X).obj ⥤ Perfect
  (nativeLineFunctor.obj X).obj :=
  perfectTensorByLine (nativeTautologicalLine X)
    (fun _ : Bool => (Relative.polynomialFunctor.obj X).obj) (nativeChart X)
    (nativeChart_cover X) (nativeLineChartIso X)

/-- Left tensor preserves the same inherited exact structure. -/
def coefficientTensorExactFunctor :
    ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex
        (nativeLineFunctor.obj X).obj.Modules ℤ))
        (locallyPerfect (nativeLineFunctor.obj X).obj))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex
        (nativeLineFunctor.obj X).obj.Modules ℤ))
        (locallyPerfect (nativeLineFunctor.obj X).obj)) :=
  perfectExactTensorByLine (nativeTautologicalLine X)
    (fun _ : Bool => (Relative.polynomialFunctor.obj X).obj) (nativeChart X)
    (nativeChart_cover X) (nativeLineChartIso X)

/-- The tensor map has the original fine Waldhausen exactness witness. -/
theorem coefficientTensorFunctor_waldhausenExact :
    IsExact (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq (coefficientTensorFunctor X) :=
  perfectTensorByLine_waldhausenExact _ _ _ _ _

/-- The actual supported cone followed by its original support-forgetting inclusion. -/
def coefficientForgottenConeFunctor :
    Perfect (nativeLineFunctor.obj X).obj ⥤ Perfect (nativeLineFunctor.obj X).obj :=
  coefficientConeFunctor X ⋙
    ObjectProperty.ιOfLE (show perfectSupported (positiveOpen X).ι ≤ locallyPerfect
      (nativeLineFunctor.obj X).obj
      from fun _ h => h.1)

instance coefficientForgottenConeFunctor_additive :
    (coefficientForgottenConeFunctor X).Additive := by
  unfold coefficientForgottenConeFunctor
  infer_instance

/-- Forgetting support retains every original inherited conflation of the signed cone. -/
def coefficientForgottenConeExactFunctor :
    ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex
        (nativeLineFunctor.obj X).obj.Modules ℤ))
        (locallyPerfect (nativeLineFunctor.obj X).obj))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex
        (nativeLineFunctor.obj X).obj.Modules ℤ))
        (locallyPerfect (nativeLineFunctor.obj X).obj)) where
  toFunctor := coefficientForgottenConeFunctor X
  map_conflation S hS := (coefficientConeExactFunctor X).map_conflation S hS

/-- The original supported exact functor and actual inclusion give fine exactness. -/
theorem coefficientForgottenConeFunctor_waldhausenExact :
    IsExact (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq (coefficientForgottenConeFunctor X) :=
  (coefficientConeFunctor_waldhausenExact X).comp
    (subcategoryInclusion_exact (perfectSupported (positiveOpen X).ι) (locallyPerfect
      (nativeLineFunctor.obj X).obj)
      (fun _ h => h.1))

/-- The literal original factorization middle object on every coefficient and arrow. -/
def coefficientMiddleFunctor :
    Perfect (nativeLineFunctor.obj X).obj ⥤ Perfect (nativeLineFunctor.obj X).obj :=
  (locallyPerfect (nativeLineFunctor.obj X).obj).lift
    (middleNatTransFunctor (Functor.whiskerRight (coefficientPerfectTransformation X)
      (locallyPerfect (nativeLineFunctor.obj X).obj).ι))
    (fun K => middle_property (locallyPerfect (nativeLineFunctor.obj X).obj)
      (fun hA hB f => locallyPerfect_mappingCone hA hB f)
      ((coefficientTensorFunctor X).obj K).property K.property
      (coefficientPerfectCoordinate X K).hom)

/-- The original first factor, now natural in every perfect coefficient. -/
def coefficientInclusionNat :
    coefficientTensorFunctor X ⟶ coefficientMiddleFunctor X where
  app K := (locallyPerfect (nativeLineFunctor.obj X).obj).homMk
    (inclusion (coefficientPerfectCoordinate X K).hom)
  naturality _ _ g := ObjectProperty.hom_ext _
    ((inclusionNatTrans (Functor.whiskerRight (coefficientPerfectTransformation X)
      (locallyPerfect (nativeLineFunctor.obj X).obj).ι)).naturality g)

/-- The unchanged weak projection to the original coefficient. -/
def coefficientProjectionNat :
    coefficientMiddleFunctor X ⟶ 𝟭 (Perfect (nativeLineFunctor.obj X).obj) where
  app K := (locallyPerfect (nativeLineFunctor.obj X).obj).homMk
    (projection (coefficientPerfectCoordinate X K).hom)
  naturality _ _ g := ObjectProperty.hom_ext _
    ((projectionNatTrans (Functor.whiskerRight (coefficientPerfectTransformation X)
      (locallyPerfect (nativeLineFunctor.obj X).obj).ι)).naturality g)

/-- The original sign-adjusted quotient into the literal support-forgotten cone. -/
def coefficientConeProjectionNat :
    coefficientMiddleFunctor X ⟶ coefficientForgottenConeFunctor X where
  app K := (locallyPerfect (nativeLineFunctor.obj X).obj).homMk
    (quotientToCone (coefficientPerfectCoordinate X K).hom)
  naturality _ _ g := ObjectProperty.hom_ext _
    ((quotientToConeNatTrans (Functor.whiskerRight
      (coefficientPerfectTransformation X)
      (locallyPerfect (nativeLineFunctor.obj X).obj).ι)).naturality g)

/-- The two actual factors retain the original tautological coordinate transformation. -/
theorem coefficientInclusionNat_projection :
    coefficientInclusionNat X ≫ coefficientProjectionNat X =
      coefficientPerfectTransformation X := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _
    (inclusion_projection (coefficientPerfectCoordinate X K).hom)

/-- The original first factor and signed quotient compose to zero. -/
theorem coefficientInclusionNat_quotient :
    coefficientInclusionNat X ≫ coefficientConeProjectionNat X = 0 := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _
    (inclusion_quotientToCone (coefficientPerfectCoordinate X K).hom)

instance coefficientMiddleFunctor_additive :
    (coefficientMiddleFunctor X).Additive := by
  unfold coefficientMiddleFunctor
  infer_instance

/-- Actual left-tensor and identity exactness preserve every inherited middle conflation. -/
def coefficientMiddleExactFunctor :
    ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex
        (nativeLineFunctor.obj X).obj.Modules ℤ))
        (locallyPerfect (nativeLineFunctor.obj X).obj))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex
        (nativeLineFunctor.obj X).obj.Modules ℤ))
        (locallyPerfect (nativeLineFunctor.obj X).obj)) where
  toFunctor := coefficientMiddleFunctor X
  map_conflation S hS := middleNatTransFunctor_shortExact
    (Functor.whiskerRight (coefficientPerfectTransformation X)
      (locallyPerfect (nativeLineFunctor.obj X).obj).ι) S
    ((coefficientTensorExactFunctor X).map_conflation S hS) hS

/-- The original middle functor also preserves fine weak maps and actual pushouts. -/
theorem coefficientMiddleFunctor_waldhausenExact :
    IsExact (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq (coefficientMiddleFunctor X) where
  zero h := (coefficientMiddleFunctor X).map_isZero h
  cofibration g hg := (coefficientMiddleExactFunctor X).map_inflation g hg
  weak {K L} g hg := by
    let φ := Arrow.homMk
      (f := Arrow.mk (coefficientPerfectCoordinate X K).hom)
      (g := Arrow.mk (coefficientPerfectCoordinate X L).hom)
      ((coefficientTensorFunctor X).map g).hom g.hom
      ((coefficientCoordinate X).naturality g.hom)
    let : QuasiIso φ.right := hg
    exact middleFunctor_map_quasiIso φ
  pushout hi h := (coefficientMiddleExactFunctor X).map_isPushout hi h

/-- The original signed quotient sequence is an inherited perfect conflation. -/
theorem coefficientConeSequence_conflation (K : Perfect (nativeLineFunctor.obj X).obj) :
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex (nativeLineFunctor.obj
      X).obj.Modules ℤ))
      (locallyPerfect (nativeLineFunctor.obj X).obj)).conflation
      (exactFunctorSequenceAt (coefficientInclusionNat X)
        (coefficientConeProjectionNat X)
        (coefficientInclusionNat_quotient X) K) :=
  quotientToConeSequence_shortExact (coefficientPerfectCoordinate X K).hom

/-- Every first factor is the original inherited cofibration. -/
theorem coefficientInclusionNat_cof (K : Perfect (nativeLineFunctor.obj X).obj) :
    (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof ((coefficientInclusionNat X).app K) :=
  ExtensionCategory.inclusion_cof (perfectWaldhausen (nativeLineFunctor.obj X).obj)
    (subcategoryExtension (locallyPerfect (nativeLineFunctor.obj X).obj)
      (fun hA hB f => locallyPerfect_mappingCone hA hB f)
      (coefficientPerfectCoordinate X K))

/-- Quotient exactness gives the actual relative cofibration on arbitrary inherited inputs. -/
theorem coefficientInclusionNat_cofibration :
    Additivity.IsCofibrationTransformation (perfectWaldhausen (nativeLineFunctor.obj X).obj)
      (coefficientInclusionNat X) (perfectWaldhausen (nativeLineFunctor.obj X).obj) where
  app_cof := coefficientInclusionNat_cof X
  relative_cof {K L} g hg := by
    let E := ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex
      (nativeLineFunctor.obj X).obj.Modules ℤ))
      (locallyPerfect (nativeLineFunctor.obj X).obj)
    let : HasPushout
        (exactFunctorSequenceAt (coefficientInclusionNat X)
          (coefficientConeProjectionNat X)
          (coefficientInclusionNat_quotient X) K).f
        (exactFunctorSequenceMap (coefficientInclusionNat X)
          (coefficientConeProjectionNat X)
          (coefficientInclusionNat_quotient X) g).τ₁ :=
      Additivity.hasPushout (perfectWaldhausen (nativeLineFunctor.obj X).obj)
        (coefficientInclusionNat X) (coefficientInclusionNat_cof X) g
    exact relativePushout_inflation E
      (exactFunctorSequenceMap (coefficientInclusionNat X)
        (coefficientConeProjectionNat X)
        (coefficientInclusionNat_quotient X) g)
      (coefficientConeSequence_conflation X K)
      (coefficientConeSequence_conflation X L)
      ((coefficientForgottenConeExactFunctor X).map_inflation g hg)

/-- The original tautological coordinate has a genuine signed-cone cofibration sequence. -/
theorem coefficientCofibrationSequence :
    Additivity.IsCofibrationSequence (perfectWaldhausen (nativeLineFunctor.obj X).obj)
      (perfectWaldhausen (nativeLineFunctor.obj X).obj) (coefficientInclusionNat X)
      (coefficientConeProjectionNat X) where
  exactF := coefficientTensorFunctor_waldhausenExact X
  exactG := coefficientMiddleFunctor_waldhausenExact X
  exactH := coefficientForgottenConeFunctor_waldhausenExact X
  cofibration := coefficientInclusionNat_cofibration X
  cofiber K := subcategoryCone_isPushout (locallyPerfect (nativeLineFunctor.obj X).obj)
    (fun hA hB f => locallyPerfect_mappingCone hA hB f)
    (coefficientPerfectCoordinate X K)

/-- The same original projection is weak before any restriction or support transport. -/
theorem coefficientProjectionNat_weak (K : Perfect (nativeLineFunctor.obj X).obj) :
    (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq ((coefficientProjectionNat X).app K) :=
  projection_quasiIso (coefficientPerfectCoordinate X K).hom

/-- The exact original tensor K-map, in every connective degree. -/
def coefficientTensorKMap (n : ℕ) :
    PerfectK (nativeLineFunctor.obj X).obj n →* PerfectK (nativeLineFunctor.obj X).obj n :=
  KMap (coefficientTensorFunctor_waldhausenExact X) n

/-- The actual weak projection identifies the original middle K-map with identity. -/
theorem coefficientMiddle_KMap (n : ℕ) :
    KMap (coefficientMiddleFunctor_waldhausenExact X) n =
      MonoidHom.id (PerfectK (nativeLineFunctor.obj X).obj n) := by
  have h := KMap_eq_of_weakNatTrans (coefficientMiddleFunctor_waldhausenExact X)
    (IsExact.id _ _) (coefficientProjectionNat X)
    (coefficientProjectionNat_weak X) n
  exact h.trans (KMap_id _ n)

/-- Support forgetting is precisely the K-map of the original composite cone functor. -/
theorem coefficientForgottenCone_KMap (n : ℕ) :
    (perfectSupportedKMap (positiveOpen X).ι n).comp (coefficientConeKMap X n) =
      KMap (coefficientForgottenConeFunctor_waldhausenExact X) n :=
  KMap_comp_KMap (coefficientConeFunctor_waldhausenExact X)
    (subcategoryInclusion_exact (perfectSupported (positiveOpen X).ι) (locallyPerfect
      (nativeLineFunctor.obj X).obj)
      (fun _ h => h.1)) n

/-- Actual sequence additivity is in the original subobject-then-quotient group order. -/
theorem coefficientConeKMap_mul (n : ℕ) (x : PerfectK (nativeLineFunctor.obj X).obj n) :
    x = coefficientTensorKMap X n x *
      perfectSupportedKMap (positiveOpen X).ι n (coefficientConeKMap X n x) := by
  have h := Additivity.KMap_additivity_mul (perfectWaldhausen (nativeLineFunctor.obj X).obj)
    (perfectWaldhausen (nativeLineFunctor.obj X).obj) (coefficientInclusionNat X)
    (coefficientConeProjectionNat X) (coefficientCofibrationSequence X) n x
  change KMap (coefficientMiddleFunctor_waldhausenExact X) n x =
    coefficientTensorKMap X n x *
      KMap (coefficientForgottenConeFunctor_waldhausenExact X) n x at h
  rw [coefficientMiddle_KMap] at h
  rw [← coefficientForgottenCone_KMap] at h
  exact h

/-- Every original class has the actual cone difference, including arbitrary K-zero classes. -/
theorem coefficientConeKMap_forget (n : ℕ) (x : PerfectK (nativeLineFunctor.obj X).obj n) :
    perfectSupportedKMap (positiveOpen X).ι n (coefficientConeKMap X n x) =
      x * (coefficientTensorKMap X n x)⁻¹ := by
  calc
    _ = (coefficientTensorKMap X n x)⁻¹ *
        (coefficientTensorKMap X n x *
          perfectSupportedKMap (positiveOpen X).ι n (coefficientConeKMap X n x)) := by
      simp only [← mul_assoc, inv_mul_cancel, one_mul]
    _ = (coefficientTensorKMap X n x)⁻¹ * x :=
      congrArg (fun y => (coefficientTensorKMap X n x)⁻¹ * y)
        (coefficientConeKMap_mul X n x).symm
    _ = x * (coefficientTensorKMap X n x)⁻¹ :=
      Additivity.K_mul_comm (perfectWaldhausen (nativeLineFunctor.obj X).obj) n _ _

attribute [local instance] Waldhausen.Additivity.KCommGroup

/-- The full support-forgotten original homomorphism is identity times inverse left tensor. -/
theorem coefficientConeKMap_forget_hom (n : ℕ) :
    (perfectSupportedKMap (positiveOpen X).ι n).comp (coefficientConeKMap X n) =
      MonoidHom.id (PerfectK (nativeLineFunctor.obj X).obj n) *
        (invMonoidHom.comp (coefficientTensorKMap X n)) := by
  ext x
  exact coefficientConeKMap_forget X n x

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
