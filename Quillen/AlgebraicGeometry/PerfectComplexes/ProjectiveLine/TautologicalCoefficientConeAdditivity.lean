/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineTensor

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoefficientConeFunctor
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationConeFunctor
public import Quillen.Waldhausen.SplitComplexes.FactorizationCofiber
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# Additivity of the original tautological coefficient cone in every degree

The original first coordinate, its literal factorization middle object and the signed cone
quotient form a genuine cofibration sequence of exact functors on perfect complexes. The actual
weak projection from the middle to the identity gives the original support-forgotten cone map
as identity times inverse left-tensor, in every connective degree including zero.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex Quillen.Waldhausen Quillen.Waldhausen.SplitFactorization
open Quillen.Waldhausen.GilletWaldhausen
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
variable (R : CommRingCat.{u})

/-- The exact original left-tensor source of the tautological coefficient transformation. -/
def tautologicalCoefficientTensorFunctor : Perfect (twoChartLine R) ⥤ Perfect (twoChartLine R) :=
  perfectTensorByLine (tautologicalLine R)
    (fun _ : Bool => Spec (.of (Polynomial R))) (polynomialChart R)
    (polynomialChart_cover R) (fun b => by
      cases b
      · exact tautologicalLineMinusIso R
      · exact tautologicalLinePlusIso R)

/-- Left tensor preserves the same inherited exact structure. -/
def tautologicalCoefficientTensorExactFunctor :
    ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure
        (CochainComplex (twoChartLine R).Modules ℤ))
        (locallyPerfect (twoChartLine R)))
      (ExactSubcategory.exactStructure (abelianExactStructure
        (CochainComplex (twoChartLine R).Modules ℤ))
        (locallyPerfect (twoChartLine R))) :=
  perfectExactTensorByLine (tautologicalLine R)
    (fun _ : Bool => Spec (.of (Polynomial R))) (polynomialChart R)
    (polynomialChart_cover R) (fun b => by
      cases b
      · exact tautologicalLineMinusIso R
      · exact tautologicalLinePlusIso R)

/-- The tensor map has the original fine Waldhausen exactness witness. -/
theorem tautologicalCoefficientTensorFunctor_waldhausenExact :
    IsExact (perfectWaldhausen (twoChartLine R)).cof
      (perfectWaldhausen (twoChartLine R)).weq
      (perfectWaldhausen (twoChartLine R)).cof
      (perfectWaldhausen (twoChartLine R)).weq (tautologicalCoefficientTensorFunctor R) :=
  perfectTensorByLine_waldhausenExact _ _ _ _ _

/-- The actual supported cone followed by its original support-forgetting inclusion. -/
def tautologicalCoefficientForgottenConeFunctor :
    Perfect (twoChartLine R) ⥤ Perfect (twoChartLine R) :=
  tautologicalCoefficientConeFunctor R ⋙
    ObjectProperty.ιOfLE (show perfectSupported (plusChart R) ≤ locallyPerfect (twoChartLine R)
      from fun _ h => h.1)

instance tautologicalCoefficientForgottenConeFunctor_additive :
    (tautologicalCoefficientForgottenConeFunctor R).Additive := by
  unfold tautologicalCoefficientForgottenConeFunctor
  infer_instance

/-- Forgetting support retains every original inherited conflation of the signed cone. -/
def tautologicalCoefficientForgottenConeExactFunctor :
    ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure
        (CochainComplex (twoChartLine R).Modules ℤ))
        (locallyPerfect (twoChartLine R)))
      (ExactSubcategory.exactStructure (abelianExactStructure
        (CochainComplex (twoChartLine R).Modules ℤ))
        (locallyPerfect (twoChartLine R))) where
  toFunctor := tautologicalCoefficientForgottenConeFunctor R
  map_conflation S hS := (tautologicalCoefficientConeExactFunctor R).map_conflation S hS

/-- The original supported exact functor and actual inclusion give fine exactness. -/
theorem tautologicalCoefficientForgottenConeFunctor_waldhausenExact :
    IsExact (perfectWaldhausen (twoChartLine R)).cof
      (perfectWaldhausen (twoChartLine R)).weq
      (perfectWaldhausen (twoChartLine R)).cof
      (perfectWaldhausen (twoChartLine R)).weq (tautologicalCoefficientForgottenConeFunctor R) :=
  (tautologicalCoefficientConeFunctor_waldhausenExact R).comp
    (subcategoryInclusion_exact (perfectSupported (plusChart R)) (locallyPerfect (twoChartLine R))
      (fun _ h => h.1))

/-- The literal original factorization middle object on every coefficient and arrow. -/
def tautologicalCoefficientMiddleFunctor :
    Perfect (twoChartLine R) ⥤ Perfect (twoChartLine R) :=
  (locallyPerfect (twoChartLine R)).lift
    (middleNatTransFunctor (Functor.whiskerRight (tautologicalCoefficientPerfectTransformation R)
      (locallyPerfect (twoChartLine R)).ι))
    (fun K => middle_property (locallyPerfect (twoChartLine R))
      (fun hA hB f => locallyPerfect_mappingCone hA hB f)
      ((tautologicalCoefficientTensorFunctor R).obj K).property K.property
      (tautologicalCoefficientPerfectCoordinate R K).hom)

/-- The original first factor, now natural in every perfect coefficient. -/
def tautologicalCoefficientInclusionNat :
    tautologicalCoefficientTensorFunctor R ⟶ tautologicalCoefficientMiddleFunctor R where
  app K := (locallyPerfect (twoChartLine R)).homMk
    (inclusion (tautologicalCoefficientPerfectCoordinate R K).hom)
  naturality _ _ g := ObjectProperty.hom_ext _
    ((inclusionNatTrans (Functor.whiskerRight (tautologicalCoefficientPerfectTransformation R)
      (locallyPerfect (twoChartLine R)).ι)).naturality g)

/-- The unchanged weak projection to the original coefficient. -/
def tautologicalCoefficientProjectionNat :
    tautologicalCoefficientMiddleFunctor R ⟶ 𝟭 (Perfect (twoChartLine R)) where
  app K := (locallyPerfect (twoChartLine R)).homMk
    (projection (tautologicalCoefficientPerfectCoordinate R K).hom)
  naturality _ _ g := ObjectProperty.hom_ext _
    ((projectionNatTrans (Functor.whiskerRight (tautologicalCoefficientPerfectTransformation R)
      (locallyPerfect (twoChartLine R)).ι)).naturality g)

/-- The original sign-adjusted quotient into the literal support-forgotten cone. -/
def tautologicalCoefficientConeProjectionNat :
    tautologicalCoefficientMiddleFunctor R ⟶ tautologicalCoefficientForgottenConeFunctor R where
  app K := (locallyPerfect (twoChartLine R)).homMk
    (quotientToCone (tautologicalCoefficientPerfectCoordinate R K).hom)
  naturality _ _ g := ObjectProperty.hom_ext _
    ((quotientToConeNatTrans (Functor.whiskerRight
      (tautologicalCoefficientPerfectTransformation R)
      (locallyPerfect (twoChartLine R)).ι)).naturality g)

/-- The two actual factors retain the original tautological coordinate transformation. -/
theorem tautologicalCoefficientInclusionNat_projection :
    tautologicalCoefficientInclusionNat R ≫ tautologicalCoefficientProjectionNat R =
      tautologicalCoefficientPerfectTransformation R := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _
    (inclusion_projection (tautologicalCoefficientPerfectCoordinate R K).hom)

/-- The original first factor and signed quotient compose to zero. -/
theorem tautologicalCoefficientInclusionNat_quotient :
    tautologicalCoefficientInclusionNat R ≫ tautologicalCoefficientConeProjectionNat R = 0 := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _
    (inclusion_quotientToCone (tautologicalCoefficientPerfectCoordinate R K).hom)

instance tautologicalCoefficientMiddleFunctor_additive :
    (tautologicalCoefficientMiddleFunctor R).Additive := by
  unfold tautologicalCoefficientMiddleFunctor
  infer_instance

/-- Actual left-tensor and identity exactness preserve every inherited middle conflation. -/
def tautologicalCoefficientMiddleExactFunctor :
    ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure
        (CochainComplex (twoChartLine R).Modules ℤ))
        (locallyPerfect (twoChartLine R)))
      (ExactSubcategory.exactStructure (abelianExactStructure
        (CochainComplex (twoChartLine R).Modules ℤ))
        (locallyPerfect (twoChartLine R))) where
  toFunctor := tautologicalCoefficientMiddleFunctor R
  map_conflation S hS := middleNatTransFunctor_shortExact
    (Functor.whiskerRight (tautologicalCoefficientPerfectTransformation R)
      (locallyPerfect (twoChartLine R)).ι) S
    ((tautologicalCoefficientTensorExactFunctor R).map_conflation S hS) hS

/-- The original middle functor also preserves fine weak maps and actual pushouts. -/
theorem tautologicalCoefficientMiddleFunctor_waldhausenExact :
    IsExact (perfectWaldhausen (twoChartLine R)).cof
      (perfectWaldhausen (twoChartLine R)).weq
      (perfectWaldhausen (twoChartLine R)).cof
      (perfectWaldhausen (twoChartLine R)).weq (tautologicalCoefficientMiddleFunctor R) where
  zero h := (tautologicalCoefficientMiddleFunctor R).map_isZero h
  cofibration g hg := (tautologicalCoefficientMiddleExactFunctor R).map_inflation g hg
  weak {K L} g hg := by
    let φ := Arrow.homMk
      (f := Arrow.mk (tautologicalCoefficientPerfectCoordinate R K).hom)
      (g := Arrow.mk (tautologicalCoefficientPerfectCoordinate R L).hom)
      ((tautologicalCoefficientTensorFunctor R).map g).hom g.hom
      ((tautologicalCoefficientCoordinate R).naturality g.hom)
    let : QuasiIso φ.right := hg
    exact middleFunctor_map_quasiIso φ
  pushout hi h := (tautologicalCoefficientMiddleExactFunctor R).map_isPushout hi h

/-- The original signed quotient sequence is an inherited perfect conflation. -/
theorem tautologicalCoefficientConeSequence_conflation (K : Perfect (twoChartLine R)) :
    (ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex (twoChartLine R).Modules ℤ))
      (locallyPerfect (twoChartLine R))).conflation
      (exactFunctorSequenceAt (tautologicalCoefficientInclusionNat R)
        (tautologicalCoefficientConeProjectionNat R)
        (tautologicalCoefficientInclusionNat_quotient R) K) :=
  quotientToConeSequence_shortExact (tautologicalCoefficientPerfectCoordinate R K).hom

/-- Every first factor is the original inherited cofibration. -/
theorem tautologicalCoefficientInclusionNat_cof (K : Perfect (twoChartLine R)) :
    (perfectWaldhausen (twoChartLine R)).cof ((tautologicalCoefficientInclusionNat R).app K) :=
  ExtensionCategory.inclusion_cof (perfectWaldhausen (twoChartLine R))
    (subcategoryExtension (locallyPerfect (twoChartLine R))
      (fun hA hB f => locallyPerfect_mappingCone hA hB f)
      (tautologicalCoefficientPerfectCoordinate R K))

/-- Quotient exactness gives the actual relative cofibration on arbitrary inherited inputs. -/
theorem tautologicalCoefficientInclusionNat_cofibration :
    Additivity.IsCofibrationTransformation (perfectWaldhausen (twoChartLine R))
      (tautologicalCoefficientInclusionNat R) (perfectWaldhausen (twoChartLine R)) where
  app_cof := tautologicalCoefficientInclusionNat_cof R
  relative_cof {K L} g hg := by
    let E := ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex (twoChartLine R).Modules ℤ))
      (locallyPerfect (twoChartLine R))
    let : HasPushout
        (exactFunctorSequenceAt (tautologicalCoefficientInclusionNat R)
          (tautologicalCoefficientConeProjectionNat R)
          (tautologicalCoefficientInclusionNat_quotient R) K).f
        (exactFunctorSequenceMap (tautologicalCoefficientInclusionNat R)
          (tautologicalCoefficientConeProjectionNat R)
          (tautologicalCoefficientInclusionNat_quotient R) g).τ₁ :=
      Additivity.hasPushout (perfectWaldhausen (twoChartLine R))
        (tautologicalCoefficientInclusionNat R) (tautologicalCoefficientInclusionNat_cof R) g
    exact relativePushout_inflation E
      (exactFunctorSequenceMap (tautologicalCoefficientInclusionNat R)
        (tautologicalCoefficientConeProjectionNat R)
        (tautologicalCoefficientInclusionNat_quotient R) g)
      (tautologicalCoefficientConeSequence_conflation R K)
      (tautologicalCoefficientConeSequence_conflation R L)
      ((tautologicalCoefficientForgottenConeExactFunctor R).map_inflation g hg)

/-- The original tautological coordinate has a genuine signed-cone cofibration sequence. -/
theorem tautologicalCoefficientCofibrationSequence :
    Additivity.IsCofibrationSequence (perfectWaldhausen (twoChartLine R))
      (perfectWaldhausen (twoChartLine R)) (tautologicalCoefficientInclusionNat R)
      (tautologicalCoefficientConeProjectionNat R) where
  exactF := tautologicalCoefficientTensorFunctor_waldhausenExact R
  exactG := tautologicalCoefficientMiddleFunctor_waldhausenExact R
  exactH := tautologicalCoefficientForgottenConeFunctor_waldhausenExact R
  cofibration := tautologicalCoefficientInclusionNat_cofibration R
  cofiber K := subcategoryCone_isPushout (locallyPerfect (twoChartLine R))
    (fun hA hB f => locallyPerfect_mappingCone hA hB f)
    (tautologicalCoefficientPerfectCoordinate R K)

/-- The same original projection is weak before any restriction or support transport. -/
theorem tautologicalCoefficientProjectionNat_weak (K : Perfect (twoChartLine R)) :
    (perfectWaldhausen (twoChartLine R)).weq ((tautologicalCoefficientProjectionNat R).app K) :=
  projection_quasiIso (tautologicalCoefficientPerfectCoordinate R K).hom

/-- The exact original tensor K-map, in every connective degree. -/
def tautologicalCoefficientTensorKMap (n : ℕ) :
    PerfectK (twoChartLine R) n →* PerfectK (twoChartLine R) n :=
  KMap (tautologicalCoefficientTensorFunctor_waldhausenExact R) n

/-- The actual weak projection identifies the original middle K-map with identity. -/
theorem tautologicalCoefficientMiddle_KMap (n : ℕ) :
    KMap (tautologicalCoefficientMiddleFunctor_waldhausenExact R) n =
      MonoidHom.id (PerfectK (twoChartLine R) n) := by
  have h := KMap_eq_of_weakNatTrans (tautologicalCoefficientMiddleFunctor_waldhausenExact R)
    (IsExact.id _ _) (tautologicalCoefficientProjectionNat R)
    (tautologicalCoefficientProjectionNat_weak R) n
  exact h.trans (KMap_id _ n)

/-- Support forgetting is precisely the K-map of the original composite cone functor. -/
theorem tautologicalCoefficientForgottenCone_KMap (n : ℕ) :
    (perfectSupportedKMap (plusChart R) n).comp (tautologicalCoefficientConeKMap R n) =
      KMap (tautologicalCoefficientForgottenConeFunctor_waldhausenExact R) n :=
  KMap_comp_KMap (tautologicalCoefficientConeFunctor_waldhausenExact R)
    (subcategoryInclusion_exact (perfectSupported (plusChart R)) (locallyPerfect (twoChartLine R))
      (fun _ h => h.1)) n

/-- Actual sequence additivity is in the original subobject-then-quotient group order. -/
theorem tautologicalCoefficientConeKMap_mul (n : ℕ) (x : PerfectK (twoChartLine R) n) :
    x = tautologicalCoefficientTensorKMap R n x *
      perfectSupportedKMap (plusChart R) n (tautologicalCoefficientConeKMap R n x) := by
  have h := Additivity.KMap_additivity_mul (perfectWaldhausen (twoChartLine R))
    (perfectWaldhausen (twoChartLine R)) (tautologicalCoefficientInclusionNat R)
    (tautologicalCoefficientConeProjectionNat R) (tautologicalCoefficientCofibrationSequence R) n x
  change KMap (tautologicalCoefficientMiddleFunctor_waldhausenExact R) n x =
    tautologicalCoefficientTensorKMap R n x *
      KMap (tautologicalCoefficientForgottenConeFunctor_waldhausenExact R) n x at h
  rw [tautologicalCoefficientMiddle_KMap] at h
  rw [← tautologicalCoefficientForgottenCone_KMap] at h
  exact h

/-- Every original class has the actual cone difference, including arbitrary K-zero classes. -/
theorem tautologicalCoefficientConeKMap_forget (n : ℕ) (x : PerfectK (twoChartLine R) n) :
    perfectSupportedKMap (plusChart R) n (tautologicalCoefficientConeKMap R n x) =
      x * (tautologicalCoefficientTensorKMap R n x)⁻¹ := by
  calc
    _ = (tautologicalCoefficientTensorKMap R n x)⁻¹ *
        (tautologicalCoefficientTensorKMap R n x *
          perfectSupportedKMap (plusChart R) n (tautologicalCoefficientConeKMap R n x)) := by
      simp only [← mul_assoc, inv_mul_cancel, one_mul]
    _ = (tautologicalCoefficientTensorKMap R n x)⁻¹ * x :=
      congrArg (fun y => (tautologicalCoefficientTensorKMap R n x)⁻¹ * y)
        (tautologicalCoefficientConeKMap_mul R n x).symm
    _ = x * (tautologicalCoefficientTensorKMap R n x)⁻¹ :=
      Additivity.K_mul_comm (perfectWaldhausen (twoChartLine R)) n _ _

/-- The commutative group structure on the original perfect K-group supplied by additivity. -/
local instance (n : ℕ) : CommGroup (PerfectK (twoChartLine R) n) :=
  Additivity.KCommGroup (perfectWaldhausen (twoChartLine R)) n

/-- The full support-forgotten original homomorphism is identity times inverse left tensor. -/
theorem tautologicalCoefficientConeKMap_forget_hom (n : ℕ) :
    (perfectSupportedKMap (plusChart R) n).comp (tautologicalCoefficientConeKMap R n) =
      MonoidHom.id (PerfectK (twoChartLine R) n) *
        (invMonoidHom.comp (tautologicalCoefficientTensorKMap R n)) := by
  ext x
  exact tautologicalCoefficientConeKMap_forget R n x

end Quillen.PerfectComplexes.ProjectiveLine
