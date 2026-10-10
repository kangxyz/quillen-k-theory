/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.ExcisionComplex
public import Quillen.Waldhausen.SConstruction.WeakNaturalTransformationBased

/-!
# Genuine support excision on the original S-construction and K-groups

The original extension-by-zero/restriction adjunction restricts to the
existing supported perfect categories when the image of the immersion and
the auxiliary support open cover the scheme. Both functors are genuinely
exact, and the unchanged unit and counit are weak with literal triangle
identities. Their original S-realization maps are homotopy inverses; their
original K-maps are mutually inverse in every connective degree, including
zero. No quasi-compactness or separation hypothesis is used.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
open Waldhausen
attribute [local instance] Abelian.hasFiniteBiproducts

instance instPreservesFiniteLimitsExtensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  :
    PreservesFiniteLimits (extensionByZero j) := by unfold extensionByZero; infer_instance

instance instPreservesFiniteColimitsExtensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion
  j]
  :
    PreservesFiniteColimits (extensionByZero j) := by unfold extensionByZero; infer_instance

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

/-- Extension by zero on the supported perfect objects under the stated cover condition. -/
def perfectSupportedExtensionByZero : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory ⥤
    (perfectSupported T.ι).FullSubcategory :=
  (perfectSupported T.ι).lift ((perfectSupported (j ⁻¹ᵁ T).ι).ι ⋙ extensionByZero j)
    (fun K => perfectSupported_extensionByZero_of_cover j T hcover K.property)

instance instAdditivePerfectSupportedExtensionByZero : (perfectSupportedExtensionByZero j T
  hcover).Additive := by
  unfold perfectSupportedExtensionByZero
  infer_instance

/-- The exact functor on supported perfect objects induced by extension by zero. -/
def perfectSupportedExactExtensionByZero : Quillen.ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex U)) (perfectSupported (j ⁻¹ᵁ
      T).ι))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex X)) (perfectSupported T.ι))
      where
  toFunctor := perfectSupportedExtensionByZero j T hcover
  map_conflation S hS := by
    change ((S.map (perfectSupported (j ⁻¹ᵁ T).ι).ι).map (extensionByZero j)).ShortExact
    exact hS.map_of_exact _

lemma perfectSupportedExtensionByZero_exact : IsExact
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq
    (perfectSupportedWaldhausen T.ι).cof (perfectSupportedWaldhausen T.ι).weq
    (perfectSupportedExtensionByZero j T hcover) where
  zero h := (perfectSupportedExtensionByZero j T hcover).map_isZero h
  cofibration f hf := (perfectSupportedExactExtensionByZero j T hcover).map_inflation f hf
  weak f hf := by have : QuasiIso f.hom := hf; exact extensionByZero_quasiIso j f.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (perfectSupported T.ι).ι
    exact (fullSubcategory_map_pushout (abelianExactStructure (Complex U))
      (perfectSupported (j ⁻¹ᵁ T).ι) hi h).map (extensionByZero j)

/-- The original adjunction unit, with no change to its underlying chain map. -/
def perfectSupportedExcisionUnit : 𝟭 ((perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) ⟶
    perfectSupportedExtensionByZero j T hcover ⋙ perfectSupportedRestrict j T where
  app K := ObjectProperty.homMk ((extensionByZeroAdjunction j).unit.app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ ((extensionByZeroAdjunction j).unit.naturality f.hom)

/-- The original adjunction counit, with no change to its underlying chain map. -/
def perfectSupportedExcisionCounit :
    perfectSupportedRestrict j T ⋙ perfectSupportedExtensionByZero j T hcover ⟶
      𝟭 ((perfectSupported T.ι).FullSubcategory) where
  app K := ObjectProperty.homMk ((extensionByZeroAdjunction j).counit.app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ ((extensionByZeroAdjunction j).counit.naturality
    f.hom)

/-- The genuine supported adjunction retains both original triangle identities. -/
def perfectSupportedExcisionAdjunction :
    perfectSupportedExtensionByZero j T hcover ⊣ perfectSupportedRestrict j T where
  unit := perfectSupportedExcisionUnit j T hcover
  counit := perfectSupportedExcisionCounit j T hcover
  left_triangle_components K := ObjectProperty.hom_ext _
    ((extensionByZeroAdjunction j).left_triangle_components K.obj)
  right_triangle_components K := ObjectProperty.hom_ext _
    ((extensionByZeroAdjunction j).right_triangle_components K.obj)

lemma perfectSupportedExcisionUnit_weak (K : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) :
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq ((perfectSupportedExcisionUnit j T hcover).app K)
      := by
  change QuasiIso ((extensionByZeroAdjunction j).unit.app K.obj)
  infer_instance

lemma perfectSupportedExcisionCounit_weak (K : (perfectSupported T.ι).FullSubcategory) :
    (perfectSupportedWaldhausen T.ι).weq ((perfectSupportedExcisionCounit j T hcover).app K) :=
  extensionByZero_supported_counit_quasiIso j T hcover K.property

/-- The original supported S-construction realization map is an actual
homotopy equivalence, with the original extension-by-zero realization inverse. -/
def perfectSupportedExcisionRealizationHomotopyEquiv : ContinuousMap.HomotopyEquiv
    (perfectSupportedWaldhausen T.ι).Delooping
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).Delooping where
  toFun := (deloopingMap (perfectSupportedRestrict_exact j T)).hom
  invFun := (deloopingMap (perfectSupportedExtensionByZero_exact j T hcover)).hom
  left_inv := by
    have h := weakNaturalTransformationRealizationHomotopy
      (perfectSupportedWaldhausen T.ι) (perfectSupportedWaldhausen T.ι)
      ((perfectSupportedRestrict_exact j T).comp (perfectSupportedExtensionByZero_exact j T hcover))
      (IsExact.id (perfectSupportedWaldhausen T.ι).cof (perfectSupportedWaldhausen T.ι).weq)
      (perfectSupportedExcisionCounit j T hcover) (perfectSupportedExcisionCounit_weak j T hcover)
    rw [← Quillen.Waldhausen.deloopingMap_comp_deloopingMap (perfectSupportedRestrict_exact j T)
      (perfectSupportedExtensionByZero_exact j T hcover), deloopingMap_id] at h
    exact ⟨h⟩
  right_inv := by
    have h := weakNaturalTransformationRealizationHomotopy
      (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
      (IsExact.id (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof (perfectSupportedWaldhausen (j ⁻¹ᵁ
        T).ι).weq)
      ((perfectSupportedExtensionByZero_exact j T hcover).comp (perfectSupportedRestrict_exact j T))
      (perfectSupportedExcisionUnit j T hcover) (perfectSupportedExcisionUnit_weak j T hcover)
    rw [← Quillen.Waldhausen.deloopingMap_comp_deloopingMap (perfectSupportedExtensionByZero_exact j
      T hcover)
      (perfectSupportedRestrict_exact j T), deloopingMap_id] at h
    exact ⟨h.symm⟩

@[simp] lemma perfectSupportedExcisionRealizationHomotopyEquiv_toFun :
    (perfectSupportedExcisionRealizationHomotopyEquiv j T hcover).toFun =
      (deloopingMap (perfectSupportedRestrict_exact j T)).hom := rfl

@[simp] lemma perfectSupportedExcisionRealizationHomotopyEquiv_invFun :
    (perfectSupportedExcisionRealizationHomotopyEquiv j T hcover).invFun =
      (deloopingMap (perfectSupportedExtensionByZero_exact j T hcover)).hom := rfl

lemma perfectSupportedKRestrict_extensionByZero_leftInverse (n : ℕ) (x : PerfectSupportedK T.ι n) :
    KMap (perfectSupportedExtensionByZero_exact j T hcover) n (perfectSupportedKRestrict j T n x) =
      x := by
  have h := KMap_eq_of_weakNatTrans
    ((perfectSupportedRestrict_exact j T).comp (perfectSupportedExtensionByZero_exact j T hcover))
    (IsExact.id (perfectSupportedWaldhausen T.ι).cof (perfectSupportedWaldhausen T.ι).weq)
    (perfectSupportedExcisionCounit j T hcover) (perfectSupportedExcisionCounit_weak j T hcover) n
  rw [← Quillen.Waldhausen.KMap_comp_KMap,KMap_id] at h
  exact DFunLike.congr_fun h x

lemma perfectSupportedKRestrict_extensionByZero_rightInverse (n : ℕ)
    (x : PerfectSupportedK (j ⁻¹ᵁ T).ι n) :
    perfectSupportedKRestrict j T n (KMap (perfectSupportedExtensionByZero_exact j T hcover) n x) =
      x := by
  have h := KMap_eq_of_weakNatTrans
    (IsExact.id (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof (perfectSupportedWaldhausen (j ⁻¹ᵁ
      T).ι).weq)
    ((perfectSupportedExtensionByZero_exact j T hcover).comp (perfectSupportedRestrict_exact j T))
    (perfectSupportedExcisionUnit j T hcover) (perfectSupportedExcisionUnit_weak j T hcover) n
  rw [← Quillen.Waldhausen.KMap_comp_KMap,KMap_id] at h
  exact (DFunLike.congr_fun h x).symm

/-- The literal original supported restriction is an equivalence in every
connective K-degree, including zero, with the actual extension-by-zero inverse. -/
def perfectSupportedExcisionKEquiv (n : ℕ) :
    PerfectSupportedK T.ι n ≃* PerfectSupportedK (j ⁻¹ᵁ T).ι n where
  toFun := perfectSupportedKRestrict j T n
  invFun := KMap (perfectSupportedExtensionByZero_exact j T hcover) n
  left_inv := perfectSupportedKRestrict_extensionByZero_leftInverse j T hcover n
  right_inv := perfectSupportedKRestrict_extensionByZero_rightInverse j T hcover n
  map_mul' := (perfectSupportedKRestrict j T n).map_mul

@[simp] lemma perfectSupportedExcisionKEquiv_apply (n : ℕ) (x : PerfectSupportedK T.ι n) :
    perfectSupportedExcisionKEquiv j T hcover n x = perfectSupportedKRestrict j T n x := rfl

@[simp] lemma perfectSupportedExcisionKEquiv_symm_apply (n : ℕ)
    (x : PerfectSupportedK (j ⁻¹ᵁ T).ι n) :
    (perfectSupportedExcisionKEquiv j T hcover n).symm x =
      KMap (perfectSupportedExtensionByZero_exact j T hcover) n x := rfl

include hcover in
lemma perfectSupportedKRestrict_bijective_of_cover (n : ℕ) :
    Function.Bijective (perfectSupportedKRestrict j T n) :=
  (perfectSupportedExcisionKEquiv j T hcover n).bijective

end Quillen.PerfectComplexes
