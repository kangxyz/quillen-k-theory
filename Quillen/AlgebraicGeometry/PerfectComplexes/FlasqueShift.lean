/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.Algebra.Homology.MappingCone.Identity
public import Aglib.Algebra.Homology.QuasiIso
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientOperations
public import Quillen.Waldhausen.Cylinder.Pushout
public import Quillen.Waldhausen.Cylinder.ZeroEndpoint
public import Quillen.Algebra.Homology.MappingConeBiprod
public import Quillen.Algebra.Homology.MappingConeAcyclicity
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence

/-! # Original cone-of-identity additivity and the signed shift on the flasque model -/
@[expose] public section
open Quillen


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.PerfectComplexes.FlasqueBoundedBelow
export CochainComplex
  (coneSequence_shortExact identityConeFunctor_additive identityConeFunctor_map_mono
  identityConeFunctor_shortExact quasiIso_of_two_acyclic)
end Quillen.PerfectComplexes.FlasqueBoundedBelow

end


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex CochainComplex
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.FlasqueBoundedBelow
open Waldhausen.SplitFactorization
open ProjectiveLine.FlasqueCoefficients
variable (X : Scheme.{u})

/-- The literal identity cone stays in the original flasque, lower-bounded perfect model. -/
lemma identityCone_objects (K : Obj X) :
    objects X (identityConeFunctor.obj K.obj) :=
  objects_of_shortExact (coneSequence_shortExact X K.obj) K.property
    (shift_objects K.property 1)

/-- The literal cone of identity and its native original cone maps. -/
def identityCone : Obj X ⥤ Obj X :=
  ObjectProperty.lift _ ((objects X).ι ⋙ identityConeFunctor) (identityCone_objects X)

instance identityCone_additive : (identityCone X).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    exact Quillen.CochainComplex.mappingCone_map_add (𝟙 K.obj) (𝟙 L.obj)
      f.hom g.hom f.hom g.hom (by simp) (by simp)

/-- The actual identity cone preserves the inherited original conflations. -/
def identityConeExactFunctor : CategoryTheory.ExactCategory.ExactFunctor
    (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure (Quillen.abelianExactStructure
      (Complex X))
      (objects X))
    (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure (Quillen.abelianExactStructure
      (Complex X))
      (objects X)) where
  toFunctor := identityCone X
  map_conflation S hS := by
    change ((S.map (objects X).ι).map identityConeFunctor).ShortExact
    exact identityConeFunctor_shortExact X hS

/-- Every original identity cone is acyclic, for arbitrary original flasque-perfect input. -/
lemma identityCone_acyclic (K : Obj X) : ((identityCone X).obj K).obj.Acyclic :=
  CochainComplex.mappingCone_acyclic_of_quasiIso (𝟙 K.obj)

lemma identityCone_zero {K : Obj X} (hK : IsZero K) : IsZero ((identityCone X).obj K) := by
  have hz := identityCone_isZero ((objects X).ι.map_isZero hK)
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  exact hz.eq_of_src _ _

lemma identityCone_exact : Waldhausen.IsExact (waldhausen X).cof (waldhausen X).weq
    (waldhausen X).cof (waldhausen X).weq (identityCone X) where
  zero h := identityCone_zero X h
  cofibration f hf := (identityConeExactFunctor X).map_inflation f hf
  weak {K L} f _ := quasiIso_of_two_acyclic X ((identityCone X).map f).hom
    (identityCone_acyclic X K) (identityCone_acyclic X L)
  pushout hi h := (identityConeExactFunctor X).map_isPushout hi h

/-- The literal original cone inclusion is natural in all original maps. -/
def coneFirst : 𝟭 (Obj X) ⟶ identityCone X where
  app K := ObjectProperty.homMk (mappingCone.inr (𝟙 K.obj))
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (mappingCone.triangleMap (𝟙 K.obj) (𝟙 L.obj) f.hom f.hom (by simp)).comm₂.symm

/-- The literal signed original cone quotient to the native shifted input is natural. -/
def coneSecond : identityCone X ⟶ modelShift X 1 where
  app K := ObjectProperty.homMk (mappingCone.triangle (𝟙 K.obj)).mor₃
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (mappingCone.triangleMap (𝟙 K.obj) (𝟙 L.obj) f.hom f.hom (by simp)).comm₃.symm

lemma coneFirst_second : coneFirst X ≫ coneSecond X = 0 := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact (mappingCone.triangleRotateShortComplex (𝟙 K.obj)).zero

lemma coneModelSequence_conflation (K : Obj X) :
    (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure (Quillen.abelianExactStructure
      (Complex X))
      (objects X)).conflation
      (ShortComplex.mk ((coneFirst X).app K) ((coneSecond X).app K)
        (NatTrans.congr_app (coneFirst_second X) K)) :=
  coneSequence_shortExact X K.obj

/-- The actual identity-cone sequence has the native relative cofibration and cofiber squares. -/
lemma coneSequence_isCofibrationSequence :
    Waldhausen.Additivity.IsCofibrationSequence (waldhausen X) (waldhausen X)
      (coneFirst X) (coneSecond X) where
  exactF := Waldhausen.IsExact.id _ _
  exactG := identityCone_exact X
  exactH := modelShift_exact X 1
  cofibration := {
    app_cof K := (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
      (Quillen.abelianExactStructure (Complex X)) (objects X)).inflation_of_conflation
        (coneModelSequence_conflation X K)
    relative_cof {K L} f hf := by
      let E := CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
        (Quillen.abelianExactStructure (Complex X)) (objects X)
      let φ := Waldhausen.GilletWaldhausen.exactFunctorSequenceMap
        (coneFirst X) (coneSecond X) (coneFirst_second X) f
      let : HasPushout
          (Waldhausen.GilletWaldhausen.exactFunctorSequenceAt
            (coneFirst X) (coneSecond X) (coneFirst_second X) K).f φ.τ₁ :=
        Waldhausen.Additivity.hasPushout (waldhausen X) (coneFirst X)
          (fun K => E.inflation_of_conflation (coneModelSequence_conflation X K)) f
      exact Waldhausen.GilletWaldhausen.relativePushout_inflation E φ
        (coneModelSequence_conflation X K) (coneModelSequence_conflation X L)
        ((modelShift_exact X 1).cofibration f hf) }
  cofiber K := Waldhausen.QuillenComparison.isPushoutOfZeroCokernel _
    ((CategoryTheory.ExactCategory.ExactSubcategory.exactStructure (Quillen.abelianExactStructure
      (Complex X))
      (objects X)).cokernel _ (coneModelSequence_conflation X K))
    (waldhausen X).isZero _ _

/-- The original zero map from the actual identity cone to the original chosen zero. -/
def coneToZero : identityCone X ⟶ Waldhausen.zeroFunctor (waldhausen X) := 0

lemma coneToZero_weak (K : Obj X) : (waldhausen X).weq ((coneToZero X).app K) := by
  apply quasiIso_of_two_acyclic X
  · exact identityCone_acyclic X K
  · exact HomologicalComplex.acyclic_of_isZero _
      ((objects X).ι.map_isZero (waldhausen X).isZero)

lemma KMap_identityCone_zero (n : ℕ) : Waldhausen.KMap (identityCone_exact X) n = 1 :=
  (Waldhausen.KMap_eq_of_weakNatTrans (identityCone_exact X)
    (Waldhausen.zeroFunctor_isExact (waldhausen X) (waldhausen X))
    (coneToZero X) (coneToZero_weak X) n).trans (Waldhausen.KMap_zeroFunctor _ _ n)

/-- The actual signed shift induces inversion on every original K-group, including degree zero. -/
lemma KMap_modelShift_one_apply (n : ℕ) (x : (waldhausen X).K n) :
    Waldhausen.KMap (modelShift_exact X 1) n x = x⁻¹ := by
  have he := Waldhausen.Additivity.KMap_additivity_mul (waldhausen X) (waldhausen X)
    (coneFirst X) (coneSecond X) (coneSequence_isCofibrationSequence X) n x
  simp only [KMap_identityCone_zero, Waldhausen.KMap_id,
    MonoidHom.one_apply, MonoidHom.id_apply] at he
  calc
    Waldhausen.KMap (modelShift_exact X 1) n x = 1 *
        Waldhausen.KMap (modelShift_exact X 1) n x := (one_mul _).symm
    _ = (x⁻¹ * x) * Waldhausen.KMap (modelShift_exact X 1) n x := by rw [inv_mul_cancel]
    _ = x⁻¹ := by rw [mul_assoc, ← he, mul_one]

end Quillen.PerfectComplexes.FlasqueBoundedBelow
