/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.IdentityCone


public import Aglib.CategoryTheory.Limits.Shapes.CokernelPushout
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.Algebra.Homology.MappingCone.Identity
public import Aglib.Algebra.Homology.MappingCone.Map
public import Aglib.Algebra.Homology.QuasiIso
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientOperations
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.Pushout
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.ZeroEndpoint
public import Quillen.Aglib.Algebra.Homology.MappingCone.Biprod
public import Aglib.Algebra.Homology.MappingCone.Acyclicity
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence

/-! # Original cone-of-identity additivity and the signed shift on the flasque model -/
@[expose] public section

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
open Quillen.Waldhausen.SplitFactorization


open CochainComplex

open Quillen




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

lemma identityCone_exact : Waldhausen.IsExact (waldhausen X).cof (waldhausen X).weq
    (waldhausen X).cof (waldhausen X).weq (identityCone X) where
  zero h := identityCone_zero X h
  cofibration f hf := (identityConeExactFunctor X).map_inflation f hf
  weak {K L} f _ :=
    CochainComplex.quasiIso_of_two_acyclic (A := X.Modules) ((identityCone X).map f).hom
    (identityCone_acyclic X K) (identityCone_acyclic X L)
  pushout hi h := (identityConeExactFunctor X).map_isPushout hi h

/-- The actual identity-cone sequence has the native relative cofibration and cofiber squares. -/
lemma coneSequence_isCofibrationSequence :
    Waldhausen.Additivity.IsCofibrationSequence (waldhausen X) (waldhausen X)
      (coneFirst X) (coneSecond X) where
  exactF := Waldhausen.IsExact.id _ _
  exactG := identityCone_exact X
  exactH := modelShift_exact X 1
  cofibration := {
    app_cof K := (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
      (CategoryTheory.ExactCategory.abelianExactStructure (CochainComplex X.Modules ℤ)) (objects
        X)).inflation_of_conflation
        (coneModelSequence_conflation X K)
    relative_cof {K L} f hf := by
      let E := CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
        (CategoryTheory.ExactCategory.abelianExactStructure (CochainComplex X.Modules ℤ))
          (objects X)
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
  cofiber K := CategoryTheory.Limits.isPushout_of_isColimit_cokernel _
    ((CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
      (CategoryTheory.ExactCategory.abelianExactStructure
      (CochainComplex X.Modules ℤ))
      (objects X)).cokernel _ (coneModelSequence_conflation X K))
    (waldhausen X).isZero _ _

/-- The original zero map from the actual identity cone to the original chosen zero. -/
def coneToZero : identityCone X ⟶ Waldhausen.zeroFunctor (waldhausen X) := 0

lemma coneToZero_weak (K : Obj X) : (waldhausen X).weq ((coneToZero X).app K) := by
  apply CochainComplex.quasiIso_of_two_acyclic (A := X.Modules)
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
