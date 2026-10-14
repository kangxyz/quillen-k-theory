/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientOperations
public import Quillen.Waldhausen.Cylinder.Pushout
public import Quillen.Waldhausen.Cylinder.ZeroEndpoint
public import Quillen.Algebra.Homology.MappingConeBiprod
public import Quillen.Algebra.Homology.MappingConeAcyclicity
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence

/-! # Original cone-of-identity additivity and the signed shift on the flasque model -/
@[expose] public section
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

instance identityConeFunctor_additive : (identityConeFunctor (A := X.Modules)).Additive where
  map_add := by
    intro K L f g
    exact Quillen.CochainComplex.mappingCone_map_add (𝟙 K) (𝟙 L)
      f g f g (by simp) (by simp)

/-- The native original cone sequence retains its signed connecting quotient. -/
lemma coneSequence_shortExact (K : Complex X) :
    (mappingCone.triangleRotateShortComplex (𝟙 K)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (mappingCone.triangleRotateShortComplexSplitting (𝟙 K) n).shortExact)

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

/-- Neighboring-term biproducts show that the original cone functor preserves monomorphisms. -/
lemma identityConeFunctor_map_mono {K L : Complex X} (f : K ⟶ L) [Mono f] :
    Mono (identityConeFunctor.map f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  let : Mono (f.f (n + 1)) := (HomologicalComplex.eval X.Modules (.up ℤ) (n + 1)).map_mono f
  let : Mono (f.f n) := (HomologicalComplex.eval X.Modules (.up ℤ) n).map_mono f
  have h : Mono ((identityConeFunctor.map f).f n ≫ (identityConeTermIso L n).hom) := by
    rw [← identityConeTermIso_naturality]
    infer_instance
  exact mono_of_mono _ (identityConeTermIso L n).hom

/-- Actual pushout preservation and the actual zero cone retain the cokernel universal property. -/
lemma identityConeFunctor_shortExact {S : ShortComplex (Complex X)} (hS : S.ShortExact) :
    (S.map identityConeFunctor).ShortExact := by
  let F : Complex X ⥤ Complex X := identityConeFunctor
  let : F.Additive := ⟨by
    intro K L f g
    exact Quillen.CochainComplex.mappingCone_map_add (𝟙 K) (𝟙 L)
      f g f g (by simp) (by simp)⟩
  have hp : IsPushout S.f (0 : S.X₁ ⟶ 0) S.g (0 : 0 ⟶ S.X₃) :=
    Waldhausen.QuillenComparison.isPushoutOfZeroCokernel S.zero hS.gIsCokernel
      (isZero_zero _) _ _
  have hFp := identityConeFunctor_map_isPushout hp
  have hFzero : IsZero (F.obj (0 : Complex X)) := identityCone_isZero (isZero_zero _)
  have hc : IsColimit (CokernelCofork.ofπ (F.map S.g)
      (show F.map S.f ≫ F.map S.g = 0 by rw [← F.map_comp, S.zero, F.map_zero])) := by
    refine Cofork.IsColimit.mk _ (fun s => hFp.desc s.π 0 (by
      rw [CokernelCofork.condition s, comp_zero])) ?_ ?_
    · intro s
      exact hFp.inl_desc _ _ _
    · intro s m hm
      apply hFp.hom_ext
      · rw [hFp.inl_desc]
        exact hm
      · exact hFzero.eq_of_src _ _
  have : Mono S.f := hS.mono_f
  have : Mono (F.map S.f) := identityConeFunctor_map_mono X S.f
  have : Epi (F.map S.g) := epi_of_isColimit_cofork hc
  change (S.map F).ShortExact
  exact {
    exact := ShortComplex.exact_of_g_is_cokernel _ hc
    mono_f := by change Mono (F.map S.f); infer_instance
    epi_g := by change Epi (F.map S.g); infer_instance }

/-- The actual identity cone preserves the inherited original conflations. -/
def identityConeExactFunctor : Quillen.ExactFunctor
    (Quillen.ExactSubcategory.exactStructure (Quillen.abelianExactStructure (Complex X))
      (objects X))
    (Quillen.ExactSubcategory.exactStructure (Quillen.abelianExactStructure (Complex X))
      (objects X)) where
  toFunctor := identityCone X
  map_conflation S hS := by
    change ((S.map (objects X).ι).map identityConeFunctor).ShortExact
    exact identityConeFunctor_shortExact X hS

lemma quasiIso_of_two_acyclic {K L : Complex X} (f : K ⟶ L)
    (hK : K.Acyclic) (hL : L.Acyclic) : QuasiIso f :=
  (quasiIso_iff f).mpr (fun n => (quasiIsoAt_iff_exactAt f n (hK n)).mpr (hL n))

/-- Every original identity cone is acyclic, for arbitrary original flasque-perfect input. -/
lemma identityCone_acyclic (K : Obj X) : ((identityCone X).obj K).obj.Acyclic :=
  Quillen.HomologicalAlgebra.mappingCone_acyclic_of_quasiIso (𝟙 K.obj)

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
    (Quillen.ExactSubcategory.exactStructure (Quillen.abelianExactStructure (Complex X))
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
    app_cof K := (Quillen.ExactSubcategory.exactStructure
      (Quillen.abelianExactStructure (Complex X)) (objects X)).inflation_of_conflation
        (coneModelSequence_conflation X K)
    relative_cof {K L} f hf := by
      let E := Quillen.ExactSubcategory.exactStructure
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
    ((Quillen.ExactSubcategory.exactStructure (Quillen.abelianExactStructure (Complex X))
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
