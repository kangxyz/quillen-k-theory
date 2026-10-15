/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeEulerAdditivity
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativePhiComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlasqueShift

/-! # Original native Euler zero, signed shift and actual coefficient entries -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeEuler
open FlasqueCoefficients
variable (X : QuasiCompactSchemes.{u})

local instance nativeMiddleDerived (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _

local instance derivedPlusQ_additive (Y : Scheme.{u}) :
    (DerivedCategory.Plus.Q (C := Y.Modules)).Additive := by
  dsimp [DerivedCategory.Plus.Q]
  infer_instance

local instance derivedProjection_additive :
    (derivedPushforwardPlus (nativeProjection.app X).hom).Additive := by
  dsimp [derivedPushforwardPlus]
  infer_instance

/-- The original coefficient complex, functorially tensored in its Euler module. -/
def coefficientTensorFunctor (K : FlasqueBoundedBelow.Obj X.obj) :
    (nativeLineFunctor.obj X).obj.Modules ⥤
      CochainComplex.Plus (nativeLineFunctor.obj X).obj.Modules where
  obj M := ⟨(endpointComplex X M).obj K, by
    obtain ⟨a, ha⟩ := K.property.1.2
    let := ha
    exact ⟨a, endpointComplex_isStrictlyGE X M K a⟩⟩
  map f := ObjectProperty.homMk
    (((moduleTensorCoefficientMap (nativeLineFunctor.obj X).obj f).mapHomologicalComplex
      (.up ℤ)).app ((pullbackComplex (nativeProjection.app X).hom).obj K.obj))
  map_id M := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.Hom.ext
    funext n
    exact (moduleTensorByLineRight
      (((pullbackComplex (nativeProjection.app X).hom).obj K.obj).X n)).map_id M
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.Hom.ext
    funext n
    exact (moduleTensorByLineRight
      (((pullbackComplex (nativeProjection.app X).hom).obj K.obj).X n)).map_comp f g

instance coefficientTensorFunctor_additive (K : FlasqueBoundedBelow.Obj X.obj) :
    (coefficientTensorFunctor X K).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.Hom.ext
    funext n
    exact Functor.map_add (moduleTensorByLineRight
      (((pullbackComplex (nativeProjection.app X).hom).obj K.obj).X n))

/-- The installed derived projection of the original bounded coefficient tensor. -/
def coefficientDerivedProjection (K : FlasqueBoundedBelow.Obj X.obj) :=
  coefficientTensorFunctor X K ⋙ DerivedCategory.Plus.Q ⋙
    derivedPushforwardPlus (nativeProjection.app X).hom

instance coefficientDerivedProjection_additive (K : FlasqueBoundedBelow.Obj X.obj) :
    (coefficientDerivedProjection X K).Additive := by
  unfold coefficientDerivedProjection
  infer_instance

/-- The actual normalized middle is the original ordered pair of negative coefficients. -/
def middleDerivedBiprodIso (K : FlasqueBoundedBelow.Obj X.obj) :
    (coefficientDerivedProjection X K).obj (sequence X).X₂ ≅
      (coefficientDerivedProjection X K).obj (nativeTautologicalLine X) ⊞
        (coefficientDerivedProjection X K).obj (nativeTautologicalLine X) :=
  (coefficientDerivedProjection X K).mapBiprod (nativeTautologicalLine X)
    (nativeTautologicalLine X)

lemma middleEndpoint_derivedZero (K : FlasqueBoundedBelow.Obj X.obj) :
    IsZero ((coefficientDerivedProjection X K).obj (sequence X).X₂) := by
  have hz : IsZero ((coefficientDerivedProjection X K).obj (nativeTautologicalLine X)) :=
    P5NativeEntries.negative_derivedZero X ((toPlus X.obj).obj K) K.property.1.1
  exact ((biprod_isZero_iff _ _).mpr ⟨hz, hz⟩).of_iso (middleDerivedBiprodIso X K)

/-- The actual total augmentation and original G0 unit certify the projected middle acyclicity. -/
lemma middleProjected_derivedZero (K : FlasqueBoundedBelow.Obj X.obj) :
    IsZero (DerivedCategory.Plus.Q.obj ((toPlus X.obj).obj ((E1 X).obj K))) := by
  let P := (nativeLineFunctor.obj X).obj
  let B := (endpointBounded X (sequence X).X₂ (middleEndpoint_locallyPerfect X)).obj K
  let C := (boundedToPlus P).obj B
  have : IsIso (DerivedCategory.Plus.Q.map ((godementTotalPlusUnit P).app C)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso P.Modules) _
      (godementTotalPlusUnit_quasiIso P C)
  have ht := (middleEndpoint_derivedZero X K).of_iso
    ((derivedPushforwardPlus (nativeProjection.app X).hom).mapIso
      (asIso (DerivedCategory.Plus.Q.map ((godementTotalPlusUnit P).app C))).symm)
  exact ht.of_iso ((P5NativeCoefficients.G0DerivedIso X).app
    ((FlasqueBoundedBelow.total P).obj B))

/-- The literal original natural transformation to the chosen flasque zero. -/
def middleToZero : E1 X ⟶ Waldhausen.zeroFunctor (FlasqueBoundedBelow.waldhausen X.obj) := 0

lemma middleToZero_weak (K : FlasqueBoundedBelow.Obj X.obj) :
    (FlasqueBoundedBelow.waldhausen X.obj).weq ((middleToZero X).app K) :=
  FlasquePhiEntries.weak_zero_of_derivedZero X.obj ((E1 X).obj K)
    (middleProjected_derivedZero X K)

/-- The actual natural weak-zero map gives the middle K-map, including degree zero. -/
lemma KMap_E1_zero (n : ℕ) : Waldhausen.KMap (E1_exact X) n = 1 :=
  (Waldhausen.KMap_eq_of_weakNatTrans (E1_exact X)
    (Waldhausen.zeroFunctor_isExact (FlasqueBoundedBelow.waldhausen X.obj)
      (FlasqueBoundedBelow.waldhausen X.obj)) (middleToZero X) (middleToZero_weak X) n).trans
    (Waldhausen.KMap_zeroFunctor _ _ n)

/-- The actual Euler additivity sign identifies the inverse square coefficient. -/
lemma KMap_E2_inv_eq_E0 (n : ℕ) (x : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    (Waldhausen.KMap (E2_exact X) n x)⁻¹ = Waldhausen.KMap (E0_exact X) n x := by
  have he := KMap_euler_additivity X n x
  simp only [KMap_E1_zero, MonoidHom.one_apply] at he
  calc
    _ = (Waldhausen.KMap (E2_exact X) n x)⁻¹ * 1 := (mul_one _).symm
    _ = (Waldhausen.KMap (E2_exact X) n x)⁻¹ *
        (Waldhausen.KMap (E2_exact X) n x * Waldhausen.KMap (E0_exact X) n x) := by rw [← he]
    _ = _ := inv_mul_cancel_left _ _

/-- The original signed shift after the actual square endpoint projection. -/
def E2Shift := E2 X ⋙ modelShift X.obj 1

lemma E2Shift_exact : Waldhausen.IsExact (FlasqueBoundedBelow.waldhausen X.obj).cof
    (FlasqueBoundedBelow.waldhausen X.obj).weq (FlasqueBoundedBelow.waldhausen X.obj).cof
    (FlasqueBoundedBelow.waldhausen X.obj).weq (E2Shift X) :=
  (E2_exact X).comp (modelShift_exact X.obj 1)

/-- The original signed-shift K-map, with original zero rebasing, gives E2[1] = E0 for all n. -/
lemma KMap_E2Shift_eq_E0 (n : ℕ) :
    Waldhausen.KMap (E2Shift_exact X) n = Waldhausen.KMap (E0_exact X) n := by
  rw [show E2Shift_exact X = (E2_exact X).comp (modelShift_exact X.obj 1) from rfl,
    ← Waldhausen.KMap_comp_KMap (E2_exact X) (modelShift_exact X.obj 1) n]
  apply MonoidHom.ext
  intro x
  exact (FlasqueBoundedBelow.KMap_modelShift_one_apply X.obj n
    (Waldhausen.KMap (E2_exact X) n x)).trans (KMap_E2_inv_eq_E0 X n x)

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeEuler

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries
open FlasqueCoefficients
variable (X : QuasiCompactSchemes.{u})

/-- Literal original right tensor on the bounded-below perfect model, before any totalization. -/
def boundedRightTensor : BoundedBelow.Obj (nativeLineFunctor.obj X).obj ⥤
    BoundedBelow.Obj (nativeLineFunctor.obj X).obj :=
  ObjectProperty.lift _ ((BoundedBelow.objects (nativeLineFunctor.obj X).obj).ι ⋙
    tensorByLineRightComplex (nativeTautologicalLine X)) (fun K => by
      obtain ⟨hp, a, ha⟩ := K.property
      let := ha
      exact ⟨P5NativeCoefficients.rightTensor_locallyPerfect X hp, a,
        P5NativeCoefficients.rightTensor_isStrictlyGE X K.obj a⟩)

instance boundedRightTensor_additive : (boundedRightTensor X).Additive := by
  unfold boundedRightTensor
  infer_instance

def boundedRightTensorExactFunctor : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure
      (Complex (nativeLineFunctor.obj X).obj)) (BoundedBelow.objects
        (nativeLineFunctor.obj X).obj))
    (ExactSubcategory.exactStructure (abelianExactStructure
      (Complex (nativeLineFunctor.obj X).obj)) (BoundedBelow.objects
        (nativeLineFunctor.obj X).obj)) where
  toFunctor := boundedRightTensor X
  map_conflation S hS := by
    change (S.map (BoundedBelow.objects (nativeLineFunctor.obj X).obj).ι).ShortExact at hS
    exact hS.map_of_exact (tensorByLineRightComplex (nativeTautologicalLine X))

lemma boundedRightTensor_exact : Waldhausen.IsExact
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq (boundedRightTensor X) where
  zero h := (boundedRightTensor X).map_isZero h
  cofibration f hf := (boundedRightTensorExactFunctor X).map_inflation f hf
  weak f hf := by
    change QuasiIso f.hom at hf
    let := hf
    exact rightLineComplex_quasiIso (nativeTautologicalLine X) f.hom
  pushout hi h := (boundedRightTensorExactFunctor X).map_isPushout hi h

/-- Identity chain maps reconcile only the two membership witnesses for original right tensor. -/
def rightTensorInclusionIso :
    FlasqueBoundedBelow.inclusion (nativeLineFunctor.obj X).obj ⋙ boundedRightTensor X ≅
      P5NativeCoefficients.rightTensor X :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _
    (Iso.refl ((tensorByLineRightComplex (nativeTautologicalLine X)).obj K.obj))) (by
      intro K L f
      apply ObjectProperty.hom_ext
      change (tensorByLineRightComplex (nativeTautologicalLine X)).map f.hom ≫ 𝟙 _ =
        𝟙 _ ≫ (tensorByLineRightComplex (nativeTautologicalLine X)).map f.hom
      simp)

/-- The original right tensor and two-line associator identify the actual Euler square endpoint. -/
def negativeRightTensorIso : P5NativePhi.second X ⋙ boundedRightTensor X ≅
    P5NativeEuler.endpointBounded X (P5NativeEuler.sequence X).X₁
      (P5NativeEuler.squareEndpoint_locallyPerfect X) :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _
    ((P5NativeEuler.originalRightTensorIso X).app K)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (P5NativeEuler.originalRightTensorIso X).hom.naturality f)

/-- The actual forward line augmentation before right tensor. -/
def totalUnitWhisker {C : Type (u + 1)} [Category.{u} C] (Y : Scheme.{u})
    (F : C ⥤ BoundedBelow.Obj Y) :
    F ⟶ (F ⋙ FlasqueBoundedBelow.total Y) ⋙ FlasqueBoundedBelow.inclusion Y :=
  Functor.whiskerLeft F (FlasqueBoundedBelow.unit Y)

lemma totalUnitWhisker_weak {C : Type (u + 1)} [Category.{u} C] (Y : Scheme.{u})
    (F : C ⥤ BoundedBelow.Obj Y) (K : C) :
    (BoundedBelow.waldhausen Y).weq ((totalUnitWhisker Y F).app K) :=
  FlasqueBoundedBelow.unit_weak Y (F.obj K)

/-- The component is the same original total augmentation, with no replacement chain map. -/
lemma totalUnitWhisker_app {C : Type (u + 1)} [Category.{u} C] (Y : Scheme.{u})
    (F : C ⥤ BoundedBelow.Obj Y) (K : C) :
    (totalUnitWhisker Y F).app K = (FlasqueBoundedBelow.unit Y).app (F.obj K) := rfl

/-- The actual forward line augmentation before right tensor. -/
def negativeLineUnit : P5NativePhi.second X ⟶
    secondTotal X ⋙ FlasqueBoundedBelow.inclusion (nativeLineFunctor.obj X).obj :=
  totalUnitWhisker (nativeLineFunctor.obj X).obj (P5NativePhi.second X)

lemma negativeLineUnit_weak (K : FlasqueBoundedBelow.Obj X.obj) :
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq ((negativeLineUnit X).app K) :=
  totalUnitWhisker_weak (nativeLineFunctor.obj X).obj (P5NativePhi.second X) K

/-- Original exact right tensor of that same forward augmentation. -/
def negativeRightUnit : P5NativePhi.second X ⋙ boundedRightTensor X ⟶
    secondTotal X ⋙ P5NativeCoefficients.rightTensor X :=
  Functor.whiskerRight (negativeLineUnit X) (boundedRightTensor X) ≫
    (Functor.associator (secondTotal X) (FlasqueBoundedBelow.inclusion
      (nativeLineFunctor.obj X).obj) (boundedRightTensor X)).hom ≫
      Functor.whiskerLeft (secondTotal X) (rightTensorInclusionIso X).hom

lemma negativeRightUnit_weak (K : FlasqueBoundedBelow.Obj X.obj) :
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq ((negativeRightUnit X).app K) :=
  (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq.comp_mem _ _
    ((boundedRightTensor_exact X).weak _ (negativeLineUnit_weak X K))
    ((BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq.comp_mem _ _
      ((BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq_iso _ inferInstance)
      ((BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq_iso _ inferInstance))

/-- Actual total, ordinary flasque pushforward, then the original signed cochain shift. -/
def projectedShift := FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj ⋙
  P5NativeCoefficients.G0 X ⋙ modelShift X.obj 1

lemma projectedShift_exact : Waldhausen.IsExact
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (projectedShift X) :=
  (FlasqueBoundedBelow.total_exact _).comp
    ((P5NativeCoefficients.G0_exact X).comp (modelShift_exact X.obj 1))

/-- Only canonical associators reconcile the original G1 pipeline. -/
def rightProjectedShiftIso : P5NativeCoefficients.rightTensor X ⋙ projectedShift X ≅
    P5NativeCoefficients.G1 X :=
  (Functor.associator (P5NativeCoefficients.rightTensor X)
    (FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj)
    (P5NativeCoefficients.G0 X ⋙ modelShift X.obj 1)).symm

def negativeRightProjectedIso :
    (secondTotal X ⋙ P5NativeCoefficients.rightTensor X) ⋙ projectedShift X ≅
      secondTotal X ⋙ P5NativeCoefficients.G1 X :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (secondTotal X) (rightProjectedShiftIso X)

/-- Canonical associators retain the actual Euler square endpoint followed by its signed shift. -/
def EulerShiftProjectionIso : P5NativeEuler.E2Shift X ≅
    P5NativeEuler.endpointBounded X (P5NativeEuler.sequence X).X₁
      (P5NativeEuler.squareEndpoint_locallyPerfect X) ⋙ projectedShift X :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _)

def rawRightProjected := (P5NativePhi.second X ⋙ boundedRightTensor X) ⋙ projectedShift X

lemma rawRightProjected_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (rawRightProjected X) :=
  ((P5NativePhi.second_exact X).comp (boundedRightTensor_exact X)).comp (projectedShift_exact X)

def totalRightProjected :=
  (secondTotal X ⋙ P5NativeCoefficients.rightTensor X) ⋙ projectedShift X

lemma totalRightProjected_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (totalRightProjected X) :=
  ((secondTotal_exact X).comp (P5NativeCoefficients.rightTensor_exact X)).comp
    (projectedShift_exact X)

/-- The actual exact pipeline maps the actual forward tensor unit to a weak natural map. -/
lemma totalRightProjected_KMap_eq_raw (n : ℕ) :
    Waldhausen.KMap (totalRightProjected_exact X) n =
      Waldhausen.KMap (rawRightProjected_exact X) n :=
  (Waldhausen.KMap_eq_of_weakNatTrans (rawRightProjected_exact X) (totalRightProjected_exact X)
    (Functor.whiskerRight (negativeRightUnit X) (projectedShift X))
    (fun K => (projectedShift_exact X).weak _ (negativeRightUnit_weak X K)) n).symm

/-- The actual original Euler E2[1] is compared to the raw right-tensor pipeline. -/
def EulerShiftRightIso : P5NativeEuler.E2Shift X ≅ rawRightProjected X :=
  EulerShiftProjectionIso X ≪≫
    Functor.isoWhiskerRight (negativeRightTensorIso X).symm (projectedShift X)

/-- The actual first diagonal functor. -/
def G0First := firstTotal X ⋙ P5NativeCoefficients.G0 X

lemma G0First_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (G0First X) := (firstTotal_exact X).comp (P5NativeCoefficients.G0_exact X)

/-- The actual original second diagonal functor, including its prescribed right tensor. -/
def G1Second := secondTotal X ⋙ P5NativeCoefficients.G1 X

lemma G1Second_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (G1Second X) := (secondTotal_exact X).comp (P5NativeCoefficients.G1_exact X)

/-- The original E0 left unitor in the actual bounded model. -/
def EulerUnitBoundedIso :
    P5NativeEuler.endpointBounded X (P5NativeEuler.sequence X).X₃
      (P5NativeEuler.unitEndpoint_locallyPerfect X) ≅ P5NativePhi.first X :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _
    ((P5NativeEuler.unitEndpointIso X).app K)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (P5NativeEuler.unitEndpointIso X).hom.naturality f)

/-- The same original E0 unitor, followed by actual total and ordinary projection. -/
def EulerE0PositiveIso : P5NativeEuler.E0 X ≅ G0First X :=
  Functor.isoWhiskerRight (EulerUnitBoundedIso X)
      (FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj ⋙ P5NativeCoefficients.G0 X) ≪≫
    (Functor.associator (P5NativePhi.first X) (FlasqueBoundedBelow.total
      (nativeLineFunctor.obj X).obj) (P5NativeCoefficients.G0 X)).symm

/-- Original Euler additivity and actual weak spans equate the two native diagonal K-maps. -/
theorem G1Second_KMap_eq_G0First (n : ℕ) :
    Waldhausen.KMap (G1Second_exact X) n = Waldhausen.KMap (G0First_exact X) n := by
  calc
    _ = Waldhausen.KMap (totalRightProjected_exact X) n :=
      (Waldhausen.KMap_eq_of_iso (totalRightProjected_exact X) (G1Second_exact X)
        (negativeRightProjectedIso X) n).symm
    _ = Waldhausen.KMap (rawRightProjected_exact X) n := totalRightProjected_KMap_eq_raw X n
    _ = Waldhausen.KMap (P5NativeEuler.E2Shift_exact X) n :=
      (Waldhausen.KMap_eq_of_iso (P5NativeEuler.E2Shift_exact X) (rawRightProjected_exact X)
        (EulerShiftRightIso X) n).symm
    _ = Waldhausen.KMap (P5NativeEuler.E0_exact X) n := P5NativeEuler.KMap_E2Shift_eq_E0 X n
    _ = _ := Waldhausen.KMap_eq_of_iso (P5NativeEuler.E0_exact X) (G0First_exact X)
      (EulerE0PositiveIso X) n

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries
open Waldhausen Waldhausen.ExtensionCategory
variable (X : QuasiCompactSchemes.{u})

/-- Original additivity and composition for a totalized sum, with all functors kept abstract. -/
theorem KMap_totalizedSum_post_apply
    {C B P D : Type (u + 1)} [Category.{u} C] [Category.{u} B]
    [Category.{u} P] [Category.{u} D] [HasBinaryCoproducts B]
    (W : Structure C) (V : Structure B) (Q : Structure P) (S : Structure D)
    {H F : C ⥤ B} {T : B ⥤ P} {J : P ⥤ D}
    (hH : IsExact W.cof W.weq V.cof V.weq H)
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hT : IsExact V.cof V.weq Q.cof Q.weq T)
    (hJ : IsExact Q.cof Q.weq S.cof S.weq J)
    (n : ℕ) (a b : W.K n) :
    KMap hJ n (KMap ((Additivity.sumFunctor_isExact (productStructure W W) V
      ((fst_exact W W).comp hH) ((snd_exact W W).comp hF)).comp hT) n
        ((Product.KEquiv W W n).symm (a, b))) =
      KMap ((hH.comp hT).comp hJ) n a * KMap ((hF.comp hT).comp hJ) n b := by
  let hsum := Additivity.sumFunctor_isExact (productStructure W W) V
    ((fst_exact W W).comp hH) ((snd_exact W W).comp hF)
  let hTJ := hT.comp hJ
  let z := (Product.KEquiv W W n).symm (a, b)
  have hz : (KMap (fst_exact W W) n z, KMap (snd_exact W W) n z) = (a, b) :=
    (Product.KEquiv W W n).apply_symm_apply _
  have hpost : (KMap hJ n).comp (KMap (hsum.comp hT) n) =
      (KMap hTJ n).comp (KMap hsum n) := by
    rw [KMap_comp_KMap, KMap_comp_KMap]
  have hfirst : (KMap hTJ n).comp (KMap hH n) = KMap ((hH.comp hT).comp hJ) n := by
    rw [KMap_comp_KMap]
  have hsecond : (KMap hTJ n).comp (KMap hF n) = KMap ((hF.comp hT).comp hJ) n := by
    rw [KMap_comp_KMap]
  change ((KMap hJ n).comp (KMap (hsum.comp hT) n)) z = _
  rw [hpost]
  change KMap hTJ n (KMap hsum n z) = _
  rw [Additivity.KMap_sum_apply _ _ ((fst_exact W W).comp hH)
    ((snd_exact W W).comp hF), map_mul]
  rw [← KMap_comp_KMap (fst_exact W W) hH n,
    ← KMap_comp_KMap (snd_exact W W) hF n]
  change ((KMap hTJ n).comp (KMap hH n)) (KMap (fst_exact W W) n z) *
    ((KMap hTJ n).comp (KMap hF n)) (KMap (snd_exact W W) n z) = _
  rw [hfirst, hsecond]
  exact congrArg₂ (fun x y => KMap ((hH.comp hT).comp hJ) n x *
    KMap ((hF.comp hT).comp hJ) n y)
    (congrArg _root_.Prod.fst hz) (congrArg _root_.Prod.snd hz)

/-- Actual totalized Phi, evaluated by an actual exact coefficient functor, retains both summands.
-/
theorem coefficient_Phi_apply
    (F : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj ⥤ FlasqueBoundedBelow.Obj X.obj)
    (hF : IsExact (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
      (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq
      (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq F)
    (n : ℕ) (a b : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    KMap hF n (P5NativePhi.PhiTwoSummandKMap X n (a, b)) =
      KMap ((firstTotal_exact X).comp hF) n a * KMap ((secondTotal_exact X).comp hF) n b :=
  KMap_totalizedSum_post_apply (FlasqueBoundedBelow.waldhausen X.obj)
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj)
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj)
    (FlasqueBoundedBelow.waldhausen X.obj) (P5NativePhi.first_exact X) (P5NativePhi.second_exact X)
    (FlasqueBoundedBelow.total_exact (nativeLineFunctor.obj X).obj) hF n a b

/-- The actual original upper row has the actual positive coefficient and zero off-diagonal. -/
theorem G0_Phi_apply (n : ℕ) (a b : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    KMap (P5NativeCoefficients.G0_exact X) n (P5NativePhi.PhiTwoSummandKMap X n (a, b)) =
      KMap (G0First_exact X) n a := by
  have h := coefficient_Phi_apply X (P5NativeCoefficients.G0 X)
    (P5NativeCoefficients.G0_exact X) n a b
  change _ = KMap (G0First_exact X) n a * KMap (G0Second_exact X) n b at h
  simpa only [G0Second_KMap_eq_one, MonoidHom.one_apply, mul_one] using h

/-- The actual original lower row uses the signed Euler diagonal and actual zero first entry. -/
theorem G1_Phi_apply (n : ℕ) (a b : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    KMap (P5NativeCoefficients.G1_exact X) n (P5NativePhi.PhiTwoSummandKMap X n (a, b)) =
      KMap (G0First_exact X) n b := by
  have h := coefficient_Phi_apply X (P5NativeCoefficients.G1 X)
    (P5NativeCoefficients.G1_exact X) n a b
  change _ = KMap (G1First_exact X) n a * KMap (G1Second_exact X) n b at h
  simpa only [G1First_KMap_eq_one, G1Second_KMap_eq_G0First, MonoidHom.one_apply, one_mul] using h

/-- The actual original paired coefficient functor retains the original product K-equivalence. -/
lemma G_KEquiv_apply (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).K n) :
    Product.KEquiv (FlasqueBoundedBelow.waldhausen X.obj) (FlasqueBoundedBelow.waldhausen X.obj) n
        (KMap (P5NativeCoefficients.G_exact X) n a) =
      (KMap (P5NativeCoefficients.G0_exact X) n a, KMap (P5NativeCoefficients.G1_exact X) n a) :=
  Product.KEquiv_pair_apply (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj)
    (FlasqueBoundedBelow.waldhausen X.obj) (FlasqueBoundedBelow.waldhausen X.obj)
    (P5NativeCoefficients.G0_exact X) (P5NativeCoefficients.G1_exact X) n a

/-- The actual GPhi map with the unchanged original product K-equivalence at both ends. -/
def GPhiPairKMap (n : ℕ) :
    (FlasqueBoundedBelow.waldhausen X.obj).K n × (FlasqueBoundedBelow.waldhausen X.obj).K n →*
      (FlasqueBoundedBelow.waldhausen X.obj).K n × (FlasqueBoundedBelow.waldhausen X.obj).K n :=
  (Product.KEquiv (FlasqueBoundedBelow.waldhausen X.obj) (FlasqueBoundedBelow.waldhausen X.obj)
    n).toMonoidHom.comp ((KMap (P5NativeCoefficients.G_exact X) n).comp
      (P5NativePhi.PhiTwoSummandKMap X n))

/-- Negative vanishing and actual signed Euler additivity give the two original positive diagonals.
-/
theorem GPhiPairKMap_apply_eq_diagonal (n : ℕ)
    (a b : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    GPhiPairKMap X n (a, b) = (KMap (G0First_exact X) n a, KMap (G0First_exact X) n b) := by
  change Product.KEquiv _ _ n (KMap (P5NativeCoefficients.G_exact X) n
    (P5NativePhi.PhiTwoSummandKMap X n (a, b))) = _
  rw [G_KEquiv_apply, G0_Phi_apply, G1_Phi_apply]

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries
