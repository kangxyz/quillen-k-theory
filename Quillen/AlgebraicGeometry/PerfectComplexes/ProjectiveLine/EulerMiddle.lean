/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.EulerNegative

/-! # Original middle Euler coefficient and its canonical natural weak-zero map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.Euler
open FlasqueCoefficients
variable (R : CommRingCat.{u})

local instance eulerMiddleStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

local instance derivedPlusQ_additive (X : Scheme.{u}) :
    (DerivedCategory.Plus.Q (C := X.Modules)).Additive := by
  dsimp [DerivedCategory.Plus.Q]
  infer_instance

local instance derivedProjection_additive :
    (derivedPushforwardPlus (projection R)).Additive := by
  dsimp [derivedPushforwardPlus]
  infer_instance

/-- Tensor with the fixed original coefficient complex is functorial in the Euler module. -/
def coefficientTensorFunctor (A : StrictPerfect (Spec R)) :
    (twoChartLine R).Modules ⥤ CochainComplex.Plus (twoChartLine R).Modules where
  obj M := ⟨(endpointComplex R M).obj A, by
    obtain ⟨a, b, hab⟩ := A.property.1
    let : A.obj.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ a).mpr
      (fun i hi => hab i (Or.inl hi))
    exact ⟨a, endpointComplex_isStrictlyGE R M A a⟩⟩
  map f := ObjectProperty.homMk
    (((moduleTensorCoefficientMap (twoChartLine R) f).mapHomologicalComplex (.up ℤ)).app
      ((pullbackComplex (projection R)).obj A.obj))
  map_id M := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.Hom.ext
    funext n
    exact (moduleTensorByLineRight
      (((pullbackComplex (projection R)).obj A.obj).X n)).map_id M
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.Hom.ext
    funext n
    exact (moduleTensorByLineRight
      (((pullbackComplex (projection R)).obj A.obj).X n)).map_comp f g

instance coefficientTensorFunctor_additive (A : StrictPerfect (Spec R)) :
    (coefficientTensorFunctor R A).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.Hom.ext
    funext n
    exact Functor.map_add (moduleTensorByLineRight
      (((pullbackComplex (projection R)).obj A.obj).X n))

/-- Original sheafified tensor and installed derived projection with the original coefficient. -/
def coefficientDerivedProjection (A : StrictPerfect (Spec R)) :
    (twoChartLine R).Modules ⥤ DerivedCategory.Plus (Spec R).Modules :=
  coefficientTensorFunctor R A ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (projection R)

instance coefficientDerivedProjection_additive (A : StrictPerfect (Spec R)) :
    (coefficientDerivedProjection R A).Additive := by
  unfold coefficientDerivedProjection
  infer_instance

/-- Fixed original middle distribution and actual preserved biproduct tensor distribution. -/
def middleDerivedBiprodIso (A : StrictPerfect (Spec R)) :
    (coefficientDerivedProjection R A).obj (sequence R).X₂ ≅
      (coefficientDerivedProjection R A).obj (tautologicalLine R) ⊞
        (coefficientDerivedProjection R A).obj (tautologicalLine R) :=
  (coefficientDerivedProjection R A).mapIso (middleIso R) ≪≫
    (coefficientDerivedProjection R A).mapBiprod (tautologicalLine R) (tautologicalLine R)

lemma middleEndpoint_derived_zero (A : StrictPerfect (Spec R)) :
    IsZero ((coefficientDerivedProjection R A).obj (sequence R).X₂) := by
  have hz : IsZero ((coefficientDerivedProjection R A).obj (tautologicalLine R)) :=
    negativeEndpoint_derived_zero R A
  exact ((biprod_isZero_iff _ _).mpr ⟨hz, hz⟩).of_iso (middleDerivedBiprodIso R A)

/-- The middle endpoint before totalization as its actual lower-bounded complex. -/
def middlePlus : StrictPerfect (Spec R) ⥤ CochainComplex.Plus (twoChartLine R).Modules :=
  endpointBounded R (sequence R).X₂ (middleEndpoint_strictPerfect R) ⋙
    boundedToPlus (twoChartLine R)

/-- Forgetting predicates retains the original totalized, projected middle and its maps. -/
def middleProjectedPlusIso : E1 R ⋙ toPlus (Spec R) ≅
    middlePlus R ⋙ godementTotalPlus (twoChartLine R) ⋙
      (Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    apply ObjectProperty.hom_ext
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

/-- Both components are the installed original Godement unit and augmentation. -/
def middleProjectedDerivedIso : E1 R ⋙ toPlus (Spec R) ⋙ DerivedCategory.Plus.Q ≅
    middlePlus R ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (projection R) :=
  Functor.isoWhiskerRight (middleProjectedPlusIso R) DerivedCategory.Plus.Q ≪≫
    Functor.isoWhiskerLeft (middlePlus R) (godementTotalDerivedPushforwardIso (projection R))

/-- Actual middle acyclicity follows from negative vanishing and the retained biproduct maps. -/
lemma middleProjected_derived_zero (A : StrictPerfect (Spec R)) :
    IsZero (DerivedCategory.Plus.Q.obj ((toPlus (Spec R)).obj ((E1 R).obj A))) :=
  (middleEndpoint_derived_zero R A).of_iso ((middleProjectedDerivedIso R).app A)

/-- A derived-zero original bounded-below model value maps weakly to its original chosen zero. -/
lemma model_to_zero_weak {X : Scheme.{u}} (K : FlasqueBoundedBelow.Obj X)
    (hK : IsZero (DerivedCategory.Plus.Q.obj ((toPlus X).obj K))) :
    (FlasqueBoundedBelow.waldhausen X).weq
      (0 : K ⟶ (FlasqueBoundedBelow.waldhausen X).zero) := by
  let W := FlasqueBoundedBelow.waldhausen X
  have hz : IsZero (DerivedCategory.Q.obj K.obj) :=
    (DerivedCategory.Plus.ι (C := X.Modules)).map_isZero hK
  have hzero : IsZero (DerivedCategory.Q.obj W.zero.obj) :=
    (DerivedCategory.Q (C := X.Modules)).map_isZero
      ((FlasqueBoundedBelow.objects X).ι.map_isZero W.isZero)
  change QuasiIso (0 : K.obj ⟶ W.zero.obj)
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules (0 : K.obj ⟶ W.zero.obj)).mp
  exact hz.isIso hzero _

/-- The literal zero maps are a natural transformation to the original chosen-zero functor. -/
def middleToZero : E1 R ⟶ Waldhausen.zeroFunctor (FlasqueBoundedBelow.waldhausen (Spec R)) := 0

lemma middleToZero_weak (A : StrictPerfect (Spec R)) :
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq ((middleToZero R).app A) :=
  model_to_zero_weak _ (middleProjected_derived_zero R A)

/-- The original chosen-zero K-map of the actual middle vanishes, including degree zero. -/
lemma KMap_E1_zero (n : ℕ) : Waldhausen.KMap (E1_exact R) n = 1 :=
  (Waldhausen.KMap_eq_of_weakNatTrans (E1_exact R)
    (Waldhausen.zeroFunctor_isExact (strictWaldhausen (Spec R))
      (FlasqueBoundedBelow.waldhausen (Spec R)))
    (middleToZero R) (middleToZero_weak R) n).trans (Waldhausen.KMap_zeroFunctor _ _ n)

end Quillen.PerfectComplexes.ProjectiveLine.Euler
