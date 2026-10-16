/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.PushforwardQuasiIso
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FirstEndpointCoefficient

/-!
# The literal original first-endpoint beta

The original Efirst maps through the inverse tautological coefficient comparison
and the actual pulled augmentation into U(T_P(K tensor L)). Both complexes are
literal ordinary second images of actual flasque totals. No arbitrary ordinary
pushforward exactness or second-projection perfect-pushforward premise is used.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
open FlasqueCoefficients
variable (R : CommRingCat.{u})

/-- The literal original first diagonal model endpoint, with no outer total. -/
abbrev originalFirst := FlasqueDiagonal.E R .first

/-- The literal original ordinary self-base-change target on the resolved right coefficient. -/
def comparisonTarget := resolved R ⋙ SelfBaseChange.target R

/-- The literal original first coefficient complex, before totalization. -/
def originalFirstComplex (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    CochainComplex (relativeSquare R).Modules ℤ :=
  ((FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ)).obj K.obj

/-- The literal original first pullback of the actual M coefficient. -/
def pulledResolvedComplex (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    CochainComplex (relativeSquare R).Modules ℤ :=
  (AlgebraicGeometry.Scheme.Modules.Complex.pullback (relativeFirst R)).obj ((resolved R).obj K).obj

/-- The original coefficient map is typed BEFORE applying totalization. -/
def coefficientChainMap (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    originalFirstComplex R K ⟶ pulledResolvedComplex R K :=
  ((coefficientMap R).app K).hom

lemma coefficientChainMap_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso (coefficientChainMap R K) := coefficientMap_quasiIso R K

lemma coefficientChainMap_naturality {K L : FlasqueBoundedBelow.Obj (twoChartLine R)}
    (f : K ⟶ L) :
    ((FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ)).map f.hom ≫
        coefficientChainMap R L = coefficientChainMap R K ≫
      (AlgebraicGeometry.Scheme.Modules.Complex.pullback (relativeFirst R)).map ((resolved R).map
        f).hom :=
  congrArg (CochainComplex.Plus.ι (relativeSquare R).Modules).map
    ((coefficientMap R).naturality f)

/-- Literal ordinary second image of literal total of the actual typed coefficient map. -/
def betaChainMap (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((originalFirst R).obj K).obj ⟶ ((comparisonTarget R).obj K).obj :=
  ((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)).map
    ((godementTotal (relativeSquare R)).map (coefficientChainMap R K))

lemma betaChainMap_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso (betaChainMap R K) := by
  let X : CochainComplex.Plus (relativeSquare R).Modules :=
    ⟨originalFirstComplex R K, ((originalFirstPlus R).obj K).property⟩
  let Y : CochainComplex.Plus (relativeSquare R).Modules :=
    ⟨pulledResolvedComplex R K, ((pulledResolvedPlus R).obj K).property⟩
  let g : X ⟶ Y := ObjectProperty.homMk (coefficientChainMap R K)
  have : QuasiIso g.hom := coefficientChainMap_quasiIso R K
  exact AlgebraicGeometry.Scheme.Modules.Godement.totalPushforwardPlus_quasiIso (relativeSecond R) g

lemma originalFirst_map_hom {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    ((originalFirst R).map f).hom =
      ((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal (relativeSquare R)).map
          (((FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ)).map f.hom)) := rfl

lemma comparisonTarget_map_hom {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    ((comparisonTarget R).map f).hom =
      ((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal (relativeSquare R)).map
          ((AlgebraicGeometry.Scheme.Modules.Complex.pullback (relativeFirst R)).map ((resolved
            R).map f).hom)) := rfl

/-- The actual pre-total coefficient chain transformation, forgetting only its Plus proofs. -/
def coefficientRawMap :
    originalFirstPlus R ⋙ CochainComplex.Plus.ι (relativeSquare R).Modules ⟶
      pulledResolvedPlus R ⋙ CochainComplex.Plus.ι (relativeSquare R).Modules :=
  CategoryTheory.Functor.whiskerRight (coefficientMap R)
    (CochainComplex.Plus.ι (relativeSquare R).Modules)

/-- Forget only the original Plus proof, before applying a total functor. -/
def modelToPlusEraseIso (X : Scheme.{u}) :
    toPlus X ⋙ CochainComplex.Plus.ι X.Modules ≅ (FlasqueBoundedBelow.objects X).ι := Iso.refl _

/-- Native exact coefficient erasure before any totalization. -/
def coefficientEraseIso :
    originalFirstPlus R ⋙ CochainComplex.Plus.ι (relativeSquare R).Modules ≅
      (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
        (FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ) :=
  Functor.associator (toPlus (twoChartLine R))
      (FlasqueDiagonal.coefficient R .first).mapCochainComplexPlus
      (CochainComplex.Plus.ι (relativeSquare R).Modules) ≪≫
    Functor.isoWhiskerLeft (toPlus (twoChartLine R))
      (FlasqueDiagonal.coefficient R .first).mapCochainComplexPlusCompι ≪≫
    (Functor.associator (toPlus (twoChartLine R)) (CochainComplex.Plus.ι (twoChartLine R).Modules)
      ((FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ))).symm ≪≫
    Functor.isoWhiskerRight (modelToPlusEraseIso (twoChartLine R))
      ((FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ))

/-- Native resolved-coefficient pullback erasure, before applying totalization. -/
def pulledEraseIso :
    pulledResolvedPlus R ⋙ CochainComplex.Plus.ι (relativeSquare R).Modules ≅
      (resolved R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι) ⋙
        AlgebraicGeometry.Scheme.Modules.Complex.pullback (relativeFirst R) :=
  let M := resolved R
  let F := toPlus (twoChartLine R)
  let A := Scheme.Modules.pullback (relativeFirst R)
  let I := CochainComplex.Plus.ι (twoChartLine R).Modules
  let J := CochainComplex.Plus.ι (relativeSquare R).Modules
  Functor.associator (M ⋙ F) A.mapCochainComplexPlus J ≪≫
    Functor.isoWhiskerLeft (M ⋙ F) A.mapCochainComplexPlusCompι ≪≫
    (Functor.associator (M ⋙ F) I (AlgebraicGeometry.Scheme.Modules.Complex.pullback (relativeFirst
      R))).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator M F I)
      (AlgebraicGeometry.Scheme.Modules.Complex.pullback (relativeFirst R)) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft M (modelToPlusEraseIso (twoChartLine R)))
      (AlgebraicGeometry.Scheme.Modules.Complex.pullback (relativeFirst R))

/-- The actual original raw coefficient transformation, transported before totalization. -/
def coefficientActualRawMap :
    (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
        (FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ) ⟶
      (resolved R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι) ⋙
        AlgebraicGeometry.Scheme.Modules.Complex.pullback (relativeFirst R) :=
  (coefficientEraseIso R).inv ≫ coefficientRawMap R ≫ (pulledEraseIso R).hom

/-- Literal total and image of the actual original coefficient chain transformation. -/
def betaRawMap :
    (((FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
      (FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ)) ⋙
        godementTotal (relativeSquare R)) ⋙
          (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ) ⟶
    (((resolved R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι) ⋙
      AlgebraicGeometry.Scheme.Modules.Complex.pullback (relativeFirst R)) ⋙ godementTotal
        (relativeSquare R)) ⋙
        (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ) :=
  CategoryTheory.Functor.whiskerRight
    (CategoryTheory.Functor.whiskerRight (coefficientActualRawMap R)
      (godementTotal (relativeSquare R)))
    ((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ))

/-- Actual source model erasure and only native associations of its literal functors. -/
def betaSourceIso :
    originalFirst R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι ≅
      (((FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
        (FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ)) ⋙
          godementTotal (relativeSquare R)) ⋙
            (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ) :=
  eqToIso (FlasqueDiagonal.E_underlying R .first) ≪≫
    (Functor.associator (FlasqueBoundedBelow.objects (twoChartLine R)).ι
      ((FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ))
      (godementTotal (relativeSquare R) ⋙
        (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ))).symm ≪≫
    (Functor.associator
      ((FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
        (FlasqueDiagonal.coefficient R .first).mapHomologicalComplex (.up ℤ))
      (godementTotal (relativeSquare R))
      ((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ))).symm

/-- The base target erasure retains its literal original ordinary-total-pullback functor. -/
def baseTargetEraseIso :
    SelfBaseChange.target R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι ≅
      SelfBaseChange.targetRaw R := Iso.refl _

/-- Only native associations and erasure of the actual original U(M) endpoint. -/
def betaTargetIso :
    (((resolved R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι) ⋙
      AlgebraicGeometry.Scheme.Modules.Complex.pullback (relativeFirst R)) ⋙ godementTotal
        (relativeSquare R)) ⋙
        (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ) ≅
      comparisonTarget R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι :=
  let M := resolved R
  let I := (FlasqueBoundedBelow.objects (twoChartLine R)).ι
  let A := AlgebraicGeometry.Scheme.Modules.Complex.pullback (relativeFirst R)
  let T := godementTotal (relativeSquare R)
  let B := (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)
  Functor.associator ((M ⋙ I) ⋙ A) T B ≪≫
    Functor.associator (M ⋙ I) A (T ⋙ B) ≪≫
    Functor.associator M I (A ⋙ (T ⋙ B)) ≪≫
    Functor.isoWhiskerLeft M (baseTargetEraseIso R).symm ≪≫
    (Functor.associator M (SelfBaseChange.target R) I).symm

/-- Actual natural beta with both original model endpoints, retaining original raw maps. -/
def betaUnderlying :
    originalFirst R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⟶
      comparisonTarget R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι :=
  (betaSourceIso R).hom ≫ betaRawMap R ≫ (betaTargetIso R).hom

/-- Fully faithful erasure lifts the actual raw natural transformation without choosing objects. -/
def beta : originalFirst R ⟶ comparisonTarget R :=
  ((FlasqueBoundedBelow.objects (twoChartLine R)).fullyFaithfulι.whiskeringRight
    (FlasqueBoundedBelow.Obj (twoChartLine R))).preimage (betaUnderlying R)

/-- The same original beta, forgetting only model proofs through the actual Plus inclusion. -/
def betaPlus : originalFirst R ⋙ toPlus (twoChartLine R) ⟶
    comparisonTarget R ⋙ toPlus (twoChartLine R) :=
  CategoryTheory.Functor.whiskerRight (beta R) (toPlus (twoChartLine R))

lemma betaPlus_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((betaPlus R).app K).hom = (betaUnderlying R).app K := rfl

lemma coefficientActualRawMap_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((coefficientActualRawMap R).app K) := by
  have : QuasiIso ((coefficientRawMap R).app K) := coefficientMap_quasiIso R K
  change QuasiIso ((coefficientEraseIso R).inv.app K ≫
    (coefficientRawMap R).app K ≫ (pulledEraseIso R).hom.app K)
  infer_instance

lemma betaRawMap_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (betaRawMap R).app K =
      ((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal (relativeSquare R)).map ((coefficientActualRawMap R).app K)) := rfl

lemma betaRawMap_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((betaRawMap R).app K) := by
  let X : CochainComplex.Plus (relativeSquare R).Modules :=
    ⟨originalFirstComplex R K, ((originalFirstPlus R).obj K).property⟩
  let Y : CochainComplex.Plus (relativeSquare R).Modules :=
    ⟨pulledResolvedComplex R K, ((pulledResolvedPlus R).obj K).property⟩
  let g : X ⟶ Y := ObjectProperty.homMk ((coefficientActualRawMap R).app K)
  have : QuasiIso g.hom := coefficientActualRawMap_quasiIso R K
  rw [betaRawMap_app]
  exact AlgebraicGeometry.Scheme.Modules.Godement.totalPushforwardPlus_quasiIso (relativeSecond R) g

private lemma quasiIso_triple_app {D : Type*} [Category D] (X : Scheme.{u})
    {F G H I : D ⥤ CochainComplex X.Modules ℤ} (f : F ⟶ G) (g : G ⟶ H) (h : H ⟶ I) (K : D)
    (hf : QuasiIso (f.app K)) (hg : QuasiIso (g.app K)) (hh : QuasiIso (h.app K)) :
    QuasiIso ((f ≫ g ≫ h).app K) := by
  let := hf
  let := hg
  let := hh
  change QuasiIso (f.app K ≫ g.app K ≫ h.app K)
  infer_instance

lemma betaUnderlying_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((betaUnderlying R).app K) :=
  quasiIso_triple_app (twoChartLine R) (betaSourceIso R).hom (betaRawMap R)
    (betaTargetIso R).hom K (by infer_instance) (betaRawMap_quasiIso R K) (by infer_instance)

lemma betaPlus_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((betaPlus R).app K).hom := by
  rw [betaPlus_hom_app]
  exact betaUnderlying_quasiIso R K

lemma beta_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((beta R).app K).hom = ((betaPlus R).app K).hom := rfl

lemma beta_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((beta R).app K) :=
  betaPlus_quasiIso R K

/-- Both literal original endpoint functors are genuinely exact. -/
lemma originalFirst_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (originalFirst R) :=
  FlasqueDiagonal.E_exact R .first

lemma comparisonTarget_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (comparisonTarget R) :=
  (rightTensorTotal_exact R).comp (SelfBaseChange.target_exact R)

/-- The resolved right coefficient retains each specified original strict lower bound. -/
lemma resolved_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((resolved R).obj K).obj.IsStrictlyGE a := by
  have : ((rightTensor R).obj K).obj.IsStrictlyGE a := rightTensor_isStrictlyGE R K.obj a
  exact FlasqueBoundedBelow.total_isStrictlyGE (twoChartLine R) ((rightTensor R).obj K) a

lemma comparisonTarget_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((comparisonTarget R).obj K).obj.IsStrictlyGE a := by
  let := resolved_isStrictlyGE R K a
  exact SelfBaseChange.targetRaw_isStrictlyGE R ((resolved R).obj K) a

lemma originalFirst_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((originalFirst R).obj K).obj.IsStrictlyGE a :=
  FlasqueDiagonal.raw_isStrictlyGE R .first K a

/-- Naturality retains every actual original complex map. -/
@[reassoc]
lemma beta_naturality {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    (originalFirst R).map f ≫ (beta R).app L =
      (beta R).app K ≫ (comparisonTarget R).map f := (beta R).naturality f

end Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
