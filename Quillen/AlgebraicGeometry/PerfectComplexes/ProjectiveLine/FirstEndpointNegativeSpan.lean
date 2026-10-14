/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FirstEndpointSpan
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FirstEndpointNativeSource

/-!
# Actual original negative first-endpoint weak span

The original unshifted right-line coefficient followed by the native negative
Phi column maps into T_P(L LEFTtensor U(M)). The original first diagonal
endpoint, tensored on the left with L and then actually totalized, maps into
the same center. Both arrows are the images of the actual alpha and beta;
no line tensor is assumed flasque and no total-shift isomorphism is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
open FlasqueCoefficients
variable (R : CommRingCat.{u})

/-- Literal native LEFT-line tensor followed by the actual Godement total. -/
def negativeTotal := FlasqueTwoSummands.boundedNegativeTwist R ⋙
  FlasqueBoundedBelow.total (twoChartLine R)

lemma negativeTotal_exact : Waldhausen.IsExact
    (BoundedBelow.waldhausen (twoChartLine R)).cof (BoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (negativeTotal R) :=
  (FlasqueTwoSummands.boundedNegativeTwist_exact R).comp
    (FlasqueBoundedBelow.total_exact (twoChartLine R))

/-- The prescribed original unshifted negative PhiG column. -/
def negativeSpanLeft := unshiftedCoefficient R ⋙ nativeNegative R

/-- The actual common center T_P(L LEFTtensor U(M)). -/
def negativeSpanCenter := centerBounded R ⋙ negativeTotal R

/-- The literal original first diagonal endpoint under LEFT line tensor then T_P. -/
def negativeSpanRight :=
  (originalFirst R ⋙ FlasqueBoundedBelow.inclusion (twoChartLine R)) ⋙ negativeTotal R

/-- Original negative source identification, then actual LEFT tensor and total of alpha. -/
def negativeSpanLeftMap : negativeSpanLeft R ⟶ negativeSpanCenter R :=
  (nativeNegativeSourceIso R).hom ≫
    CategoryTheory.Functor.whiskerRight (alpha R) (negativeTotal R)

/-- Actual LEFT tensor and Godement total of the original beta arrow. -/
def negativeSpanRightMap : negativeSpanRight R ⟶ negativeSpanCenter R :=
  CategoryTheory.Functor.whiskerRight (betaBounded R) (negativeTotal R)

lemma negativeSpanLeftMap_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (negativeSpanLeftMap R).app K = (nativeNegativeSourceIso R).hom.app K ≫
      (negativeTotal R).map ((alpha R).app K) := rfl

lemma negativeSpanRightMap_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (negativeSpanRightMap R).app K =
      (negativeTotal R).map ((betaBounded R).app K) := rfl

lemma negativeSpanLeftMap_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
      ((negativeSpanLeftMap R).app K) := by
  rw [negativeSpanLeftMap_app]
  exact (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
    ((FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance)
    ((negativeTotal_exact R).weak ((alpha R).app K) (alpha_weak R K))

lemma negativeSpanRightMap_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
      ((negativeSpanRightMap R).app K) :=
  (negativeTotal_exact R).weak ((betaBounded R).app K) (betaBounded_weak R K)

lemma negativeSpanLeft_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (negativeSpanLeft R) :=
  ((rightTensorTotal_exact R).comp (G0_exact R)).comp
    ((FlasqueTwoSummands.second_exact R).comp
      (FlasqueBoundedBelow.total_exact (twoChartLine R)))

lemma negativeSpanCenter_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (negativeSpanCenter R) :=
  (centerBounded_exact R).comp (negativeTotal_exact R)

lemma negativeSpanRight_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (negativeSpanRight R) :=
  ((originalFirst_exact R).comp (FlasqueBoundedBelow.inclusion_exact (twoChartLine R))).comp
    (negativeTotal_exact R)

lemma boundedNegativeTwist_isStrictlyGE (K : BoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((FlasqueTwoSummands.boundedNegativeTwist R).obj K).obj.IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)

lemma negativeTotal_isStrictlyGE (K : BoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((negativeTotal R).obj K).obj.IsStrictlyGE a := by
  let := boundedNegativeTwist_isStrictlyGE R K a
  exact FlasqueBoundedBelow.total_isStrictlyGE (twoChartLine R)
    ((FlasqueTwoSummands.boundedNegativeTwist R).obj K) a

lemma negativeSpanLeft_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((negativeSpanLeft R).obj K).obj.IsStrictlyGE a := by
  let := source_isStrictlyGE R K a
  have : (((source R ⋙ negativeTotal R).obj K).obj).IsStrictlyGE a :=
    negativeTotal_isStrictlyGE R ((source R).obj K) a
  let e : (((source R ⋙ negativeTotal R).obj K).obj) ≅
      ((negativeSpanLeft R).obj K).obj :=
    (FlasqueBoundedBelow.objects (twoChartLine R)).ι.mapIso
      ((nativeNegativeSourceIso R).app K).symm
  exact CochainComplex.isStrictlyGE_of_iso e a

lemma negativeSpanCenter_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((negativeSpanCenter R).obj K).obj.IsStrictlyGE a := by
  have : ((centerBounded R).obj K).obj.IsStrictlyGE a := comparisonTarget_isStrictlyGE R K a
  exact negativeTotal_isStrictlyGE R ((centerBounded R).obj K) a

lemma negativeSpanRight_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((negativeSpanRight R).obj K).obj.IsStrictlyGE a := by
  let I := FlasqueBoundedBelow.inclusion (twoChartLine R)
  have : ((originalFirst R ⋙ I).obj K).obj.IsStrictlyGE a := originalFirst_isStrictlyGE R K a
  exact negativeTotal_isStrictlyGE R ((originalFirst R ⋙ I).obj K) a

/-- Original maps remain natural on all flasque perfect inputs, including the zero ring. -/
@[reassoc]
lemma negativeSpanLeftMap_naturality {K L : FlasqueBoundedBelow.Obj (twoChartLine R)}
    (f : K ⟶ L) :
    (negativeSpanLeft R).map f ≫ (negativeSpanLeftMap R).app L =
      (negativeSpanLeftMap R).app K ≫ (negativeSpanCenter R).map f :=
  (negativeSpanLeftMap R).naturality f

@[reassoc]
lemma negativeSpanRightMap_naturality {K L : FlasqueBoundedBelow.Obj (twoChartLine R)}
    (f : K ⟶ L) :
    (negativeSpanRight R).map f ≫ (negativeSpanRightMap R).app L =
      (negativeSpanRightMap R).app K ≫ (negativeSpanCenter R).map f :=
  (negativeSpanRightMap R).naturality f

/-- Actual zero objects are preserved; the native chosen-zero rebasing therefore applies. -/
lemma negativeSpan_zero {K : FlasqueBoundedBelow.Obj (twoChartLine R)} (hK : IsZero K) :
    IsZero ((negativeSpanLeft R).obj K) ∧ IsZero ((negativeSpanCenter R).obj K) ∧
      IsZero ((negativeSpanRight R).obj K) :=
  ⟨(negativeSpanLeft_exact R).zero hK, (negativeSpanCenter_exact R).zero hK,
    (negativeSpanRight_exact R).zero hK⟩

end Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
