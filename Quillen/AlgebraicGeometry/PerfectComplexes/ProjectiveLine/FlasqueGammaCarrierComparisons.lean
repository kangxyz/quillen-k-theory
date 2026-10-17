/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Carriers


public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Carrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueGammaThirdSpan
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.OriginalLineGodementContractions

/-! # Canonical proof-forgetting carriers of the actual Gamma contraction functors -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueTensorAdditivity
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueThirdEndpoint

open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
open FlasqueTensorAdditivity FlasqueThirdEndpoint

/-- Lift a natural cochain map to the original full model without replacing any objects. -/
def liftModelNatTrans {C D : Type*} [Category C] [Category D] (P : ObjectProperty D)
    {F G : C ⥤ P.FullSubcategory} (a : F ⋙ P.ι ⟶ G ⋙ P.ι) : F ⟶ G where
  app K := ObjectProperty.homMk (a.app K)
  naturality {_K _L} f := ObjectProperty.hom_ext _ (a.naturality f)

/-- A proved original Plus map transported through the named actual cochain carrier isos. -/
def liftPlusModelNatTrans {C : Type*} [Category C] (X : Scheme.{u})
    {F G : C ⥤ FlasqueBoundedBelow.Obj X} {A B : C ⥤ CochainComplex.Plus X.Modules}
    (eF : F ⋙ (FlasqueBoundedBelow.objects X).ι ≅ A ⋙ CochainComplex.Plus.ι X.Modules)
    (eG : G ⋙ (FlasqueBoundedBelow.objects X).ι ≅ B ⋙ CochainComplex.Plus.ι X.Modules)
    (a : A ⟶ B) : F ⟶ G :=
  liftModelNatTrans (FlasqueBoundedBelow.objects X)
    (eF.hom ≫ whiskerRight a (CochainComplex.Plus.ι X.Modules) ≫ eG.inv)

/-- Weakness is proved at the generic symbolic carrier boundary, before concrete evaluation. -/
lemma liftPlusModelNatTrans_weak {C : Type*} [Category C] (X : Scheme.{u})
    {F G : C ⥤ FlasqueBoundedBelow.Obj X} {A B : C ⥤ CochainComplex.Plus X.Modules}
    (eF : F ⋙ (FlasqueBoundedBelow.objects X).ι ≅ A ⋙ CochainComplex.Plus.ι X.Modules)
    (eG : G ⋙ (FlasqueBoundedBelow.objects X).ι ≅ B ⋙ CochainComplex.Plus.ι X.Modules)
    (a : A ⟶ B) (ha : ∀ K, QuasiIso (a.app K).hom) (K : C) :
    (FlasqueBoundedBelow.waldhausen X).weq ((liftPlusModelNatTrans X eF eG a).app K) := by
  let : QuasiIso (a.app K).hom := ha K
  change QuasiIso (eF.hom.app K ≫ (a.app K).hom ≫ eG.inv.app K)
  infer_instance

/-- The natural identification of the underlying negative twist with left tensor by the tautological
line.
-/
def negativeCarrierIso (R : CommRingCat.{u}) :
    FlasqueTwoSummands.boundedNegativeTwist R ⋙ (BoundedBelow.objects (twoChartLine R)).ι ≅
      (BoundedBelow.objects (twoChartLine R)).ι ⋙
        AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R) := by
  unfold FlasqueTwoSummands.boundedNegativeTwist
  exact ObjectProperty.liftCompιIso _ _ _

/-- Actual Gamma before forgetting, through only its actual lift carriers and associators. -/
def GammaCarrierIso (R : CommRingCat.{u}) :
    Gamma R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι ≅
      (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
        AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R) ⋙ godementTotal
          (twoChartLine R) := by
  let P := twoChartLine R
  let I := FlasqueBoundedBelow.inclusion P
  let B := FlasqueTwoSummands.boundedNegativeTwist R
  let T := FlasqueBoundedBelow.total P
  let J := (BoundedBelow.objects P).ι
  let K := (FlasqueBoundedBelow.objects P).ι
  let L := AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)
  let V := godementTotal P
  let eB := (associator B T K ≪≫ isoWhiskerLeft B (totalCarrierIso P) ≪≫ (associator B J V).symm ≪≫
    isoWhiskerRight (negativeCarrierIso R) V ≪≫ associator J L V)
  let eI : I ⋙ J ≅ K ⋙ 𝟭 (CochainComplex P.Modules ℤ) :=
    inclusionCarrierIso P ≪≫ (Functor.rightUnitor K).symm
  exact isoWhiskerRight (associator I B T) K ≪≫
    (associator I (B ⋙ T) K ≪≫ isoWhiskerLeft I eB ≪≫ (associator I J (L ⋙ V)).symm ≪≫
      isoWhiskerRight eI (L ⋙ V) ≪≫ associator K (𝟭 (CochainComplex P.Modules ℤ)) (L ⋙ V)) ≪≫
    isoWhiskerLeft K (Functor.leftUnitor (L ⋙ V))

/-- The chosen actual bounded tensor followed by total and Gamma keeps the same four factors. -/
def actualResolvedCarrierIso {C : Type*} [Category C] (R : CommRingCat.{u})
    (A : C ⥤ BoundedBelow.Obj (twoChartLine R)) (I : C ⥤ CochainComplex (twoChartLine R).Modules ℤ)
    (F : CochainComplex (twoChartLine R).Modules ℤ ⥤ CochainComplex (twoChartLine R).Modules ℤ)
    (e : A ⋙ (BoundedBelow.objects (twoChartLine R)).ι ≅ I ⋙ F) :
    ((A ⋙ FlasqueBoundedBelow.total (twoChartLine R)) ⋙ Gamma R) ⋙
        (FlasqueBoundedBelow.objects (twoChartLine R)).ι ≅
      I ⋙ (F ⋙ godementTotal (twoChartLine R)) ⋙
        (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R) ⋙ godementTotal
          (twoChartLine R)) := by
  let P := twoChartLine R
  let B := (BoundedBelow.objects P).ι
  let K := (FlasqueBoundedBelow.objects P).ι
  let T := FlasqueBoundedBelow.total P
  let V := godementTotal P
  let L := AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)
  let eA := (associator A T K ≪≫ isoWhiskerLeft A (totalCarrierIso P) ≪≫ (associator A B V).symm ≪≫
    isoWhiskerRight e V ≪≫ associator I F V)
  exact (associator (A ⋙ T) (Gamma R) K ≪≫ isoWhiskerLeft (A ⋙ T) (GammaCarrierIso R) ≪≫ (associator
    (A ⋙ T) K (L ⋙ V)).symm ≪≫ isoWhiskerRight eA (L ⋙ V) ≪≫ associator I (F ⋙ V) (L ⋙ V))

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
