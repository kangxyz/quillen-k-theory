/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Carrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueGammaThirdSpan
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.OriginalLineGodementContractions

/-! # Canonical proof-forgetting carriers of the actual Gamma contraction functors -/
@[expose] public section
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

/-- The original bounded object with only its original bound proof forgotten to Plus. -/
def boundedToPlus (X : Scheme.{u}) : BoundedBelow.Obj X ⥤ CochainComplex.Plus X.Modules :=
  ObjectProperty.lift _ (BoundedBelow.objects X).ι (fun K => K.property.2)

def boundedToPlusCarrierIso (X : Scheme.{u}) :
    boundedToPlus X ⋙ CochainComplex.Plus.ι X.Modules ≅ (BoundedBelow.objects X).ι :=
  ObjectProperty.liftCompιIso _ _ _

/-- This uses the generic lift carrier, leaving the entire actual total functor opaque. -/
def totalCarrierIso (X : Scheme.{u}) :
    FlasqueBoundedBelow.total X ⋙ (FlasqueBoundedBelow.objects X).ι ≅
      (BoundedBelow.objects X).ι ⋙ godementTotal X := by
  unfold FlasqueBoundedBelow.total
  exact ObjectProperty.liftCompιIso _ _ _

def inclusionCarrierIso (X : Scheme.{u}) :
    FlasqueBoundedBelow.inclusion X ⋙ (BoundedBelow.objects X).ι ≅
      (FlasqueBoundedBelow.objects X).ι := by
  unfold FlasqueBoundedBelow.inclusion
  exact Iso.refl _

def negativeCarrierIso (R : CommRingCat.{u}) :
    FlasqueTwoSummands.boundedNegativeTwist R ⋙ (BoundedBelow.objects (twoChartLine R)).ι ≅
      (BoundedBelow.objects (twoChartLine R)).ι ⋙ tensorByLineComplex (tautologicalLine R) := by
  unfold FlasqueTwoSummands.boundedNegativeTwist
  exact ObjectProperty.liftCompιIso _ _ _

/-- Actual Gamma before forgetting, through only its actual lift carriers and associators. -/
def GammaCarrierIso (R : CommRingCat.{u}) :
    Gamma R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι ≅
      (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
        tensorByLineComplex (tautologicalLine R) ⋙ godementTotal (twoChartLine R) := by
  let P := twoChartLine R
  let I := FlasqueBoundedBelow.inclusion P
  let B := FlasqueTwoSummands.boundedNegativeTwist R
  let T := FlasqueBoundedBelow.total P
  let J := (BoundedBelow.objects P).ι
  let K := (FlasqueBoundedBelow.objects P).ι
  let L := tensorByLineComplex (tautologicalLine R)
  let V := godementTotal P
  let eB := forgetComposeIso B T L V J J K (negativeCarrierIso R) (totalCarrierIso P)
  let eI : I ⋙ J ≅ K ⋙ 𝟭 (Complex P) :=
    inclusionCarrierIso P ≪≫ (Functor.rightUnitor K).symm
  exact isoWhiskerRight (associator I B T) K ≪≫
    forgetComposeIso I (B ⋙ T) (𝟭 (Complex P)) (L ⋙ V) K J K eI eB ≪≫
    isoWhiskerLeft K (Functor.leftUnitor (L ⋙ V))

/-- The chosen actual bounded tensor followed by total and Gamma keeps the same four factors. -/
def actualResolvedCarrierIso {C : Type*} [Category C] (R : CommRingCat.{u})
    (A : C ⥤ BoundedBelow.Obj (twoChartLine R)) (I : C ⥤ Complex (twoChartLine R))
    (F : Complex (twoChartLine R) ⥤ Complex (twoChartLine R))
    (e : A ⋙ (BoundedBelow.objects (twoChartLine R)).ι ≅ I ⋙ F) :
    ((A ⋙ FlasqueBoundedBelow.total (twoChartLine R)) ⋙ Gamma R) ⋙
        (FlasqueBoundedBelow.objects (twoChartLine R)).ι ≅
      I ⋙ (F ⋙ godementTotal (twoChartLine R)) ⋙
        (tensorByLineComplex (tautologicalLine R) ⋙ godementTotal (twoChartLine R)) := by
  let P := twoChartLine R
  let B := (BoundedBelow.objects P).ι
  let K := (FlasqueBoundedBelow.objects P).ι
  let T := FlasqueBoundedBelow.total P
  let V := godementTotal P
  let L := tensorByLineComplex (tautologicalLine R)
  let eA := forgetComposeIso A T F V I B K e (totalCarrierIso P)
  exact forgetComposeIso (A ⋙ T) (Gamma R) (F ⋙ V) (L ⋙ V) I K K eA (GammaCarrierIso R)

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
