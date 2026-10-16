/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.Limits.Shapes.CoproductZero


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueNativePhiKMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientOne
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.StrictPositiveSourceComparison
public import Quillen.Waldhausen.Additivity.GroupMultiplication

/-!
# Original first diagonal of G composed with Phi on strict affine coefficients

The actual injected Phi contains its selected coproduct with a zero image.
The original coproduct inclusion compares that sum with its original summand.
The forward base augmentation is pulled and totalized before applying G0.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open AlgebraicGeometry.Scheme.Modules.Godement

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
open Quillen.PerfectComplexes.ProjectiveLine.StrictPositiveRetraction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiEntries
open StrictPositiveRetraction FlasqueTwoSummands FlasqueCoefficients

/-- The first actual chosen-zero embedding in the original product category. -/
def firstInjection (R : CommRingCat.{u}) :=
  Waldhausen.Additivity.firstEmbedding (FlasqueBoundedBelow.waldhausen (Spec R))

lemma firstInjection_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).cof
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).weq
    (firstInjection R) := Waldhausen.Additivity.firstEmbedding_isExact _

/-- The second actual chosen-zero embedding in the original product category. -/
def secondInjection (R : CommRingCat.{u}) :=
  Waldhausen.Additivity.secondEmbedding (FlasqueBoundedBelow.waldhausen (Spec R))

lemma secondInjection_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).cof
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).weq
    (secondInjection R) := Waldhausen.Additivity.secondEmbedding_isExact _

/-- The first original summand maps into the actual injected selected coproduct. -/
def firstSumUnit (R : CommRingCat.{u}) :
    first R ⟶ firstInjection R ⋙ beforeTotal R where
  app _ := coprod.inl
  naturality {_ _} f := by
    change (first R).map f ≫ coprod.inl =
      coprod.inl ≫ coprod.map ((first R).map f) ((second R).map (𝟙 _))
    simp

instance firstSumUnit_isIso (R : CommRingCat.{u}) : IsIso (firstSumUnit R) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  exact coprod_inl_isIso_of_isZero _ _
    ((second_exact R).zero (FlasqueBoundedBelow.waldhausen (Spec R)).isZero)

/-- The second original summand maps into the actual injected selected coproduct. -/
def secondSumUnit (R : CommRingCat.{u}) :
    second R ⟶ secondInjection R ⋙ beforeTotal R where
  app _ := coprod.inr
  naturality {_ _} f := by
    change (second R).map f ≫ coprod.inr =
      coprod.inr ≫ coprod.map ((first R).map (𝟙 _)) ((second R).map f)
    simp

instance secondSumUnit_isIso (R : CommRingCat.{u}) : IsIso (secondSumUnit R) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  exact coprod_inr_isIso_of_isZero _ _
    ((first_exact R).zero (FlasqueBoundedBelow.waldhausen (Spec R)).isZero)

/-- Actual totalized first summand before its selected zero coproduct comparison. -/
def firstTotal (R : CommRingCat.{u}) := first R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

lemma firstTotal_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (firstTotal R) :=
  (first_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

/-- Actual totalized negative summand, retaining the native left tensor order. -/
def secondTotal (R : CommRingCat.{u}) := second R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

lemma secondTotal_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (secondTotal R) :=
  (second_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

/-- Total of the original first coproduct inclusion, retaining its actual selected sum. -/
def firstPhiUnit (R : CommRingCat.{u}) : firstTotal R ⟶ firstInjection R ⋙ Phi R :=
  Functor.whiskerRight (firstSumUnit R) (FlasqueBoundedBelow.total (twoChartLine R)) ≫
    (Functor.associator (firstInjection R) (beforeTotal R)
      (FlasqueBoundedBelow.total (twoChartLine R))).hom

instance firstPhiUnit_isIso (R : CommRingCat.{u}) : IsIso (firstPhiUnit R) := by
  unfold firstPhiUnit
  infer_instance

/-- Total of the original second coproduct inclusion, retaining its actual selected sum. -/
def secondPhiUnit (R : CommRingCat.{u}) : secondTotal R ⟶ secondInjection R ⋙ Phi R :=
  Functor.whiskerRight (secondSumUnit R) (FlasqueBoundedBelow.total (twoChartLine R)) ≫
    (Functor.associator (secondInjection R) (beforeTotal R)
      (FlasqueBoundedBelow.total (twoChartLine R))).hom

instance secondPhiUnit_isIso (R : CommRingCat.{u}) : IsIso (secondPhiUnit R) := by
  unfold secondPhiUnit
  infer_instance

/-- The original forward base augmentation on the strict source, before geometric pullback. -/
def strictBaseUnit (R : CommRingCat.{u}) :
    strictToBoundedBelow (Spec R) ⟶ strictTotal (Spec R) ⋙
      FlasqueBoundedBelow.inclusion (Spec R) where
  app K := ObjectProperty.homMk ((godementTotalUnit (Spec R)).app K.obj)
  naturality {_ _} f := by
    apply ObjectProperty.hom_ext
    exact (godementTotalUnit (Spec R)).naturality f.hom

lemma strictBaseUnit_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (BoundedBelow.waldhausen (Spec R)).weq ((strictBaseUnit R).app K) :=
  godementTotalUnit_quasiIso (Spec R) ((strictToPlus (Spec R)).obj K)

/-- Literal identity chain maps compare only the two proofs of bounded-model membership. -/
def strictBoundedPullbackIso (R : CommRingCat.{u}) :
    strictPullback (projection R) ⋙ strictToBoundedBelow (twoChartLine R) ≅
      strictToBoundedBelow (Spec R) ⋙ boundedPullback (projection R) :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ (Iso.refl ((AlgebraicGeometry.Scheme.Modules.Complex.pullback
      (projection R)).obj K.obj)))
    (by
      intro K L f
      apply ObjectProperty.hom_ext
      change (AlgebraicGeometry.Scheme.Modules.Complex.pullback (projection R)).map f.hom ≫ 𝟙 _ =
        𝟙 _ ≫ (AlgebraicGeometry.Scheme.Modules.Complex.pullback (projection R)).map f.hom
      simp)

/-- The actual geometric pullback of that forward base augmentation. -/
def strictPullbackUnit (R : CommRingCat.{u}) :
    strictPullback (projection R) ⋙ strictToBoundedBelow (twoChartLine R) ⟶
      strictTotal (Spec R) ⋙ first R :=
  (strictBoundedPullbackIso R).hom ≫
    Functor.whiskerRight (strictBaseUnit R) (boundedPullback (projection R)) ≫
      (Functor.associator (strictTotal (Spec R)) (FlasqueBoundedBelow.inclusion (Spec R))
        (boundedPullback (projection R))).hom

lemma strictPullbackUnit_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (BoundedBelow.waldhausen (twoChartLine R)).weq ((strictPullbackUnit R).app K) := by
  exact (BoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
    ((BoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance)
    ((BoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
      ((boundedPullback_exact (projection R)).weak _ (strictBaseUnit_weak R K))
      ((BoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance))

/-- Actual first summand after the original strict source totalization. -/
def strictFirstTotal (R : CommRingCat.{u}) := strictTotal (Spec R) ⋙ firstTotal R

lemma strictFirstTotal_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (strictFirstTotal R) :=
  (strictTotal_exact (Spec R)).comp (firstTotal_exact R)

/-- Forward totalized pullback of A-to-T_A; no strictness is assigned to its target terms. -/
def strictPullbackTotalUnit (R : CommRingCat.{u}) : pullbackTotal R ⟶ strictFirstTotal R :=
  (Functor.associator (strictPullback (projection R))
    (strictToBoundedBelow (twoChartLine R)) (FlasqueBoundedBelow.total (twoChartLine R))).inv ≫
  Functor.whiskerRight (strictPullbackUnit R) (FlasqueBoundedBelow.total (twoChartLine R)) ≫
    (Functor.associator (strictTotal (Spec R)) (first R)
      (FlasqueBoundedBelow.total (twoChartLine R))).hom

lemma strictPullbackTotalUnit_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
      ((strictPullbackTotalUnit R).app K) := by
  exact (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
    ((FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance)
    ((FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
      (FlasqueBoundedBelow.total_weak ((strictPullbackUnit R).app K)
        (strictPullbackUnit_weak R K))
      ((FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance))

/-- The actual first injected Phi, with the literal strict-to-flasque source precomposition. -/
def strictPhiFirst (R : CommRingCat.{u}) :=
  strictTotal (Spec R) ⋙ firstInjection R ⋙ Phi R

lemma strictPhiFirst_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (strictPhiFirst R) :=
  (strictTotal_exact (Spec R)).comp ((firstInjection_exact R).comp (Phi_exact R))

/-- The totalized first coproduct inclusion, precomposed with Godement totalization of the strict
base model.
-/
def strictFirstPhiUnit (R : CommRingCat.{u}) : strictFirstTotal R ⟶ strictPhiFirst R :=
  Functor.whiskerLeft (strictTotal (Spec R)) (firstPhiUnit R)

instance strictFirstPhiUnit_isIso (R : CommRingCat.{u}) : IsIso (strictFirstPhiUnit R) := by
  unfold strictFirstPhiUnit
  infer_instance

/-- The actual first G0/Phi matrix entry, on the original strict source. -/
def G0First (R : CommRingCat.{u}) := strictPhiFirst R ⋙ G0 R

lemma G0First_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (G0First R) :=
  (strictPhiFirst_exact R).comp (G0_exact R)

/-- The original forward augmentation bridge, followed by the original coproduct-unit bridge. -/
def positiveToG0First (R : CommRingCat.{u}) : positive R ⟶ G0First R :=
  Functor.whiskerRight (strictPullbackTotalUnit R) (G0 R) ≫
    Functor.whiskerRight (strictFirstPhiUnit R) (G0 R)

lemma positiveToG0First_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq ((positiveToG0First R).app K) :=
  (FlasqueBoundedBelow.waldhausen (Spec R)).weq.comp_mem _ _
    ((G0_exact R).weak _ (strictPullbackTotalUnit_weak R K))
    ((FlasqueBoundedBelow.waldhausen (Spec R)).weq_iso _ inferInstance)

/-- The actual first diagonal equals the original literal source total K-map, including n=0. -/
theorem G0First_KMap_eq_strictTotal (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap (G0First_exact R) n = Waldhausen.KMap (strictTotal_exact (Spec R)) n :=
  (Waldhausen.KMap_eq_of_weakNatTrans (positive_exact R) (G0First_exact R)
    (positiveToG0First R) (positiveToG0First_weak R) n).symm.trans
      (positive_KMap_eq_strictTotal R n)

end Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiEntries
