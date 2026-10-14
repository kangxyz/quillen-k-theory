/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands

/-!
# Local original-map comparison for the flasque two-summand functor

The actual coproduct inclusion comparison and original weak total augmentation
compare original K-maps. Native affine geometry is supplied in the next leaf.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands

/-- Original left tensor on the local perfect category, with the original chart trivializations. -/
def localNegativeTwist (R : CommRingCat.{u}) :
    Perfect (twoChartLine R) ⥤ Perfect (twoChartLine R) :=
  perfectTensorByLine (tautologicalLine R)
    (fun _ : Bool => Spec (CommRingCat.of (Polynomial R))) (polynomialChart R)
    (polynomialChart_cover R) (lineChartIso R)

lemma localNegativeTwist_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (perfectWaldhausen (twoChartLine R)).cof (perfectWaldhausen (twoChartLine R)).weq
    (perfectWaldhausen (twoChartLine R)).cof (perfectWaldhausen (twoChartLine R)).weq
    (localNegativeTwist R) := perfectTensorByLine_waldhausenExact _ _ _ _ _

/-- The original local perfect two-summand functor in O/O(-1) order. -/
def localTwoSummands (R : CommRingCat.{u}) :
    Perfect (Spec R) × Perfect (Spec R) ⥤ Perfect (twoChartLine R) :=
  Waldhausen.Additivity.sumFunctor
    (CategoryTheory.Prod.fst _ _ ⋙ perfectFlatPullback (projection R))
    (CategoryTheory.Prod.snd _ _ ⋙ perfectFlatPullback (projection R) ⋙ localNegativeTwist R)

lemma localTwoSummands_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (Waldhausen.ExtensionCategory.productStructure
      (perfectWaldhausen (Spec R)) (perfectWaldhausen (Spec R))).cof
    (Waldhausen.ExtensionCategory.productStructure
      (perfectWaldhausen (Spec R)) (perfectWaldhausen (Spec R))).weq
    (perfectWaldhausen (twoChartLine R)).cof (perfectWaldhausen (twoChartLine R)).weq
    (localTwoSummands R) :=
  Waldhausen.Additivity.sumFunctor_isExact _ _
    ((Waldhausen.ExtensionCategory.fst_exact _ _).comp
      (perfectFlatPullback_waldhausenExact (projection R)))
    ((Waldhausen.ExtensionCategory.snd_exact _ _).comp
      ((perfectFlatPullback_waldhausenExact (projection R)).comp (localNegativeTwist_exact R)))

/-- The literal product of the existing original model inclusions. -/
def inputInclusion (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (Spec R) × FlasqueBoundedBelow.Obj (Spec R) ⥤
      Perfect (Spec R) × Perfect (Spec R) :=
  (FlasqueBoundedBelow.perfectInclusion (Spec R)).prod
    (FlasqueBoundedBelow.perfectInclusion (Spec R))

lemma inputInclusion_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).cof
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).weq
    (Waldhausen.ExtensionCategory.productStructure
      (perfectWaldhausen (Spec R)) (perfectWaldhausen (Spec R))).cof
    (Waldhausen.ExtensionCategory.productStructure
      (perfectWaldhausen (Spec R)) (perfectWaldhausen (Spec R))).weq (inputInclusion R) :=
  Waldhausen.ExtensionCategory.pair_exact _ _ _
    ((Waldhausen.ExtensionCategory.fst_exact _ _).comp
      (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)))
    ((Waldhausen.ExtensionCategory.snd_exact _ _).comp
      (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)))

instance boundedInclusion_additive (X : Scheme.{u}) :
    (BoundedBelow.inclusion X).Additive := by
  unfold BoundedBelow.inclusion
  infer_instance

instance boundedInclusion_preservesBinaryBiproducts (X : Scheme.{u}) :
    PreservesBinaryBiproducts (BoundedBelow.inclusion X) := by
  let : PreservesFiniteBiproducts (BoundedBelow.inclusion X) := inferInstance
  exact preservesBinaryBiproducts_of_preservesBiproducts _

instance boundedInclusion_preservesBinaryCoproducts (X : Scheme.{u}) :
    PreservesColimitsOfShape (Discrete WalkingPair) (BoundedBelow.inclusion X) :=
  preservesBinaryCoproducts_of_preservesBinaryBiproducts _

/-- The actual categorical coproduct comparison, without replacing either selected sum. -/
def boundedSumInclusionIso {C : Type v} [Category C] (X : Scheme.{u})
    (H F : C ⥤ BoundedBelow.Obj X) :
    Waldhausen.Additivity.sumFunctor (H ⋙ BoundedBelow.inclusion X)
        (F ⋙ BoundedBelow.inclusion X) ≅
      Waldhausen.Additivity.sumFunctor H F ⋙ BoundedBelow.inclusion X :=
  NatIso.ofComponents
    (fun K => asIso (coprodComparison (BoundedBelow.inclusion X) (H.obj K) (F.obj K)))
    (fun f => (coprodComparison_natural (BoundedBelow.inclusion X) (H.map f) (F.map f)).symm)

/-- Actual pre-total sum after the literal inclusion is the local original sum. -/
def beforeTotalInclusionIso (R : CommRingCat.{u}) :
    beforeTotal R ⋙ BoundedBelow.inclusion (twoChartLine R) ≅
      inputInclusion R ⋙ localTwoSummands R :=
  (boundedSumInclusionIso (twoChartLine R)
    (CategoryTheory.Prod.fst _ _ ⋙ first R) (CategoryTheory.Prod.snd _ _ ⋙ second R)).symm

/-- The actual total augmentation transported by the literal original perfect inclusion. -/
def PhiPerfectUnit (R : CommRingCat.{u}) :
    beforeTotal R ⋙ BoundedBelow.inclusion (twoChartLine R) ⟶
      Phi R ⋙ FlasqueBoundedBelow.perfectInclusion (twoChartLine R) :=
  CategoryTheory.Functor.whiskerRight (PhiUnit R) (BoundedBelow.inclusion (twoChartLine R))

lemma PhiPerfectUnit_weak (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (Spec R) × FlasqueBoundedBelow.Obj (Spec R)) :
    (perfectWaldhausen (twoChartLine R)).weq ((PhiPerfectUnit R).app K) :=
  (BoundedBelow.inclusion_exact _).weak _ (PhiUnit_weak R K)

/-- The induced local original K-map is recovered by exact functors and an actual weak unit. -/
lemma Phi_KMap_after_perfectInclusion (R : CommRingCat.{u}) (n : ℕ) :
    (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (twoChartLine R)) n).comp
        (Waldhausen.KMap (Phi_exact R) n) =
      (Waldhausen.KMap (localTwoSummands_exact R) n).comp
        (Waldhausen.KMap (inputInclusion_exact R) n) := by
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]
  have hw := Waldhausen.KMap_eq_of_weakNatTrans
    ((beforeTotal_exact R).comp (BoundedBelow.inclusion_exact (twoChartLine R)))
    ((Phi_exact R).comp (FlasqueBoundedBelow.perfectInclusion_exact (twoChartLine R)))
    (PhiPerfectUnit R) (PhiPerfectUnit_weak R) n
  have hi := Waldhausen.KMap_eq_of_iso
    ((beforeTotal_exact R).comp (BoundedBelow.inclusion_exact (twoChartLine R)))
    ((inputInclusion_exact R).comp (localTwoSummands_exact R)) (beforeTotalInclusionIso R) n
  exact hw.symm.trans hi

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
