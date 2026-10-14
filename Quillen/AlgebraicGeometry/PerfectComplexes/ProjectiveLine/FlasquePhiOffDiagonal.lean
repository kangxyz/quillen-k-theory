/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasquePhiFirstEntry
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativePerfectGeneration

/-!
# Original off-diagonal weak zero maps for G composed with Phi

Native O(-1) derived vanishing certifies the literal natural zero chain maps
as quasi-isomorphisms. Original Godement augmentation and exact line tensor
comparisons retain the actual flasque outputs and the original G1 shift.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiEntries
open StrictPositiveRetraction FlasqueTwoSummands FlasqueCoefficients

local instance matrixDerivedStandard (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

/-- Actual derived zero certifies the literal original map to the chosen flasque zero. -/
lemma weak_zero_of_derivedZero (X : Scheme.{u}) (K : FlasqueBoundedBelow.Obj X)
    (hK : IsZero (DerivedCategory.Plus.Q.obj ((toPlus X).obj K))) :
    (FlasqueBoundedBelow.waldhausen X).weq
      (0 : K ⟶ (FlasqueBoundedBelow.waldhausen X).zero) := by
  change QuasiIso (0 : K.obj ⟶ (FlasqueBoundedBelow.waldhausen X).zero.obj)
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules _).mp
  have hs : IsZero (DerivedCategory.Q.obj K.obj) :=
    (DerivedCategory.Plus.ι (C := X.Modules)).map_isZero hK
  have ht : IsZero (DerivedCategory.Q.obj (FlasqueBoundedBelow.waldhausen X).zero.obj) :=
    DerivedCategory.Q.map_isZero
      ((FlasqueBoundedBelow.objects X).ι.map_isZero (FlasqueBoundedBelow.waldhausen X).isZero)
  exact hs.isIso ht _

/-- The original natural zero transformation, not a derived-category map, gives KMap vanishing. -/
lemma KMap_eq_one_of_derivedZero {C : Type (u + 1)} [Category.{u} C]
    (V : Waldhausen.Structure C) (X : Scheme.{u}) (F : C ⥤ FlasqueBoundedBelow.Obj X)
    (hF : Waldhausen.IsExact V.cof V.weq
      (FlasqueBoundedBelow.waldhausen X).cof (FlasqueBoundedBelow.waldhausen X).weq F)
    (hz : ∀ K, IsZero (DerivedCategory.Plus.Q.obj ((toPlus X).obj (F.obj K)))) (n : ℕ) :
    Waldhausen.KMap hF n = 1 :=
  (Waldhausen.KMap_eq_of_weakNatTrans hF
    (Waldhausen.zeroFunctor_isExact V (FlasqueBoundedBelow.waldhausen X)) 0
    (fun K => weak_zero_of_derivedZero X (F.obj K) (hz K)) n).trans
      (Waldhausen.KMap_zeroFunctor V (FlasqueBoundedBelow.waldhausen X) n)

/-- Native negative-line vanishing applies to the actual left tensor of each original input. -/
lemma negativePullback_derivedZero (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (Spec R)) :
    IsZero ((derivedPushforwardPlus (projection R)).obj
      (DerivedCategory.Plus.Q.obj ((boundedToPlus (twoChartLine R)).obj ((second R).obj K)))) := by
  let B := (toPlus (Spec R)).obj K
  let H := affineNegativePullbackModule R
  have hp : perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj
      (DerivedCategory.Plus.Q.obj B)) :=
    (perfectDerivedObjects_toDerived_iff (Spec R) K.obj).mpr K.property.1.1
  have hz := isZero_derivedProjection_negativePullback_perfect R
    (DerivedCategory.Plus.Q.obj B) hp
  have := H.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact hz.of_iso ((derivedPushforwardPlus (projection R)).mapIso
    (asIso (H.rightDerivedFunctorPlusUnit.app B)))

/-- Actual total augmentation and installed G0 unit retain the literal negative output. -/
lemma G0_secondTotal_derivedZero (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (Spec R)) :
    IsZero (DerivedCategory.Plus.Q.obj ((toPlus (Spec R)).obj
      ((G0 R).obj ((secondTotal R).obj K)))) := by
  let C := (boundedToPlus (twoChartLine R)).obj ((second R).obj K)
  have : IsIso (DerivedCategory.Plus.Q.map ((godementTotalPlusUnit (twoChartLine R)).app C)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (twoChartLine R).Modules) _
      (godementTotalPlusUnit_quasiIso (twoChartLine R) C)
  have ht := (negativePullback_derivedZero R K).of_iso
    ((derivedPushforwardPlus (projection R)).mapIso
      (asIso (DerivedCategory.Plus.Q.map ((godementTotalPlusUnit (twoChartLine R)).app C))).symm)
  exact ht.of_iso ((G0DerivedIso R).app ((secondTotal R).obj K))

/-- Original exact right tensor takes the forward total augmentation to a weak chain map. -/
def firstRightTensorUnit (R : CommRingCat.{u}) (K : FlasqueBoundedBelow.Obj (Spec R)) :
    (moduleTensorByLineRight (tautologicalLine R)).mapCochainComplexPlus.obj
        ((boundedToPlus (twoChartLine R)).obj ((first R).obj K)) ⟶
      (rightTensorPlus R).obj ((firstTotal R).obj K) :=
  ObjectProperty.homMk
    ((tensorByLineRightComplex (tautologicalLine R)).map
      ((godementTotalUnit (twoChartLine R)).app
        ((boundedToPlus (twoChartLine R)).obj ((first R).obj K)).obj))

lemma firstRightTensorUnit_quasiIso (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (Spec R)) :
    QuasiIso (firstRightTensorUnit R K).hom := by
  let C := (boundedToPlus (twoChartLine R)).obj ((first R).obj K)
  let : QuasiIso ((godementTotalPlusUnit (twoChartLine R)).app C).hom :=
    godementTotalPlusUnit_quasiIso (twoChartLine R) C
  change QuasiIso ((tensorByLineRightComplex (tautologicalLine R)).map
    ((godementTotalPlusUnit (twoChartLine R)).app C).hom)
  infer_instance

/-- The actual right tensor of actual pulled total has zero derived direct image. -/
lemma rightTensor_firstTotal_derivedZero (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (Spec R)) :
    IsZero ((derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj
      ((rightTensorPlus R).obj ((firstTotal R).obj K)))) := by
  let C := (boundedToPlus (twoChartLine R)).obj ((first R).obj K)
  let N := (boundedToPlus (twoChartLine R)).obj ((second R).obj K)
  let M := (moduleTensorByLineRight (tautologicalLine R)).mapCochainComplexPlus.obj C
  let e : N ≅ M := (CochainComplex.plus (twoChartLine R).Modules).isoMk
    ((tensorByLineComplexSymmetry (tautologicalLine R)).app C.obj)
  have hm := (negativePullback_derivedZero R K).of_iso
    ((derivedPushforwardPlus (projection R)).mapIso (DerivedCategory.Plus.Q.mapIso e.symm))
  have : IsIso (DerivedCategory.Plus.Q.map (firstRightTensorUnit R K)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (twoChartLine R).Modules) _
      (firstRightTensorUnit_quasiIso R K)
  exact hm.of_iso ((derivedPushforwardPlus (projection R)).mapIso
    (asIso (DerivedCategory.Plus.Q.map (firstRightTensorUnit R K))).symm)

/-- The installed original G1 comparison and its original shift retain actual derived vanishing. -/
lemma G1_firstTotal_derivedZero (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (Spec R)) :
    IsZero (DerivedCategory.Plus.Q.obj ((toPlus (Spec R)).obj
      ((G1 R).obj ((firstTotal R).obj K)))) := by
  have hs := (shiftFunctor (DerivedCategory.Plus (Spec R).Modules) (1 : ℤ)).map_isZero
    (rightTensor_firstTotal_derivedZero R K)
  exact hs.of_iso ((G1DerivedIso R).app ((firstTotal R).obj K))

/-- Original second injected Phi after literal strict source totalization. -/
def strictPhiSecond (R : CommRingCat.{u}) :=
  strictTotal (Spec R) ⋙ secondInjection R ⋙ Phi R

lemma strictPhiSecond_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (strictPhiSecond R) :=
  (strictTotal_exact (Spec R)).comp ((secondInjection_exact R).comp (Phi_exact R))

/-- Actual upper off-diagonal from the strict source, with original Phi and G0. -/
def G0Second (R : CommRingCat.{u}) := strictPhiSecond R ⋙ G0 R

lemma G0Second_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (G0Second R) :=
  (strictPhiSecond_exact R).comp (G0_exact R)

/-- Actual lower off-diagonal from the strict source, retaining the original G1 shift. -/
def G1First (R : CommRingCat.{u}) := strictPhiFirst R ⋙ G1 R

lemma G1First_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (G1First R) :=
  (strictPhiFirst_exact R).comp (G1_exact R)

/-- The original coproduct-unit comparison certifies the actual G0 second-injection zero map. -/
lemma G0Second_derivedZero (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    IsZero (DerivedCategory.Plus.Q.obj ((toPlus (Spec R)).obj ((G0Second R).obj K))) := by
  let B := (strictTotal (Spec R)).obj K
  exact (G0_secondTotal_derivedZero R B).of_iso
    ((toPlus (Spec R) ⋙ DerivedCategory.Plus.Q).mapIso
      ((G0 R).mapIso (asIso ((secondPhiUnit R).app B))).symm)

/-- The original coproduct-unit comparison certifies the actual G1 first-injection zero map. -/
lemma G1First_derivedZero (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    IsZero (DerivedCategory.Plus.Q.obj ((toPlus (Spec R)).obj ((G1First R).obj K))) := by
  let B := (strictTotal (Spec R)).obj K
  exact (G1_firstTotal_derivedZero R B).of_iso
    ((toPlus (Spec R) ⋙ DerivedCategory.Plus.Q).mapIso
      ((G1 R).mapIso (asIso ((firstPhiUnit R).app B))).symm)

/-- The actual G0/Phi upper off-diagonal original KMap vanishes for every n, including zero. -/
theorem G0Second_KMap_eq_one (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap (G0Second_exact R) n = 1 :=
  KMap_eq_one_of_derivedZero (strictWaldhausen (Spec R)) (Spec R) (G0Second R)
    (G0Second_exact R) (G0Second_derivedZero R) n

/-- The actual G1/Phi lower off-diagonal original KMap vanishes for every n, including zero. -/
theorem G1First_KMap_eq_one (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap (G1First_exact R) n = 1 :=
  KMap_eq_one_of_derivedZero (strictWaldhausen (Spec R)) (Spec R) (G1First R)
    (G1First_exact R) (G1First_derivedZero R) n

end Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiEntries
