/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.EulerFunctors
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence

/-! # Original Waldhausen additivity for the natural Euler short exact sequence -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.Euler
open FlasqueCoefficients
variable (R : CommRingCat.{u})

/-- The original first Euler map lifted before totalization. -/
def boundedFirst :
    endpointBounded R (sequence R).X₁ (squareEndpoint_strictPerfect R) ⟶
      endpointBounded R (sequence R).X₂ (middleEndpoint_strictPerfect R) where
  app A := ObjectProperty.homMk ((first R).app A)
  naturality {A B} f := by
    apply ObjectProperty.hom_ext
    exact (first R).naturality f

/-- The original quotient Euler map lifted before totalization. -/
def boundedSecond :
    endpointBounded R (sequence R).X₂ (middleEndpoint_strictPerfect R) ⟶
      endpointBounded R (sequence R).X₃ (unitEndpoint_strictPerfect R) where
  app A := ObjectProperty.homMk ((second R).app A)
  naturality {A B} f := by
    apply ObjectProperty.hom_ext
    exact (second R).naturality f

lemma boundedFirst_second : boundedFirst R ≫ boundedSecond R = 0 := by
  apply NatTrans.ext
  funext A
  apply ObjectProperty.hom_ext
  exact NatTrans.congr_app (first_second R) A

/-- The original first Euler map after totalization and ordinary projection. -/
def projectedFirst : E2 R ⟶ E1 R :=
  Functor.whiskerRight (boundedFirst R) (FlasqueBoundedBelow.total (twoChartLine R) ⋙ G0 R)

/-- The original determinant-normalized quotient map after the same exact functors. -/
def projectedSecond : E1 R ⟶ E0 R :=
  Functor.whiskerRight (boundedSecond R) (FlasqueBoundedBelow.total (twoChartLine R) ⋙ G0 R)

lemma projectedFirst_second : projectedFirst R ≫ projectedSecond R = 0 := by
  apply NatTrans.ext
  funext A
  change (FlasqueBoundedBelow.total (twoChartLine R) ⋙ G0 R).map ((boundedFirst R).app A) ≫
    (FlasqueBoundedBelow.total (twoChartLine R) ⋙ G0 R).map ((boundedSecond R).app A) = 0
  have hw : (boundedFirst R).app A ≫ (boundedSecond R).app A = 0 :=
    NatTrans.congr_app (boundedFirst_second R) A
  rw [← Functor.map_comp, hw, Functor.map_zero]

/-- The actual coefficient short complex inside the original lower-bounded full subcategory. -/
def boundedModelSequence (A : StrictPerfect (Spec R)) :
    ShortComplex (BoundedBelow.Obj (twoChartLine R)) :=
  ShortComplex.mk ((boundedFirst R).app A) ((boundedSecond R).app A)
    (NatTrans.congr_app (boundedFirst_second R) A)

lemma boundedModelSequence_conflation (A : StrictPerfect (Spec R)) :
    (Quillen.ExactSubcategory.exactStructure
      (Quillen.abelianExactStructure (Complex (twoChartLine R)))
      (BoundedBelow.objects (twoChartLine R))).conflation (boundedModelSequence R A) :=
  coefficientSequence_shortExact R A

/-- The actual short complex inside the original flasque-perfect full subcategory. -/
def projectedModelSequence (A : StrictPerfect (Spec R)) :
    ShortComplex (FlasqueBoundedBelow.Obj (Spec R)) :=
  (boundedModelSequence R A).map (FlasqueBoundedBelow.total (twoChartLine R) ⋙ G0 R)

lemma projectedModelSequence_conflation (A : StrictPerfect (Spec R)) :
    (Quillen.ExactSubcategory.exactStructure (Quillen.abelianExactStructure (Complex (Spec R)))
      (FlasqueBoundedBelow.objects (Spec R))).conflation (projectedModelSequence R A) :=
  ((FlasqueBoundedBelow.totalExactFunctor (twoChartLine R)).comp (G0ExactFunctor R)).map_conflation
    _ (boundedModelSequence_conflation R A)

/-- Its actual quotient functor preserves inherited conflations. -/
def E0ExactFunctor : Quillen.ExactFunctor (strictExactStructure (Spec R))
    (Quillen.ExactSubcategory.exactStructure (Quillen.abelianExactStructure (Complex (Spec R)))
      (FlasqueBoundedBelow.objects (Spec R))) :=
  (endpointBoundedExactFunctor R (sequence R).X₃ (unitEndpoint_strictPerfect R)).comp
    ((FlasqueBoundedBelow.totalExactFunctor (twoChartLine R)).comp (G0ExactFunctor R))

/-- Actual inherited conflations give the cofibration and cofiber structure on these models. -/
lemma strictFlasqueSequence_isCofibrationSequence {X Y : Scheme.{u}}
    {F G H : StrictPerfect X ⥤ FlasqueBoundedBelow.Obj Y}
    (a : F ⟶ G) (b : G ⟶ H) (w : a ≫ b = 0)
    (hF : Waldhausen.IsExact (strictWaldhausen X).cof (strictWaldhausen X).weq
      (FlasqueBoundedBelow.waldhausen Y).cof (FlasqueBoundedBelow.waldhausen Y).weq F)
    (hG : Waldhausen.IsExact (strictWaldhausen X).cof (strictWaldhausen X).weq
      (FlasqueBoundedBelow.waldhausen Y).cof (FlasqueBoundedBelow.waldhausen Y).weq G)
    (hH : Waldhausen.IsExact (strictWaldhausen X).cof (strictWaldhausen X).weq
      (FlasqueBoundedBelow.waldhausen Y).cof (FlasqueBoundedBelow.waldhausen Y).weq H)
    (hc : ∀ A, (Quillen.ExactSubcategory.exactStructure
      (Quillen.abelianExactStructure (Complex Y)) (FlasqueBoundedBelow.objects Y)).conflation
      (ShortComplex.mk (a.app A) (b.app A) (NatTrans.congr_app w A))) :
    Waldhausen.Additivity.IsCofibrationSequence (strictWaldhausen X)
      (FlasqueBoundedBelow.waldhausen Y) a b where
  exactF := hF
  exactG := hG
  exactH := hH
  cofibration := {
    app_cof A := (Quillen.ExactSubcategory.exactStructure
      (Quillen.abelianExactStructure (Complex Y))
      (FlasqueBoundedBelow.objects Y)).inflation_of_conflation (hc A)
    relative_cof {A B} f hf := by
      let E := Quillen.ExactSubcategory.exactStructure
        (Quillen.abelianExactStructure (Complex Y)) (FlasqueBoundedBelow.objects Y)
      let φ := Waldhausen.GilletWaldhausen.exactFunctorSequenceMap a b w f
      let : HasPushout (Waldhausen.GilletWaldhausen.exactFunctorSequenceAt a b w A).f φ.τ₁ :=
        Waldhausen.Additivity.hasPushout (FlasqueBoundedBelow.waldhausen Y) a
          (fun A => E.inflation_of_conflation (hc A)) f
      exact Waldhausen.GilletWaldhausen.relativePushout_inflation E φ
        (hc A) (hc B) (hH.cofibration f hf) }
  cofiber A := Waldhausen.QuillenComparison.isPushoutOfZeroCokernel _
    ((Quillen.ExactSubcategory.exactStructure (Quillen.abelianExactStructure (Complex Y))
      (FlasqueBoundedBelow.objects Y)).cokernel _ (hc A))
    (FlasqueBoundedBelow.waldhausen Y).isZero _ _

/-- The original cofibration and cofiber squares needed by native Waldhausen additivity. -/
lemma projectedSequence_isCofibrationSequence :
    Waldhausen.Additivity.IsCofibrationSequence
      (strictWaldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))
      (projectedFirst R) (projectedSecond R) := by
  have hc (A : StrictPerfect (Spec R)) := projectedModelSequence_conflation R A
  dsimp only [projectedModelSequence, boundedModelSequence, ShortComplex.map,
    projectedFirst, projectedSecond, E2, E1, E0, projectedEndpoint,
    Functor.comp_obj, Functor.whiskerRight_app] at hc ⊢
  exact
  strictFlasqueSequence_isCofibrationSequence (projectedFirst R) (projectedSecond R)
    (projectedFirst_second R) (E2_exact R) (E1_exact R) (E0_exact R)
    hc

/-- Literal native Euler additivity, for every natural degree including zero. -/
lemma KMap_euler_additivity (n : ℕ) (x : (strictWaldhausen (Spec R)).K n) :
    Waldhausen.KMap (E1_exact R) n x =
      Waldhausen.KMap (E2_exact R) n x * Waldhausen.KMap (E0_exact R) n x :=
  Waldhausen.Additivity.KMap_additivity_mul _ _ _ _
    (projectedSequence_isCofibrationSequence R) n x

end Quillen.PerfectComplexes.ProjectiveLine.Euler
