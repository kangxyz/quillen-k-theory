/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.CokernelPushout
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeEulerFunctors
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence

/-! # Original native Euler conflations and their actual Waldhausen additivity -/
@[expose] public section

open AlgebraicGeometry.Scheme.ProjectiveLine


open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeEuler
variable (X : QuasiCompactSchemes.{u})

/-- The actual first Euler map in the original bounded-below model. -/
def boundedFirst :
    endpointBounded X (sequence X).X₁ (squareEndpoint_locallyPerfect X) ⟶
      endpointBounded X (sequence X).X₂ (middleEndpoint_locallyPerfect X) where
  app K := ObjectProperty.homMk ((first X).app K)
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (first X).naturality f

/-- The actual original Euler quotient in the same model. -/
def boundedSecond :
    endpointBounded X (sequence X).X₂ (middleEndpoint_locallyPerfect X) ⟶
      endpointBounded X (sequence X).X₃ (unitEndpoint_locallyPerfect X) where
  app K := ObjectProperty.homMk ((second X).app K)
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (second X).naturality f

lemma boundedFirst_second : boundedFirst X ≫ boundedSecond X = 0 := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact NatTrans.congr_app (first_second X) K

/-- The original first Euler map after totalization and actual flasque pushforward. -/
def projectedFirst : E2 X ⟶ E1 X :=
  Functor.whiskerRight (boundedFirst X)
    (FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj ⋙ P5NativeCoefficients.G0 X)

/-- The original normalized quotient map after the same two exact functors. -/
def projectedSecond : E1 X ⟶ E0 X :=
  Functor.whiskerRight (boundedSecond X)
    (FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj ⋙ P5NativeCoefficients.G0 X)

lemma projectedFirst_second : projectedFirst X ≫ projectedSecond X = 0 := by
  dsimp only [projectedFirst, projectedSecond]
  rw [← Functor.whiskerRight_comp, boundedFirst_second]
  apply NatTrans.ext
  funext K
  exact Functor.map_zero (FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj ⋙
    P5NativeCoefficients.G0 X) _ _

/-- The actual original coefficient sequence inside the bounded-below full subcategory. -/
def boundedModelSequence (K : FlasqueBoundedBelow.Obj X.obj) :
    ShortComplex (BoundedBelow.Obj (nativeLineFunctor.obj X).obj) :=
  ShortComplex.mk ((boundedFirst X).app K) ((boundedSecond X).app K)
    (NatTrans.congr_app (boundedFirst_second X) K)

lemma boundedModelSequence_conflation (K : FlasqueBoundedBelow.Obj X.obj) :
    (ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex (nativeLineFunctor.obj X).obj.Modules ℤ)) (BoundedBelow.objects
        (nativeLineFunctor.obj X).obj)).conflation (boundedModelSequence X K) :=
  coefficientSequence_shortExact X K

/-- The projected sequence uses actual Godement totals before ordinary pushforward. -/
def projectedModelSequence (K : FlasqueBoundedBelow.Obj X.obj) :
    ShortComplex (FlasqueBoundedBelow.Obj X.obj) :=
  (boundedModelSequence X K).map
    (FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj ⋙ P5NativeCoefficients.G0 X)

lemma projectedModelSequence_conflation (K : FlasqueBoundedBelow.Obj X.obj) :
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.obj.Modules ℤ))
      (FlasqueBoundedBelow.objects X.obj)).conflation (projectedModelSequence X K) :=
  ((FlasqueBoundedBelow.totalExactFunctor (nativeLineFunctor.obj X).obj).comp
    (P5NativeCoefficients.G0ExactFunctor X)).map_conflation _ (boundedModelSequence_conflation X K)

/-- Actual inherited conflations provide the original cofiber data for arbitrary source models. -/
lemma flasqueTargetSequence_isCofibrationSequence {C : Type (u + 1)} [Category.{u} C]
    (W : Waldhausen.Structure C) {Y : Scheme.{u}} {F G H : C ⥤ FlasqueBoundedBelow.Obj Y}
    (a : F ⟶ G) (b : G ⟶ H) (w : a ≫ b = 0)
    (hF : Waldhausen.IsExact W.cof W.weq
      (FlasqueBoundedBelow.waldhausen Y).cof (FlasqueBoundedBelow.waldhausen Y).weq F)
    (hG : Waldhausen.IsExact W.cof W.weq
      (FlasqueBoundedBelow.waldhausen Y).cof (FlasqueBoundedBelow.waldhausen Y).weq G)
    (hH : Waldhausen.IsExact W.cof W.weq
      (FlasqueBoundedBelow.waldhausen Y).cof (FlasqueBoundedBelow.waldhausen Y).weq H)
    (hc : ∀ K, (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex Y.Modules ℤ))
      (FlasqueBoundedBelow.objects Y)).conflation
      (ShortComplex.mk (a.app K) (b.app K) (NatTrans.congr_app w K))) :
    Waldhausen.Additivity.IsCofibrationSequence W (FlasqueBoundedBelow.waldhausen Y) a b where
  exactF := hF
  exactG := hG
  exactH := hH
  cofibration := {
    app_cof K := (ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex Y.Modules ℤ))
      (FlasqueBoundedBelow.objects Y)).inflation_of_conflation (hc K)
    relative_cof {K L} f hf := by
      let E := ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex Y.Modules ℤ))
        (FlasqueBoundedBelow.objects Y)
      let φ := Waldhausen.GilletWaldhausen.exactFunctorSequenceMap a b w f
      let : HasPushout (Waldhausen.GilletWaldhausen.exactFunctorSequenceAt a b w K).f φ.τ₁ :=
        Waldhausen.Additivity.hasPushout (FlasqueBoundedBelow.waldhausen Y) a
          (fun K => E.inflation_of_conflation (hc K)) f
      exact Waldhausen.GilletWaldhausen.relativePushout_inflation E φ
        (hc K) (hc L) (hH.cofibration f hf) }
  cofiber K := CategoryTheory.Limits.isPushout_of_isColimit_cokernel _
    ((ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex Y.Modules ℤ))
      (FlasqueBoundedBelow.objects Y)).cokernel _ (hc K))
    (FlasqueBoundedBelow.waldhausen Y).isZero _ _

/-- The original projected native Euler sequence has genuine cofibration and cofiber squares. -/
lemma projectedSequence_isCofibrationSequence :
    Waldhausen.Additivity.IsCofibrationSequence (FlasqueBoundedBelow.waldhausen X.obj)
      (FlasqueBoundedBelow.waldhausen X.obj) (projectedFirst X) (projectedSecond X) := by
  have hc (K : FlasqueBoundedBelow.Obj X.obj) := projectedModelSequence_conflation X K
  dsimp only [projectedModelSequence, boundedModelSequence, ShortComplex.map,
    projectedFirst, projectedSecond, E2, E1, E0, projectedEndpoint,
    Functor.comp_obj, Functor.whiskerRight_app] at hc ⊢
  exact flasqueTargetSequence_isCofibrationSequence (FlasqueBoundedBelow.waldhausen X.obj)
    (projectedFirst X) (projectedSecond X) (projectedFirst_second X)
    (E2_exact X) (E1_exact X) (E0_exact X) hc

/-- Original native Euler additivity in every connective degree, including K0. -/
lemma KMap_euler_additivity (n : ℕ) (x : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    Waldhausen.KMap (E1_exact X) n x =
      Waldhausen.KMap (E2_exact X) n x * Waldhausen.KMap (E0_exact X) n x :=
  Waldhausen.Additivity.KMap_additivity_mul _ _ _ _
    (projectedSequence_isCofibrationSequence X) n x

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeEuler
