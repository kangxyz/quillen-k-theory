/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeEulerSequence
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeOffDiagonal
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFunctorAssociator

/-! # Original native Euler coefficient functors on every flasque perfect input

Actual local splitting gives the coefficient short exact sequence even though
the original input terms need not be flat. Every endpoint is bounded below
before Godement totalization; ordinary projection is used only afterwards.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients


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
open FlasqueCoefficients
variable (X : QuasiCompactSchemes.{u})

/-- Literal tensor by a fixed native Euler endpoint after the original flat projection pullback. -/
def endpointComplex (M : (nativeLineFunctor.obj X).obj.Modules) :
    FlasqueBoundedBelow.Obj X.obj ⥤ Complex (nativeLineFunctor.obj X).obj :=
  (FlasqueBoundedBelow.objects X.obj).ι ⋙ AlgebraicGeometry.Scheme.Modules.Complex.pullback
    (nativeProjection.app X).hom ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft M

instance endpointComplex_additive (M : (nativeLineFunctor.obj X).obj.Modules) :
    (endpointComplex X M).Additive := by
  unfold endpointComplex
  infer_instance

/-- The actual first Euler coefficient map, natural in the original input. -/
def first : endpointComplex X (sequence X).X₁ ⟶ endpointComplex X (sequence X).X₂ :=
  Functor.whiskerLeft ((FlasqueBoundedBelow.objects X.obj).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.pullback (nativeProjection.app X).hom)
    ((moduleTensorCoefficientMap (nativeLineFunctor.obj X).obj
      (sequence X).f).mapHomologicalComplex (.up ℤ))

/-- The actual determinant-normalized Euler quotient map. -/
def second : endpointComplex X (sequence X).X₂ ⟶ endpointComplex X (sequence X).X₃ :=
  Functor.whiskerLeft ((FlasqueBoundedBelow.objects X.obj).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.pullback (nativeProjection.app X).hom)
    ((moduleTensorCoefficientMap (nativeLineFunctor.obj X).obj
      (sequence X).g).mapHomologicalComplex (.up ℤ))

lemma first_second : first X ≫ second X = 0 := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext n
  change (moduleTensorByLineRight
    (((AlgebraicGeometry.Scheme.Modules.Complex.pullback (nativeProjection.app X).hom).obj K.obj).X
      n)).map (sequence X).f ≫
      (moduleTensorByLineRight
        (((AlgebraicGeometry.Scheme.Modules.Complex.pullback (nativeProjection.app X).hom).obj
          K.obj).X n)).map (sequence X).g = 0
  rw [← Functor.map_comp, (sequence X).zero, Functor.map_zero]

/-- The genuine coefficient Euler sequence on the original cochain objects. -/
def coefficientSequence (K : FlasqueBoundedBelow.Obj X.obj) :
    ShortComplex (Complex (nativeLineFunctor.obj X).obj) :=
  ShortComplex.mk ((first X).app K) ((second X).app K) (NatTrans.congr_app (first_second X) K)

/-- Arbitrary original terms are allowed: exactness uses local splitting of the Euler quotient. -/
lemma coefficientSequence_shortExact (K : FlasqueBoundedBelow.Obj X.obj) :
    (coefficientSequence X K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact coefficient_shortExact X (((AlgebraicGeometry.Scheme.Modules.Complex.pullback
    (nativeProjection.app X).hom).obj K.obj).X n)

/-- The actual two-line associator with both original native chart trivializations. -/
def twoLineAssociator :
    AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (nativeTautologicalLine X) ⋙
        AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (nativeTautologicalLine X) ≅
          AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (sequence X).X₁ :=
  Functor.mapHomologicalComplexCompIso
    (moduleLineTensorAssociator (nativeTautologicalLine X) (nativeTautologicalLine X)
      (fun _ : Bool => (polynomialFunctor.obj X).obj) (nativeChart X) (nativeChart_cover X)
      (nativeLineChartIso X) (nativeLineChartIso X)) (.up ℤ)

/-- Right tensor of the original second summand keeps the original symmetry and associator. -/
def originalRightTensorIso :
    endpointComplex X (nativeTautologicalLine X) ⋙
        AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (nativeTautologicalLine X) ≅
          endpointComplex X (sequence X).X₁ :=
  Functor.isoWhiskerLeft ((FlasqueBoundedBelow.objects X.obj).ι ⋙
      AlgebraicGeometry.Scheme.Modules.Complex.pullback (nativeProjection.app X).hom)
    (Functor.isoWhiskerLeft (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft
      (nativeTautologicalLine X))
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeftRightIso (nativeTautologicalLine X)).symm
        ≪≫ twoLineAssociator X)

lemma squareEndpoint_locallyPerfect (K : FlasqueBoundedBelow.Obj X.obj) :
    locallyPerfect (nativeLineFunctor.obj X).obj
      ((endpointComplex X (sequence X).X₁).obj K) := by
  have hp := locallyPerfect_flatPullback (nativeProjection.app X).hom K.property.1.1
  have h₁ := locallyPerfect_tensorByLine (nativeTautologicalLine X)
    (fun _ : Bool => (polynomialFunctor.obj X).obj) (nativeChart X)
    (nativeChart_cover X) (nativeLineChartIso X) hp
  have h₂ := locallyPerfect_tensorByLine (nativeTautologicalLine X)
    (fun _ : Bool => (polynomialFunctor.obj X).obj) (nativeChart X)
    (nativeChart_cover X) (nativeLineChartIso X) h₁
  exact locallyPerfect_of_iso
    ((twoLineAssociator X).app ((AlgebraicGeometry.Scheme.Modules.Complex.pullback
      (nativeProjection.app X).hom).obj K.obj)) h₂

/-- The actual E0 endpoint left unitor on every original input complex. -/
def unitEndpointIso : endpointComplex X (sequence X).X₃ ≅
    (FlasqueBoundedBelow.objects X.obj).ι ⋙ AlgebraicGeometry.Scheme.Modules.Complex.pullback
      (nativeProjection.app X).hom :=
  Functor.isoWhiskerLeft ((FlasqueBoundedBelow.objects X.obj).ι ⋙
      AlgebraicGeometry.Scheme.Modules.Complex.pullback (nativeProjection.app X).hom)
    (NatIso.mapHomologicalComplex
      (SheafOfModulesOfCommRing.tensorLeftUnitIso (nativeLineFunctor.obj X).obj.sheaf) (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)) ≪≫ Functor.rightUnitor _

lemma unitEndpoint_locallyPerfect (K : FlasqueBoundedBelow.Obj X.obj) :
    locallyPerfect (nativeLineFunctor.obj X).obj
      ((endpointComplex X (sequence X).X₃).obj K) :=
  locallyPerfect_of_iso ((unitEndpointIso X).app K).symm
    (locallyPerfect_flatPullback (nativeProjection.app X).hom K.property.1.1)

lemma middleEndpoint_locallyPerfect (K : FlasqueBoundedBelow.Obj X.obj) :
    locallyPerfect (nativeLineFunctor.obj X).obj
      ((endpointComplex X (sequence X).X₂).obj K) :=
  locallyPerfect_of_shortExact (coefficientSequence_shortExact X K)
    (squareEndpoint_locallyPerfect X K) (unitEndpoint_locallyPerfect X K)

/-- Every fixed tensor endpoint keeps each specified original lower bound. -/
lemma endpointComplex_isStrictlyGE (M : (nativeLineFunctor.obj X).obj.Modules)
    (K : FlasqueBoundedBelow.Obj X.obj) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((endpointComplex X M).obj K).IsStrictlyGE a := by
  dsimp [endpointComplex, AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft,
    AlgebraicGeometry.Scheme.Modules.Complex.pullback]
  infer_instance

/-- The original endpoint complex with its proved bounded-below perfect membership. -/
def endpointBounded (M : (nativeLineFunctor.obj X).obj.Modules)
    (hM : ∀ K, locallyPerfect (nativeLineFunctor.obj X).obj ((endpointComplex X M).obj K)) :
    FlasqueBoundedBelow.Obj X.obj ⥤ BoundedBelow.Obj (nativeLineFunctor.obj X).obj :=
  ObjectProperty.lift _ (endpointComplex X M) (fun K => by
    obtain ⟨a, ha⟩ := K.property.1.2
    let := ha
    exact ⟨hM K, a, endpointComplex_isStrictlyGE X M K a⟩)

instance endpointBounded_additive (M : (nativeLineFunctor.obj X).obj.Modules)
    (hM : ∀ K, locallyPerfect (nativeLineFunctor.obj X).obj ((endpointComplex X M).obj K)) :
    (endpointBounded X M hM).Additive where
  map_add := by
    intro A B f g
    apply ObjectProperty.hom_ext
    exact Functor.map_add (endpointComplex X M)

/-- Exactness in the source variable uses native flat pullback and the vector-bundle endpoint. -/
def endpointBoundedExactFunctor (M : (nativeLineFunctor.obj X).obj.Modules)
    [IsFiniteLocallyFree (nativeLineFunctor.obj X).obj M]
    (hM : ∀ K, locallyPerfect (nativeLineFunctor.obj X).obj ((endpointComplex X M).obj K)) :
    ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (Complex X.obj))
        (FlasqueBoundedBelow.objects X.obj))
      (ExactSubcategory.exactStructure (abelianExactStructure
        (Complex (nativeLineFunctor.obj X).obj)) (BoundedBelow.objects
          (nativeLineFunctor.obj X).obj)) where
  toFunctor := endpointBounded X M hM
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects X.obj).ι).ShortExact at hS
    exact (hS.map_of_exact (AlgebraicGeometry.Scheme.Modules.Complex.pullback (nativeProjection.app
      X).hom)).map_of_exact
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft M)

lemma endpointBounded_exact (M : (nativeLineFunctor.obj X).obj.Modules)
    [IsFiniteLocallyFree (nativeLineFunctor.obj X).obj M]
    (hM : ∀ K, locallyPerfect (nativeLineFunctor.obj X).obj ((endpointComplex X M).obj K)) :
    Waldhausen.IsExact (FlasqueBoundedBelow.waldhausen X.obj).cof
      (FlasqueBoundedBelow.waldhausen X.obj).weq
      (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
      (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq (endpointBounded X M hM) where
  zero h := (endpointBounded X M hM).map_isZero h
  cofibration f hf := (endpointBoundedExactFunctor X M hM).map_inflation f hf
  weak {A B} f hf := by
    let : QuasiIso f.hom := hf
    change QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft M).map
      ((AlgebraicGeometry.Scheme.Modules.Complex.pullback (nativeProjection.app X).hom).map f.hom))
    infer_instance
  pushout hi h := (endpointBoundedExactFunctor X M hM).map_isPushout hi h

/-- Actual totalization precedes every ordinary native projection. -/
def projectedEndpoint (M : (nativeLineFunctor.obj X).obj.Modules)
    (hM : ∀ K, locallyPerfect (nativeLineFunctor.obj X).obj ((endpointComplex X M).obj K)) :=
  endpointBounded X M hM ⋙ FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj ⋙
    P5NativeCoefficients.G0 X

lemma projectedEndpoint_exact (M : (nativeLineFunctor.obj X).obj.Modules)
    [IsFiniteLocallyFree (nativeLineFunctor.obj X).obj M]
    (hM : ∀ K, locallyPerfect (nativeLineFunctor.obj X).obj ((endpointComplex X M).obj K)) :
    Waldhausen.IsExact (FlasqueBoundedBelow.waldhausen X.obj).cof
      (FlasqueBoundedBelow.waldhausen X.obj).weq (FlasqueBoundedBelow.waldhausen X.obj).cof
      (FlasqueBoundedBelow.waldhausen X.obj).weq (projectedEndpoint X M hM) :=
  (endpointBounded_exact X M hM).comp
    ((FlasqueBoundedBelow.total_exact _).comp (P5NativeCoefficients.G0_exact X))

/-- Original square endpoint after totalization and ordinary projection. -/
def E2 := projectedEndpoint X (sequence X).X₁ (squareEndpoint_locallyPerfect X)

/-- Original middle endpoint after totalization and ordinary projection. -/
def E1 := projectedEndpoint X (sequence X).X₂ (middleEndpoint_locallyPerfect X)

/-- Original unit endpoint after totalization and ordinary projection. -/
def E0 := projectedEndpoint X (sequence X).X₃ (unitEndpoint_locallyPerfect X)

lemma E2_exact : Waldhausen.IsExact (FlasqueBoundedBelow.waldhausen X.obj).cof
    (FlasqueBoundedBelow.waldhausen X.obj).weq (FlasqueBoundedBelow.waldhausen X.obj).cof
    (FlasqueBoundedBelow.waldhausen X.obj).weq (E2 X) := projectedEndpoint_exact X _ _

lemma E1_exact : Waldhausen.IsExact (FlasqueBoundedBelow.waldhausen X.obj).cof
    (FlasqueBoundedBelow.waldhausen X.obj).weq (FlasqueBoundedBelow.waldhausen X.obj).cof
    (FlasqueBoundedBelow.waldhausen X.obj).weq (E1 X) := projectedEndpoint_exact X _ _

lemma E0_exact : Waldhausen.IsExact (FlasqueBoundedBelow.waldhausen X.obj).cof
    (FlasqueBoundedBelow.waldhausen X.obj).weq (FlasqueBoundedBelow.waldhausen X.obj).cof
    (FlasqueBoundedBelow.waldhausen X.obj).weq (E0 X) := projectedEndpoint_exact X _ _

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeEuler
