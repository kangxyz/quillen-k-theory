/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueTwoSummandComparison
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.NativeBaseChange

/-! # The original forward flasque Phi over every native quasi-compact base

The original two-summand coproduct retains O/O(-1) order and left tensor.
Only the actual Godement totalization asserts flasqueness. Native flatness and
the original native line chart trivializations discharge the geometric inputs.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Bass AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi
open FlasqueTwoSummands

/-- Actual original negative-line tensor on the lower-bounded perfect category. -/
def boundedNegativeTwist (X : QuasiCompactSchemes.{u}) :
    BoundedBelow.Obj (nativeLineFunctor.obj X).obj ⥤ BoundedBelow.Obj (nativeLineFunctor.obj
      X).obj :=
  ObjectProperty.lift _ ((BoundedBelow.objects (nativeLineFunctor.obj X).obj).ι ⋙
    tensorByLineComplex (nativeTautologicalLine X)) (fun K => by
      obtain ⟨hp, a, ha⟩ := K.property
      let := ha
      refine ⟨locallyPerfect_tensorByLine (nativeTautologicalLine X)
        (fun _ : Bool => (polynomialFunctor.obj X).obj) (nativeChart X)
        (nativeChart_cover X) (nativeLineChartIso X) hp, a, ?_⟩
      apply (CochainComplex.isStrictlyGE_iff _ a).mpr
      intro n hn
      exact (moduleTensorLeftFunctor (nativeLineFunctor.obj X).obj (nativeTautologicalLine
        X)).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn))

instance boundedNegativeTwist_additive (X : QuasiCompactSchemes.{u}) :
    (boundedNegativeTwist X).Additive := by
  unfold boundedNegativeTwist
  infer_instance

def boundedNegativeTwistExactFunctor (X : QuasiCompactSchemes.{u}) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (nativeLineFunctor.obj X).obj))
      (BoundedBelow.objects (nativeLineFunctor.obj X).obj))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (nativeLineFunctor.obj X).obj))
      (BoundedBelow.objects (nativeLineFunctor.obj X).obj)) where
  toFunctor := boundedNegativeTwist X
  map_conflation S hs := by
    change (S.map (BoundedBelow.objects (nativeLineFunctor.obj X).obj).ι).ShortExact at hs
    change ((S.map (BoundedBelow.objects (nativeLineFunctor.obj X).obj).ι).map
      (tensorByLineComplex (nativeTautologicalLine X))).ShortExact
    exact hs.map_of_exact _

lemma boundedNegativeTwist_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof (BoundedBelow.waldhausen
      (nativeLineFunctor.obj X).obj).weq
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof (BoundedBelow.waldhausen
      (nativeLineFunctor.obj X).obj).weq
    (boundedNegativeTwist X) where
  zero h := (boundedNegativeTwist X).map_isZero h
  cofibration s hs := (boundedNegativeTwistExactFunctor X).map_inflation s hs
  weak s hs := by
    change QuasiIso s.hom at hs
    let := hs
    exact tensorByLineComplex_quasiIso (nativeTautologicalLine X) s.hom
  pushout hi h := (boundedNegativeTwistExactFunctor X).map_isPushout hi h

/-- The literal structure summand from the original flasque input model. -/
def first (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj X.obj ⥤ BoundedBelow.Obj (nativeLineFunctor.obj X).obj :=
  FlasqueBoundedBelow.inclusion X.obj ⋙ boundedPullback (nativeProjection.app X).hom

/-- The original negative-line summand, with its native left/right tensor comparison retained. -/
def second (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj X.obj ⥤ BoundedBelow.Obj (nativeLineFunctor.obj X).obj :=
  first X ⋙ boundedNegativeTwist X

/-- This component is the actual native symmetry to prescribed pullback tensor L order. -/
def secondTensorOrderIso (X : QuasiCompactSchemes.{u}) (K : FlasqueBoundedBelow.Obj X.obj) :
    ((second X).obj K).obj ≅
      (tensorByLineRightComplex (nativeTautologicalLine X)).obj
        ((pullbackComplex (nativeProjection.app X).hom).obj K.obj) :=
  (tensorByLineComplexSymmetry (nativeTautologicalLine X)).app _

lemma first_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof (BoundedBelow.waldhausen
      (nativeLineFunctor.obj X).obj).weq
    (first X) :=
  (FlasqueBoundedBelow.inclusion_exact X.obj).comp (boundedPullback_exact (nativeProjection.app
    X).hom)

lemma second_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X.obj).cof (FlasqueBoundedBelow.waldhausen X.obj).weq
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof (BoundedBelow.waldhausen
      (nativeLineFunctor.obj X).obj).weq
    (second X) := (first_exact X).comp (boundedNegativeTwist_exact X)

/-- Actual original two-summand coproduct, in O/O(-1) order, before totalization. -/
def beforeTotal (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj ⥤
      BoundedBelow.Obj (nativeLineFunctor.obj X).obj :=
  Waldhausen.Additivity.sumFunctor
    (CategoryTheory.Prod.fst _ _ ⋙ first X) (CategoryTheory.Prod.snd _ _ ⋙ second X)

lemma beforeTotal_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen X.obj) (FlasqueBoundedBelow.waldhausen X.obj)).cof
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen X.obj) (FlasqueBoundedBelow.waldhausen X.obj)).weq
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof (BoundedBelow.waldhausen
      (nativeLineFunctor.obj X).obj).weq
    (beforeTotal X) :=
  Waldhausen.Additivity.sumFunctor_isExact _ _
    ((Waldhausen.ExtensionCategory.fst_exact _ _).comp (first_exact X))
    ((Waldhausen.ExtensionCategory.snd_exact _ _).comp (second_exact X))

/-- The actual original flasque Phi is totalization of the original two-summand coproduct. -/
def Phi (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj ⥤
      FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj :=
  beforeTotal X ⋙ FlasqueBoundedBelow.total (nativeLineFunctor.obj X).obj

lemma Phi_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen X.obj) (FlasqueBoundedBelow.waldhausen X.obj)).cof
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen X.obj) (FlasqueBoundedBelow.waldhausen X.obj)).weq
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq (Phi X) :=
  (beforeTotal_exact X).comp (FlasqueBoundedBelow.total_exact (nativeLineFunctor.obj X).obj)

/-- The comparison is the actual forward total augmentation in the original bounded model. -/
def PhiUnit (X : QuasiCompactSchemes.{u}) :
    beforeTotal X ⟶ Phi X ⋙ FlasqueBoundedBelow.inclusion (nativeLineFunctor.obj X).obj :=
  CategoryTheory.Functor.whiskerLeft (beforeTotal X) (FlasqueBoundedBelow.unit
    (nativeLineFunctor.obj X).obj)

lemma PhiUnit_weak (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj) :
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq ((PhiUnit X).app K) :=
  FlasqueBoundedBelow.unit_weak _ _

/-- The literal bounded-model inclusion recovers the actual pre-total sum K-map, in every degree. -/
lemma Phi_KMap_after_boundedInclusion (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (Waldhausen.KMap (FlasqueBoundedBelow.inclusion_exact (nativeLineFunctor.obj X).obj) n).comp
        (Waldhausen.KMap (Phi_exact X) n) =
      Waldhausen.KMap (beforeTotal_exact X) n := by
  rw [Waldhausen.KMap_comp_KMap]
  exact (Waldhausen.KMap_eq_of_weakNatTrans (beforeTotal_exact X)
    ((Phi_exact X).comp (FlasqueBoundedBelow.inclusion_exact (nativeLineFunctor.obj X).obj))
    (PhiUnit X) (PhiUnit_weak X) n).symm

end Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi
