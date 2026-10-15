/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeCoefficientsZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientOperations
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTwoSummands

/-! # Native right tensor before the original flasque total

Local perfection follows from the actual two native chart trivializations.
Right tensor retains its actual order, maps and lower bound; its output is not
asserted flasque before Godement totalization.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeCoefficients
open FlasqueCoefficients AlgebraicGeometry.Scheme.Bass

/-- Original K tensor L remains locally perfect by the actual tensor symmetry. -/
lemma rightTensor_locallyPerfect (X : QuasiCompactSchemes.{u}) {K : Complex
    (nativeLineFunctor.obj X).obj}
    (hK : locallyPerfect (nativeLineFunctor.obj X).obj K) :
    locallyPerfect (nativeLineFunctor.obj X).obj ((tensorByLineRightComplex
      (nativeTautologicalLine X)).obj K) :=
  locallyPerfect_of_iso ((tensorByLineComplexSymmetry (nativeTautologicalLine X)).app K)
    (locallyPerfect_tensorByLine (nativeTautologicalLine X)
      (fun _ : Bool => (polynomialFunctor.obj X).obj)
      (nativeChart X) (nativeChart_cover X) (nativeLineChartIso X) hK)

/-- Right tensor preserves a specified strict lower bound. -/
lemma rightTensor_isStrictlyGE (X : QuasiCompactSchemes.{u}) (K : Complex (nativeLineFunctor.obj
    X).obj)
    (a : ℤ) [K.IsStrictlyGE a] :
    ((tensorByLineRightComplex (nativeTautologicalLine X)).obj K).IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (moduleTensorByLineRight (nativeTautologicalLine X)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K a n hn)

/-- Actual right tensor has lower-bounded perfect values before the flasque totalization. -/
lemma rightTensor_objects (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) :
    BoundedBelow.objects (nativeLineFunctor.obj X).obj
      ((tensorByLineRightComplex (nativeTautologicalLine X)).obj K.obj) := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  exact ⟨rightTensor_locallyPerfect X K.property.1.1, a,
    rightTensor_isStrictlyGE X K.obj a⟩

/-- The right tensor in the prescribed original coefficient order K tensor L. -/
def rightTensor (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj ⥤ BoundedBelow.Obj
      (nativeLineFunctor.obj X).obj :=
  ObjectProperty.lift _ ((FlasqueBoundedBelow.objects (nativeLineFunctor.obj X).obj).ι ⋙
    tensorByLineRightComplex (nativeTautologicalLine X)) (rightTensor_objects X)

instance rightTensor_additive (X : QuasiCompactSchemes.{u}) : (rightTensor X).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (tensorByLineRightComplex (nativeTautologicalLine X)).map (f.hom + g.hom) =
      (tensorByLineRightComplex (nativeTautologicalLine X)).map f.hom +
        (tensorByLineRightComplex (nativeTautologicalLine X)).map g.hom
    exact CategoryTheory.Functor.map_add _

/-- Right tensor preserves the actual inherited short exact sequences. -/
def rightTensorExactFunctor (X : QuasiCompactSchemes.{u}) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (nativeLineFunctor.obj X).obj))
      (FlasqueBoundedBelow.objects (nativeLineFunctor.obj X).obj))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (nativeLineFunctor.obj X).obj))
      (BoundedBelow.objects (nativeLineFunctor.obj X).obj)) where
  toFunctor := rightTensor X
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects (nativeLineFunctor.obj X).obj).ι).ShortExact at hS
    change ((S.map (FlasqueBoundedBelow.objects (nativeLineFunctor.obj X).obj).ι).map
      (tensorByLineRightComplex (nativeTautologicalLine X))).ShortExact
    exact hS.map_of_exact _

lemma rightTensor_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).cof
    (BoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).weq (rightTensor X) where
  zero h := (rightTensor X).map_isZero h
  cofibration f hf := (rightTensorExactFunctor X).map_inflation f hf
  weak f hf := by
    change QuasiIso f.hom at hf
    let := hf
    exact rightLineComplex_quasiIso (nativeTautologicalLine X) f.hom
  pushout hi h := (rightTensorExactFunctor X).map_isPushout hi h


end Quillen.PerfectComplexes.ProjectiveLine.P5NativeCoefficients
