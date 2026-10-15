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
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlasqueBoundedBelowComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTwoSummands
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.NativeBaseChange
public import Quillen.Waldhausen.ExactFunctor

/-!
# Actual local two-chart flasque two-summand functor

The two original summands are flat pullback and its original negative-line
tensor, in O/O(-1) order. Their actual sum is followed by the admitted natural
Godement total. Native affine-target correspondence is a separate geometry step.
-/
@[expose] public section

open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands

/-- Literal flat geometric pullback on original lower-bounded perfect complexes. -/
def boundedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    BoundedBelow.Obj Y ⥤ BoundedBelow.Obj X :=
  ObjectProperty.lift _ ((BoundedBelow.objects Y).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.pullback f) (fun K => by
    obtain ⟨hp, a, ha⟩ := K.property
    let := ha
    refine ⟨locallyPerfect_flatPullback f hp, a, ?_⟩
    apply (CochainComplex.isStrictlyGE_iff _ a).mpr
    intro n hn
    exact (Scheme.Modules.pullback f).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn))

instance boundedPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (boundedPullback f).Additive := by
  unfold boundedPullback
  infer_instance

/-- Original flat pullback preserves inherited actual exact sequences. -/
def boundedPullbackExactFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex Y))
      (BoundedBelow.objects Y))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex X))
      (BoundedBelow.objects X)) where
  toFunctor := boundedPullback f
  map_conflation S hs := by
    change (S.map (BoundedBelow.objects Y).ι).ShortExact at hs
    change ((S.map (BoundedBelow.objects Y).ι).map
      (AlgebraicGeometry.Scheme.Modules.Complex.pullback f)).ShortExact
    exact hs.map_of_exact _

lemma boundedPullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] : Waldhausen.IsExact
    (BoundedBelow.waldhausen Y).cof (BoundedBelow.waldhausen Y).weq
    (BoundedBelow.waldhausen X).cof (BoundedBelow.waldhausen X).weq (boundedPullback f) where
  zero h := (boundedPullback f).map_isZero h
  cofibration s hs := (boundedPullbackExactFunctor f).map_inflation s hs
  weak s hs := by
    change QuasiIso s.hom at hs
    let := hs
    exact AlgebraicGeometry.Scheme.Modules.Complex.pullback_quasiIso f s.hom
  pushout hi h := (boundedPullbackExactFunctor f).map_isPushout hi h

/-- Original tautological chart trivializations, retaining the original Boolean chart order. -/
def lineChartIso (R : CommRingCat.{u}) (b : Bool) :
    (tautologicalLine R).restrict (polynomialChart R b) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Polynomial R))).ringCatSheaf := by
  cases b
  · exact tautologicalLineMinusIso R
  · exact tautologicalLinePlusIso R

/-- Actual original negative-line tensor on the lower-bounded perfect category. -/
def boundedNegativeTwist (R : CommRingCat.{u}) :
    BoundedBelow.Obj (twoChartLine R) ⥤ BoundedBelow.Obj (twoChartLine R) :=
  ObjectProperty.lift _ ((BoundedBelow.objects (twoChartLine R)).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)) (fun K => by
      obtain ⟨hp, a, ha⟩ := K.property
      let := ha
      refine ⟨locallyPerfect_tensorByLine (tautologicalLine R)
        (fun _ : Bool => Spec (CommRingCat.of (Polynomial R))) (polynomialChart R)
        (polynomialChart_cover R) (lineChartIso R) hp, a, ?_⟩
      apply (CochainComplex.isStrictlyGE_iff _ a).mpr
      intro n hn
      exact (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn))

instance boundedNegativeTwist_additive (R : CommRingCat.{u}) :
    (boundedNegativeTwist R).Additive := by
  unfold boundedNegativeTwist
  infer_instance

/-- Left tensor by the tautological line on bounded-below perfect complexes, bundled with
preservation of degreewise short exact sequences.
-/
def boundedNegativeTwistExactFunctor (R : CommRingCat.{u}) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (BoundedBelow.objects (twoChartLine R)))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (BoundedBelow.objects (twoChartLine R))) where
  toFunctor := boundedNegativeTwist R
  map_conflation S hs := by
    change (S.map (BoundedBelow.objects (twoChartLine R)).ι).ShortExact at hs
    change ((S.map (BoundedBelow.objects (twoChartLine R)).ι).map
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R))).ShortExact
    exact hs.map_of_exact _

lemma boundedNegativeTwist_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (BoundedBelow.waldhausen (twoChartLine R)).cof (BoundedBelow.waldhausen (twoChartLine R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof (BoundedBelow.waldhausen (twoChartLine R)).weq
    (boundedNegativeTwist R) where
  zero h := (boundedNegativeTwist R).map_isZero h
  cofibration s hs := (boundedNegativeTwistExactFunctor R).map_inflation s hs
  weak s hs := by
    change QuasiIso s.hom at hs
    let := hs
    exact AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft_quasiIso (tautologicalLine R) s.hom
  pushout hi h := (boundedNegativeTwistExactFunctor R).map_isPushout hi h

/-- The literal structure summand from the original flasque input model. -/
def first (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (Spec R) ⥤ BoundedBelow.Obj (twoChartLine R) :=
  FlasqueBoundedBelow.inclusion (Spec R) ⋙ boundedPullback (projection R)

/-- The original negative-line summand, with its native left/right tensor comparison retained. -/
def second (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (Spec R) ⥤ BoundedBelow.Obj (twoChartLine R) :=
  first R ⋙ boundedNegativeTwist R

/-- This component is the actual native symmetry to prescribed pullback tensor L order. -/
def secondTensorOrderIso (R : CommRingCat.{u}) (K : FlasqueBoundedBelow.Obj (Spec R)) :
    ((second R).obj K).obj ≅
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).obj
        ((AlgebraicGeometry.Scheme.Modules.Complex.pullback (projection R)).obj K.obj) :=
  (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeftRightIso (tautologicalLine R)).app _

lemma first_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof (FlasqueBoundedBelow.waldhausen (Spec R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof (BoundedBelow.waldhausen (twoChartLine R)).weq
    (first R) :=
  (FlasqueBoundedBelow.inclusion_exact (Spec R)).comp (boundedPullback_exact (projection R))

lemma second_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof (FlasqueBoundedBelow.waldhausen (Spec R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof (BoundedBelow.waldhausen (twoChartLine R)).weq
    (second R) := (first_exact R).comp (boundedNegativeTwist_exact R)

/-- Actual original two-summand coproduct, in O/O(-1) order, before totalization. -/
def beforeTotal (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (Spec R) × FlasqueBoundedBelow.Obj (Spec R) ⥤
      BoundedBelow.Obj (twoChartLine R) :=
  Waldhausen.Additivity.sumFunctor
    (CategoryTheory.Prod.fst _ _ ⋙ first R) (CategoryTheory.Prod.snd _ _ ⋙ second R)

lemma beforeTotal_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).cof
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof (BoundedBelow.waldhausen (twoChartLine R)).weq
    (beforeTotal R) :=
  Waldhausen.Additivity.sumFunctor_isExact _ _
    ((Waldhausen.ExtensionCategory.fst_exact _ _).comp (first_exact R))
    ((Waldhausen.ExtensionCategory.snd_exact _ _).comp (second_exact R))

/-- The actual original flasque Phi is totalization of the original two-summand coproduct. -/
def Phi (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (Spec R) × FlasqueBoundedBelow.Obj (Spec R) ⥤
      FlasqueBoundedBelow.Obj (twoChartLine R) :=
  beforeTotal R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

lemma Phi_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).cof
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (Phi R) :=
  (beforeTotal_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

/-- The comparison is the actual forward total augmentation in the original bounded model. -/
def PhiUnit (R : CommRingCat.{u}) :
    beforeTotal R ⟶ Phi R ⋙ FlasqueBoundedBelow.inclusion (twoChartLine R) :=
  CategoryTheory.Functor.whiskerLeft (beforeTotal R) (FlasqueBoundedBelow.unit (twoChartLine R))

lemma PhiUnit_weak (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (Spec R) × FlasqueBoundedBelow.Obj (Spec R)) :
    (BoundedBelow.waldhausen (twoChartLine R)).weq ((PhiUnit R).app K) :=
  FlasqueBoundedBelow.unit_weak _ _

/-- The literal bounded-model inclusion recovers the actual pre-total sum K-map, in every degree. -/
lemma Phi_KMap_after_boundedInclusion (R : CommRingCat.{u}) (n : ℕ) :
    (Waldhausen.KMap (FlasqueBoundedBelow.inclusion_exact (twoChartLine R)) n).comp
        (Waldhausen.KMap (Phi_exact R) n) =
      Waldhausen.KMap (beforeTotal_exact R) n := by
  rw [Waldhausen.KMap_comp_KMap]
  exact (Waldhausen.KMap_eq_of_weakNatTrans (beforeTotal_exact R)
    ((Phi_exact R).comp (FlasqueBoundedBelow.inclusion_exact (twoChartLine R)))
    (PhiUnit R) (PhiUnit_weak R) n).symm

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
