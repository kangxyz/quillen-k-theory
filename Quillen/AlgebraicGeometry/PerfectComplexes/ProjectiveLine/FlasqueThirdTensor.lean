/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalComparisons
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientOperations
public import Aglib.AlgebraicGeometry.Cohomology.Godement.Section.Span

/-! # Original right quotient-line tensor and its flasque total -/

@[expose] public section

open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueThirdEndpoint

/-- The actual original right tensor by Q on arbitrary module coefficients. -/
abbrev quotientTensor (R : CommRingCat.{u}) :=
  moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)

instance quotientTensor_preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (quotientTensor R) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance quotientTensor_preservesFiniteColimits (R : CommRingCat.{u}) :
    PreservesFiniteColimits (quotientTensor R) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- The prescribed original order K tensor Q, retaining each original chain map. -/
def rightQRaw (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ Complex (twoChartLine R) :=
  (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
    (quotientTensor R).mapHomologicalComplex (.up ℤ)

instance rightQRaw_additive (R : CommRingCat.{u}) : (rightQRaw R).Additive := by
  dsimp [rightQRaw]
  infer_instance

/-- Original quotient charts and the actual tensor braiding prove local perfection. -/
lemma rightQ_locallyPerfect (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    locallyPerfect (twoChartLine R) ((rightQRaw R).obj K) := by
  change locallyPerfect (twoChartLine R)
    ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalQuotientLine R)).obj K.obj)
  exact locallyPerfect_of_iso
    ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeftRightIso (tautologicalQuotientLine R)).app
      K.obj)
    (FlasqueDiagonal.quotientLeft_locallyPerfect R K.obj K.property.1.1)

/-- The original right tensor preserves every specified strict lower bound. -/
lemma rightQ_isStrictlyGE (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((rightQRaw R).obj K).IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (quotientTensor R).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)

/-- The actual right tensor is bounded and perfect before applying totalization. -/
lemma rightQ_objects (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    BoundedBelow.objects (twoChartLine R) ((rightQRaw R).obj K) := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  exact ⟨rightQ_locallyPerfect R K, a, rightQ_isStrictlyGE R K a⟩

/-- The original right-Q tensor in the bounded perfect category. -/
def rightQ (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ BoundedBelow.Obj (twoChartLine R) :=
  ObjectProperty.lift _ (rightQRaw R) (rightQ_objects R)

instance rightQ_additive (R : CommRingCat.{u}) : (rightQ R).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    exact (rightQRaw R).map_add

/-- Exact finite-line tensor preserves the actual inherited original sequences. -/
def rightQExactFunctor (R : CommRingCat.{u}) : ExactFunctor
    (FlasqueDiagonal.modelExactStructure R)
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (BoundedBelow.objects (twoChartLine R))) where
  toFunctor := rightQ R
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact at hS
    change ((S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).map
      ((quotientTensor R).mapHomologicalComplex (.up ℤ))).ShortExact
    exact hS.map_of_exact _

/-- The actual original tensor preserves zero, cofibrations, weak arrows and pushouts. -/
lemma rightQ_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq (rightQ R) where
  zero h := (rightQ R).map_isZero h
  cofibration f hf := (rightQExactFunctor R).map_inflation f hf
  weak f hf := by
    change QuasiIso f.hom at hf
    let := hf
    change QuasiIso (((quotientTensor R).mapHomologicalComplex (.up ℤ)).map f.hom)
    exact HomologicalComplex.quasiIso_map_of_preservesHomology f.hom (quotientTensor R)
  pushout hi h := (rightQExactFunctor R).map_isPushout hi h

/-- The required original flasque endpoint T_P(K tensor Q). -/
def rightQTotal (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ FlasqueBoundedBelow.Obj (twoChartLine R) :=
  rightQ R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

/-- Each specified input lower bound is retained after the actual source total. -/
lemma rightQTotal_isStrictlyGE (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((rightQTotal R).obj K).obj.IsStrictlyGE a := by
  let : ((rightQ R).obj K).obj.IsStrictlyGE a := rightQ_isStrictlyGE R K a
  exact FlasqueBoundedBelow.total_isStrictlyGE (twoChartLine R) ((rightQ R).obj K) a

/-- Actual right tensor followed by actual totalization is Waldhausen-exact. -/
lemma rightQTotal_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (rightQTotal R) :=
  (rightQ_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueThirdEndpoint
