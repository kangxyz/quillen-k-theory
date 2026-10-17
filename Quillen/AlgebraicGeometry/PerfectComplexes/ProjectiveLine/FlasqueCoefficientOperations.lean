/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Shift


public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.TensorByLineRightExact


public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineTensor
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological

/-!
# Original right tensor and shift for exact flasque coefficients

Right tensor by the actual tautological line is exact before Godement total.
The original shift preserves the flasque model and its inherited exact structure.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen



open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients

/-- The actual original two charts of the projective line. -/
def lineChart (R : CommRingCat.{u}) (b : Bool) :
    Spec (CommRingCat.of (Polynomial R)) ⟶ twoChartLine R :=
  if b then plusChart R else minusChart R

instance lineChart_isOpenImmersion (R : CommRingCat.{u}) (b : Bool) :
    IsOpenImmersion (lineChart R b) := by
  cases b <;> dsimp [lineChart] <;> infer_instance

lemma lineChart_cover (R : CommRingCat.{u}) (x : twoChartLine R) :
    ∃ b y, lineChart R b y = x := by
  have hx : x ∈ (plusChart R).opensRange ⊔ (minusChart R).opensRange := by
    rw [chart_ranges_cover]
    trivial
  change (∃ y, plusChart R y = x) ∨ (∃ y, minusChart R y = x) at hx
  rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact ⟨true, y, hy⟩
  · exact ⟨false, y, hy⟩

/-- The actual original tautological trivializations, with the original chart order. -/
def lineChartIso (R : CommRingCat.{u}) (b : Bool) :
    (tautologicalLine R).restrict (lineChart R b) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Polynomial R))).ringCatSheaf := by
  cases b
  · exact tautologicalLineMinusIso R
  · exact tautologicalLinePlusIso R

/-- Original K tensor L remains locally perfect by the actual tensor symmetry. -/
lemma rightTensor_locallyPerfect (R : CommRingCat.{u})
    {K : CochainComplex (twoChartLine R).Modules ℤ}
    (hK : locallyPerfect (twoChartLine R) K) :
    locallyPerfect (twoChartLine R) ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight
      (tautologicalLine R)).obj K) :=
  locallyPerfect_of_iso ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeftRightIso
    (tautologicalLine R)).app K)
    (locallyPerfect_tensorByLine (tautologicalLine R)
      (fun _ : Bool => Spec (CommRingCat.of (Polynomial R)))
      (lineChart R) (lineChart_cover R) (lineChartIso R) hK)

/-- Right tensor preserves a specified strict lower bound. -/
lemma rightTensor_isStrictlyGE (R : CommRingCat.{u}) (K : CochainComplex (twoChartLine R).Modules ℤ)
    (a : ℤ) [K.IsStrictlyGE a] :
    ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).obj K).IsStrictlyGE
      a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (moduleTensorByLineRight (tautologicalLine R)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K a n hn)

/-- Actual right tensor has lower-bounded perfect values before the flasque totalization. -/
lemma rightTensor_objects (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    BoundedBelow.objects (twoChartLine R)
      ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).obj K.obj) := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  exact ⟨rightTensor_locallyPerfect R K.property.1.1, a,
    rightTensor_isStrictlyGE R K.obj a⟩

/-- The right tensor in the prescribed original coefficient order K tensor L. -/
def rightTensor (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ BoundedBelow.Obj (twoChartLine R) :=
  ObjectProperty.lift _ ((FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)) (rightTensor_objects
      R)

instance rightTensor_additive (R : CommRingCat.{u}) : (rightTensor R).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).map (f.hom +
      g.hom) =
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).map f.hom +
        (AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).map g.hom
    exact CategoryTheory.Functor.map_add _

/-- Right tensor preserves the actual inherited short exact sequences. -/
def rightTensorExactFunctor (R : CommRingCat.{u}) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex (twoChartLine R).Modules ℤ))
      (FlasqueBoundedBelow.objects (twoChartLine R)))
    (ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex (twoChartLine R).Modules ℤ))
      (BoundedBelow.objects (twoChartLine R))) where
  toFunctor := rightTensor R
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact at hS
    change ((S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).map
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R))).ShortExact
    exact hS.map_of_exact _

lemma rightTensor_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq (rightTensor R) where
  zero h := (rightTensor R).map_isZero h
  cofibration f hf := (rightTensorExactFunctor R).map_inflation f hf
  weak f hf := by
    change QuasiIso f.hom at hf
    let := hf
    exact AlgebraicGeometry.Scheme.Modules.Complex.tensorRight_quasiIso (tautologicalLine R) f.hom
  pushout hi h := (rightTensorExactFunctor R).map_isPushout hi h

lemma modelShift_exact (X : Scheme.{u}) (n : ℤ) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen X).cof (FlasqueBoundedBelow.waldhausen X).weq
    (FlasqueBoundedBelow.waldhausen X).cof (FlasqueBoundedBelow.waldhausen X).weq
    (modelShift X n) where
  zero h := (modelShift X n).map_isZero h
  cofibration f hf := (modelShiftExactFunctor X n).map_inflation f hf
  weak f hf := by
    change QuasiIso f.hom at hf
    let := hf
    change QuasiIso (f.hom⟦n⟧')
    infer_instance
  pushout hi h := (modelShiftExactFunctor X n).map_isPushout hi h

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
