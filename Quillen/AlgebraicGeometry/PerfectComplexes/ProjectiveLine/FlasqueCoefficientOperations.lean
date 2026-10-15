/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineTensor
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological

/-!
# Original right tensor and shift for exact flasque coefficients

Right tensor by the actual tautological line is exact before Godement total.
The original shift preserves the flasque model and its inherited exact structure.
-/
@[expose] public section

open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients

instance rightLineModule_preservesFiniteLimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteLimits (moduleTensorByLineRight L) :=
  preservesFiniteLimits_of_natIso (moduleTensorByLineSymmetry L)

instance rightLineModule_preservesFiniteColimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteColimits (moduleTensorByLineRight L) :=
  preservesFiniteColimits_of_natIso (moduleTensorByLineSymmetry L)

instance rightLineModule_preservesHomology {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : (moduleTensorByLineRight L).PreservesHomology :=
  ((CategoryTheory.Functor.exact_tfae (moduleTensorByLineRight L)).out 1 3).mp
    (fun (S : ShortComplex X.Modules) (hs : S.ShortExact) =>
      hs.map_of_exact (moduleTensorByLineRight L))

instance rightLineComplex_additive {X : Scheme.{u}} (L : X.Modules) :
    (tensorByLineRightComplex L).Additive := by
  unfold tensorByLineRightComplex
  infer_instance

instance rightLineComplex_preservesFiniteLimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteLimits (tensorByLineRightComplex L) := by
  unfold tensorByLineRightComplex
  infer_instance

instance rightLineComplex_preservesFiniteColimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteColimits (tensorByLineRightComplex L) := by
  unfold tensorByLineRightComplex
  infer_instance

instance rightLineComplex_quasiIso {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] {K M : Complex X} (f : K ⟶ M) [QuasiIso f] :
    QuasiIso ((tensorByLineRightComplex L).map f) := by
  unfold tensorByLineRightComplex
  infer_instance

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
lemma rightTensor_locallyPerfect (R : CommRingCat.{u}) {K : Complex (twoChartLine R)}
    (hK : locallyPerfect (twoChartLine R) K) :
    locallyPerfect (twoChartLine R) ((tensorByLineRightComplex (tautologicalLine R)).obj K) :=
  locallyPerfect_of_iso ((tensorByLineComplexSymmetry (tautologicalLine R)).app K)
    (locallyPerfect_tensorByLine (tautologicalLine R)
      (fun _ : Bool => Spec (CommRingCat.of (Polynomial R)))
      (lineChart R) (lineChart_cover R) (lineChartIso R) hK)

/-- Right tensor preserves a specified strict lower bound. -/
lemma rightTensor_isStrictlyGE (R : CommRingCat.{u}) (K : Complex (twoChartLine R))
    (a : ℤ) [K.IsStrictlyGE a] :
    ((tensorByLineRightComplex (tautologicalLine R)).obj K).IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (moduleTensorByLineRight (tautologicalLine R)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K a n hn)

/-- Actual right tensor has lower-bounded perfect values before the flasque totalization. -/
lemma rightTensor_objects (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    BoundedBelow.objects (twoChartLine R)
      ((tensorByLineRightComplex (tautologicalLine R)).obj K.obj) := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  exact ⟨rightTensor_locallyPerfect R K.property.1.1, a,
    rightTensor_isStrictlyGE R K.obj a⟩

/-- The right tensor in the prescribed original coefficient order K tensor L. -/
def rightTensor (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ BoundedBelow.Obj (twoChartLine R) :=
  ObjectProperty.lift _ ((FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
    tensorByLineRightComplex (tautologicalLine R)) (rightTensor_objects R)

instance rightTensor_additive (R : CommRingCat.{u}) : (rightTensor R).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (tensorByLineRightComplex (tautologicalLine R)).map (f.hom + g.hom) =
      (tensorByLineRightComplex (tautologicalLine R)).map f.hom +
        (tensorByLineRightComplex (tautologicalLine R)).map g.hom
    exact CategoryTheory.Functor.map_add _

/-- Right tensor preserves the actual inherited short exact sequences. -/
def rightTensorExactFunctor (R : CommRingCat.{u}) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (FlasqueBoundedBelow.objects (twoChartLine R)))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (BoundedBelow.objects (twoChartLine R))) where
  toFunctor := rightTensor R
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact at hS
    change ((S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).map
      (tensorByLineRightComplex (tautologicalLine R))).ShortExact
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
    exact rightLineComplex_quasiIso (tautologicalLine R) f.hom
  pushout hi h := (rightTensorExactFunctor R).map_isPushout hi h

/-- Original shift preserves the full flasque-perfect object predicate. -/
lemma shift_objects {X : Scheme.{u}} {K : Complex X}
    (hK : FlasqueBoundedBelow.objects X K) (n : ℤ) :
    FlasqueBoundedBelow.objects X (K⟦n⟧) := by
  refine ⟨BoundedBelow.objects_shift hK.1 n, fun i => ?_⟩
  let : TopCat.Presheaf.IsFlasque (K.X (i + n)).presheaf := hK.2 (i + n)
  exact flasque_of_iso (K.shiftFunctorObjXIso n i (i + n) rfl).symm

/-- The literal standard original cochain shift, including its differential sign. -/
def modelShift (X : Scheme.{u}) (n : ℤ) :
    FlasqueBoundedBelow.Obj X ⥤ FlasqueBoundedBelow.Obj X :=
  ObjectProperty.lift _ ((FlasqueBoundedBelow.objects X).ι ⋙ shiftFunctor (Complex X) n)
    (fun K => shift_objects K.property n)

instance modelShift_additive (X : Scheme.{u}) (n : ℤ) : (modelShift X n).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (shiftFunctor (Complex X) n).map (f.hom + g.hom) =
      (shiftFunctor (Complex X) n).map f.hom + (shiftFunctor (Complex X) n).map g.hom
    exact CategoryTheory.Functor.map_add _

/-- Original shift preserves the inherited actual exact sequences. -/
def modelShiftExactFunctor (X : Scheme.{u}) (n : ℤ) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex X))
      (FlasqueBoundedBelow.objects X))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex X))
      (FlasqueBoundedBelow.objects X)) where
  toFunctor := modelShift X n
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects X).ι).ShortExact at hS
    change ((S.map (FlasqueBoundedBelow.objects X).ι).map (shiftFunctor (Complex X) n)).ShortExact
    exact hS.map_of_exact _

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
