/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5LocallySplitTensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.EulerFunctors
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Native
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.PullbackTensorCompatibility

/-! # The actual native Euler sequence with canonical tensor and unit normalizations

The original integer Euler sequence is pulled back through the actual native
integer projection. Exactness follows from its finite locally free quotient
and genuine local splittings; no flatness of that projection is assumed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients


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

/-- The original integer Euler maps pulled back along the actual native integer projection. -/
def rawSequence : ShortComplex (nativeLineFunctor.obj X).obj.Modules :=
  (Euler.sequence integerRing).map (Scheme.Modules.pullback (nativeIntegerProjection X))

/-- Pullback exactness is justified by the actual vector-bundle quotient. -/
lemma rawSequence_shortExact : (rawSequence X).ShortExact :=
  shortExact_pullback (nativeIntegerProjection X) (Euler.sequence_shortExact integerRing)

instance integerLineTensorMap_isIso (M : (twoChartLine integerRing).Modules) :
    IsIso (modulePullbackTensorMap (nativeIntegerProjection X)
      (tautologicalLine integerRing) M) := by
  apply modulePullbackTensorMap_isIso_of_trivializingCover (nativeIntegerProjection X)
    (fun _ : Bool => Spec (CommRingCat.of (Polynomial integerRing)))
    (lineChart integerRing) (lineChart_cover integerRing) (tautologicalLine integerRing) M
    (lineChartIso integerRing)

/-- The square endpoint uses the original invertible pullback-tensor mate. -/
def squareIso : (rawSequence X).X₁ ≅
    (moduleTensorLeftFunctor (nativeLineFunctor.obj X).obj (nativeTautologicalLine X)).obj
      (nativeTautologicalLine X) :=
  asIso (modulePullbackTensorMap (nativeIntegerProjection X)
    (tautologicalLine integerRing) (tautologicalLine integerRing))

/-- The middle endpoint retains the original ordered integer middle and biproduct comparison. -/
def middleIso : (rawSequence X).X₂ ≅
    nativeTautologicalLine X ⊞ nativeTautologicalLine X := by
  let F := Scheme.Modules.pullback (nativeIntegerProjection X)
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts _
  exact F.mapIso (Euler.middleIso integerRing) ≪≫
    F.mapBiprod (tautologicalLine integerRing) (tautologicalLine integerRing)

/-- The quotient endpoint uses the actual original pullback unit. -/
def unitIso : (rawSequence X).X₃ ≅
    SheafOfModules.unit (nativeLineFunctor.obj X).obj.ringCatSheaf :=
  pullbackUnitIso (nativeIntegerProjection X)

/-- Actual normalized native Euler maps, in square/middle/unit order. -/
def sequence : ShortComplex (nativeLineFunctor.obj X).obj.Modules :=
  ShortComplex.mk
    ((squareIso X).inv ≫ (rawSequence X).f ≫ (middleIso X).hom)
    ((middleIso X).inv ≫ (rawSequence X).g ≫ (unitIso X).hom) (by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, (rawSequence X).zero_assoc,
        zero_comp, comp_zero])

/-- The normalization is the original three endpoint comparisons. -/
def sequenceIso : rawSequence X ≅ sequence X :=
  ShortComplex.isoMk (squareIso X) (middleIso X) (unitIso X)
    (by simp [sequence]) (by simp [sequence])

/-- The original normalized native Euler sequence is short exact for every native base. -/
lemma sequence_shortExact : (sequence X).ShortExact :=
  ShortComplex.shortExact_of_iso (sequenceIso X) (rawSequence_shortExact X)

instance rawSquare_finiteLocallyFree : IsFiniteLocallyFree (nativeLineFunctor.obj X).obj
    (rawSequence X).X₁ := by
  change IsFiniteLocallyFree (nativeLineFunctor.obj X).obj
    ((Scheme.Modules.pullback (nativeIntegerProjection X)).obj (Euler.sequence integerRing).X₁)
  infer_instance

instance rawMiddle_finiteLocallyFree : IsFiniteLocallyFree (nativeLineFunctor.obj X).obj
    (rawSequence X).X₂ := by
  change IsFiniteLocallyFree (nativeLineFunctor.obj X).obj
    ((Scheme.Modules.pullback (nativeIntegerProjection X)).obj (Euler.sequence integerRing).X₂)
  infer_instance

instance rawUnit_finiteLocallyFree : IsFiniteLocallyFree (nativeLineFunctor.obj X).obj
    (rawSequence X).X₃ := by
  change IsFiniteLocallyFree (nativeLineFunctor.obj X).obj
    ((Scheme.Modules.pullback (nativeIntegerProjection X)).obj (Euler.sequence integerRing).X₃)
  infer_instance

instance square_finiteLocallyFree : IsFiniteLocallyFree (nativeLineFunctor.obj X).obj
    (sequence X).X₁ :=
  finiteLocallyFree_of_iso (squareIso X)

instance middle_finiteLocallyFree : IsFiniteLocallyFree (nativeLineFunctor.obj X).obj
    (sequence X).X₂ :=
  finiteLocallyFree_of_iso (middleIso X)

instance unit_finiteLocallyFree : IsFiniteLocallyFree (nativeLineFunctor.obj X).obj
    (sequence X).X₃ :=
  finiteLocallyFree_of_iso (unitIso X)

/-- Arbitrary original coefficient terms preserve the actual Euler sequence by local splitting. -/
theorem coefficient_shortExact (M : (nativeLineFunctor.obj X).obj.Modules) :
    ((sequence X).map (moduleTensorByLineRight M)).ShortExact :=
  shortExact_tensorRight_of_finiteLocallyFree_quotient M (sequence_shortExact X)

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeEuler
