/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.UnitFiniteLocallyFree


public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.StrictProperty


public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.EulerSequence

/-! # The literal Euler endpoint exact functors on strict-perfect coefficients -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.Euler
open FlasqueCoefficients
variable (R : CommRingCat.{u})

/-- The actual square of the negative line is trivialized by both original line charts. -/
def squareChartIso (b : Bool) :
    (sequence R).X₁.restrict (lineChart R b) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Polynomial R))).ringCatSheaf :=
  tensorPairingTrivialization (lineChart R b) (tautologicalLine R) (tautologicalLine R)
    (lineChartIso R b) (lineChartIso R b)

instance square_finiteLocallyFree : IsFiniteLocallyFree (twoChartLine R) (sequence R).X₁ := by
  apply finiteLocallyFree_of_affineCharts (sequence R).X₁
    (fun _ : Bool => CommRingCat.of (Polynomial R)) (lineChart R) (lineChart_cover R)
  intro b
  let := unit_finiteLocallyFree (Spec (CommRingCat.of (Polynomial R)))
  exact finiteLocallyFree_of_iso (squareChartIso R b).symm

instance unitEndpoint_finiteLocallyFree : IsFiniteLocallyFree (twoChartLine R) (sequence R).X₃ :=
  unit_finiteLocallyFree _

instance middle_finiteLocallyFree : IsFiniteLocallyFree (twoChartLine R) (sequence R).X₂ :=
  finiteLocallyFree_of_shortExact (sequence_shortExact R)

/-- An actual chart-trivialized fixed line preserves strict-perfect coefficient complexes. -/
lemma tensor_strictPerfect_of_charts (M : (twoChartLine R).Modules)
    (e : ∀ b, M.restrict (lineChart R b) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Polynomial R))).ringCatSheaf)
    (K : CochainComplex (twoChartLine R).Modules ℤ) (hK : strictPerfect (twoChartLine R) K) :
    strictPerfect (twoChartLine R) ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft M).obj K)
      := by
  obtain ⟨⟨a, b, hab⟩, hf⟩ := hK
  refine ⟨⟨a, b, fun n hn => (moduleTensorLeftFunctor (twoChartLine R) M).map_isZero
    (hab n hn)⟩, fun n => ?_⟩
  apply finiteLocallyFree_of_affineCharts _
    (fun _ : Bool => CommRingCat.of (Polynomial R)) (lineChart R) (lineChart_cover R)
  intro c
  let : IsFiniteLocallyFree (twoChartLine R) (K.X n) := hf n
  exact finiteLocallyFree_of_iso
    ((tensorByLineModuleChartIso (lineChart R c) M (e c)).app (K.X n)).symm

lemma squareEndpoint_strictPerfect (A : StrictPerfect (Spec R)) :
    strictPerfect (twoChartLine R) ((endpointComplex R (sequence R).X₁).obj A) :=
  tensor_strictPerfect_of_charts R _ (squareChartIso R) _
    (strictPerfect_pullback (projection R) A.property)

/-- The original left unitor, with no choice of derived representative. -/
def unitEndpointIso : endpointComplex R (sequence R).X₃ ≅
    (strictPerfect (Spec R)).ι ⋙ AlgebraicGeometry.Scheme.Modules.Complex.pullback (projection R) :=
  Functor.isoWhiskerLeft ((strictPerfect (Spec R)).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.pullback (projection R))
    (NatIso.mapHomologicalComplex
      (SheafOfModulesOfCommRing.tensorLeftUnitIso (twoChartLine R).sheaf) (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ (.up ℤ)) ≪≫ Functor.rightUnitor _

lemma unitEndpoint_strictPerfect (A : StrictPerfect (Spec R)) :
    strictPerfect (twoChartLine R) ((endpointComplex R (sequence R).X₃).obj A) :=
  strictPerfect_of_iso ((unitEndpointIso R).app A).symm
    (strictPerfect_pullback (projection R) A.property)

lemma middleEndpoint_strictPerfect (A : StrictPerfect (Spec R)) :
    strictPerfect (twoChartLine R) ((endpointComplex R (sequence R).X₂).obj A) :=
  strictPerfect_of_shortExact (coefficientSequence_shortExact R A)
    (squareEndpoint_strictPerfect R A) (unitEndpoint_strictPerfect R A)

/-- A fixed endpoint with its proved strict-perfect values, keeping the raw original complex. -/
def endpointBounded (M : (twoChartLine R).Modules)
    (hM : ∀ A, strictPerfect (twoChartLine R) ((endpointComplex R M).obj A)) :
    StrictPerfect (Spec R) ⥤ BoundedBelow.Obj (twoChartLine R) :=
  ObjectProperty.lift _ (endpointComplex R M)
    (fun A => boundedBelow_of_strictPerfect (hM A))

instance endpointBounded_additive (M : (twoChartLine R).Modules)
    (hM : ∀ A, strictPerfect (twoChartLine R) ((endpointComplex R M).obj A)) :
    (endpointBounded R M hM).Additive where
  map_add := by
    intro A B f g
    apply ObjectProperty.hom_ext
    exact Functor.map_add (endpointComplex R M)

/-- Inherited conflations are preserved by the actual finite-locally-free fixed endpoint tensor. -/
def endpointBoundedExactFunctor (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M]
    (hM : ∀ A, strictPerfect (twoChartLine R) ((endpointComplex R M).obj A)) :
    CategoryTheory.ExactCategory.ExactFunctor (strictExactStructure (Spec R))
      (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
        (CategoryTheory.ExactCategory.abelianExactStructure
          (CochainComplex (twoChartLine R).Modules ℤ))
        (BoundedBelow.objects (twoChartLine R))) where
  toFunctor := endpointBounded R M hM
  map_conflation S hS := by
    have hp := (strictExactPullback (projection R)).map_conflation S hS
    change (S.map (strictPullback (projection R)) |>.map
      (strictPerfect (twoChartLine R)).ι).ShortExact at hp
    exact hp.map_of_exact (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft M)

lemma endpointBounded_exact (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M]
    (hM : ∀ A, strictPerfect (twoChartLine R) ((endpointComplex R M).obj A)) :
    Waldhausen.IsExact (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
      (BoundedBelow.waldhausen (twoChartLine R)).cof
      (BoundedBelow.waldhausen (twoChartLine R)).weq (endpointBounded R M hM) where
  zero h := (endpointBounded R M hM).map_isZero h
  cofibration f hf := (endpointBoundedExactFunctor R M hM).map_inflation f hf
  weak {A B} f hf := by
    let : QuasiIso f.hom := hf
    let : QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.pullback (projection R)).map f.hom) :=
      quasiIso_pullback_of_strictPerfect (projection R) A.property B.property f.hom
    change QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft M).map
      ((AlgebraicGeometry.Scheme.Modules.Complex.pullback (projection R)).map f.hom))
    exact AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft_quasiIso M _
  pushout hi h := (endpointBoundedExactFunctor R M hM).map_isPushout hi h

/-- Actual Godement totalization followed by the original ordinary projection. -/
def projectedEndpoint (M : (twoChartLine R).Modules)
    (hM : ∀ A, strictPerfect (twoChartLine R) ((endpointComplex R M).obj A)) :
    StrictPerfect (Spec R) ⥤ FlasqueBoundedBelow.Obj (Spec R) :=
  endpointBounded R M hM ⋙ FlasqueBoundedBelow.total (twoChartLine R) ⋙ G0 R

lemma projectedEndpoint_exact (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M]
    (hM : ∀ A, strictPerfect (twoChartLine R) ((endpointComplex R M).obj A)) :
    Waldhausen.IsExact (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
      (FlasqueBoundedBelow.waldhausen (Spec R)).cof
      (FlasqueBoundedBelow.waldhausen (Spec R)).weq (projectedEndpoint R M hM) :=
  (endpointBounded_exact R M hM).comp
    ((FlasqueBoundedBelow.total_exact (twoChartLine R)).comp (G0_exact R))

/-- The original L² coefficient after actual totalization and projection. -/
def E2 := projectedEndpoint R (sequence R).X₁ (squareEndpoint_strictPerfect R)

/-- The original middle coefficient after actual totalization and projection. -/
def E1 := projectedEndpoint R (sequence R).X₂ (middleEndpoint_strictPerfect R)

/-- The determinant-normalized structure coefficient after actual totalization and projection. -/
def E0 := projectedEndpoint R (sequence R).X₃ (unitEndpoint_strictPerfect R)

lemma E2_exact : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (E2 R) := projectedEndpoint_exact R _ _

lemma E1_exact : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (E1 R) := projectedEndpoint_exact R _ _

lemma E0_exact : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (E0 R) := projectedEndpoint_exact R _ _

end Quillen.PerfectComplexes.ProjectiveLine.Euler
