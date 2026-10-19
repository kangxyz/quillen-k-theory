/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportNull
public import Quillen.KTheory.Bass.DiagramRowNull
public import Quillen.KTheory.Bass.ModelDiagramRowRefinement
public import Quillen.Waldhausen.SConstruction.Iterated.RowSwapTransformation

/-! # The original auxiliary supported null preserves every actual row interchange

The null is the prescribed reversed selected-zero transformation. No endpoint-only square
replaces its whole time parameter. Finite Bass stages use the original iterated null.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open ModelDiagramRowInterchange GeometricSeedCospan
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The actual weak zero transformation commutes with the original last-row transpose. -/
theorem fullNull_initial_row (X : Scheme.{u}ᵒᵖ) (k : ℕ) (r : unitInterval)
    (x : (prespectrum ((fiber f T).obj X)).space (k + 3)) :
    initial (openModel f T) X k (((fullNull f T).homotopy X).level (k + 3) (r, x)) =
      ((fullNull f T).homotopy X).level (k + 3)
        (r, initial (fiber f T) X k x) := by
  rw [fullNull_level, fullNull_level]
  exact stageTransformationTopHomotopy_rowSwap k
    (zeroToFull f T X) (zeroToFull_weak f T X) (unitInterval.symm r) x

/-- Every original finite auxiliary null retains its exact time and computed stage row action. -/
theorem fullNull_stage_row (i : ℕ) (X : Scheme.{u}ᵒᵖ) (k : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (fiber f T ⋙ prespectrumFunctor)).obj X).space (k + 3)) :
    stage squareFunctor (openModel f T) i X k
        (((strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X).level
          (k + 3) (r, x)) =
      ((strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X).level
        (k + 3) (r, stage squareFunctor (fiber f T) i X k x) :=
  DiagramRowInterchange.iterate_null squareFunctor
    (F := fiber f T ⋙ prespectrumFunctor) (G := openModel f T ⋙ prespectrumFunctor)
    (initial (fiber f T)) (initial_point (fiber f T)) (initial_naturality (fiber f T))
    (initial (openModel f T)) (initial_point (openModel f T))
    (initial_naturality (openModel f T)) (fullNull f T) (fullNull_initial_row f T) i X k r x

/-- Every original moving cone preserves null time independently of both quotient heights. -/
theorem fullNull_cone_row (i : ℕ) (X : Scheme.{u}ᵒᵖ) (k : ℕ) (r : unitInterval)
    (x : (ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).space (k + 3)) :
    cone squareFunctor i (openModel f T) X k
        ((diagramSquareMapHomotopy
          (η := (strictDiagramIterate squareFunctor i).map
              (Functor.whiskerRight (enlargement f T) prespectrumFunctor) ≫
            (strictDiagramIterate squareFunctor i).map
              (Functor.whiskerRight (restriction f T) prespectrumFunctor))
          (θ := diagramZeroMap
            ((strictDiagramIterate squareFunctor i).obj (fiber f T ⋙ prespectrumFunctor))
            ((strictDiagramIterate squareFunctor i).obj (openModel f T ⋙ prespectrumFunctor)))
          (strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy
          (strictDiagramIterateNull squareFunctor (fullNull f T) i).naturality
          (squareFunctor.obj X)).cone.level (k + 3) (r, x)) =
      (diagramSquareMapHomotopy
          (η := (strictDiagramIterate squareFunctor i).map
              (Functor.whiskerRight (enlargement f T) prespectrumFunctor) ≫
            (strictDiagramIterate squareFunctor i).map
              (Functor.whiskerRight (restriction f T) prespectrumFunctor))
          (θ := diagramZeroMap
            ((strictDiagramIterate squareFunctor i).obj (fiber f T ⋙ prespectrumFunctor))
            ((strictDiagramIterate squareFunctor i).obj (openModel f T ⋙ prespectrumFunctor)))
        (strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy
        (strictDiagramIterateNull squareFunctor (fullNull f T) i).naturality
        (squareFunctor.obj X)).cone.level (k + 3)
        (r, cone squareFunctor i (fiber f T) X k x) :=
  DiagramRowInterchange.cone_iterate_null squareFunctor
    (F := fiber f T ⋙ prespectrumFunctor) (G := openModel f T ⋙ prespectrumFunctor)
    (initial (fiber f T)) (initial_point (fiber f T)) (initial_naturality (fiber f T))
    (initial (openModel f T)) (initial_point (openModel f T))
    (initial_naturality (openModel f T)) (fullNull f T) (fullNull_initial_row f T) i X k r x

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
