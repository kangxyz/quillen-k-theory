/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryCurrentFiber

/-! # Actual auxiliary-supported four-model comparison and unchanged null cylinders -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open Quillen.PerfectComplexes.ParameterAuxiliaryCurrentFiber
open SchemeNaturalSeed
universe u
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

example (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (currentLift f T X) ↔ IsStableEquivalence (iteratedLift f T X) :=
  current_iterated_lift_stable_iff f T X

example (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s t : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (fiber f T ⋙ prespectrumFunctor)).obj X).space n) :
    ((ParameterAuxiliarySupport.currentNull f T).homotopy X).level n
      (s, Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj
          (fiber f T ⋙ prespectrumFunctor)).obj X)
        (fun j => (currentTransition (fiberAction f T) j).app X) n i (t, x)) =
      Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj
          (openModel f T ⋙ prespectrumFunctor)).obj X)
        (fun j => (currentTransition (openAction f T) j).app X) n i
        (t, ((strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X).level n
          (s, x)) := rfl

example (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s t : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (fiber f T ⋙ prespectrumFunctor)).obj X).space n) :
    ((iteratedNull f T).homotopy X).level n
      (s, Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj
          (fiber f T ⋙ prespectrumFunctor)).obj X)
        (fun j => (strictDiagramTransition squareFunctor (seed (fiberAction f T)) j).app X)
        n i (t, x)) =
      Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj
          (openModel f T ⋙ prespectrumFunctor)).obj X)
        (fun j => (strictDiagramTransition squareFunctor (seed (openAction f T)) j).app X)
        n i (t, ((strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X).level n
          (s, x)) := rfl
