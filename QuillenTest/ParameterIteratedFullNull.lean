/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterIteratedFullNull

/-! # The actual original null retains its independent telescope height -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.ParameterLaurentTrack
open Quillen.PerfectComplexes.ParameterFullCurrentNull
open SchemeNaturalSeed
universe u
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

example (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (r t : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterModels.supported f ⋙
        Quillen.Waldhausen.IteratedS.prespectrumFunctor)).obj X).space n) :
    ((iteratedNull f).homotopy X).level n
      (r, Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj
          (ParameterModels.supported f ⋙ Quillen.Waldhausen.IteratedS.prespectrumFunctor)).obj X)
        (fun j => (strictDiagramTransition squareFunctor (SchemeNaturalSeed.seed
      (supportedTrack f)) j).app X) n i (t, x)) =
      Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj
          (ParameterModels.ambient P ⋙ Quillen.Waldhausen.IteratedS.prespectrumFunctor)).obj X)
        (fun j => (strictDiagramTransition squareFunctor (SchemeNaturalSeed.seed
      (ambientTrack P)) j).app X) n i
        (t, ((strictDiagramIterateNull squareFunctor
          (fullNull f) i).homotopy X).level n (r, x)) := rfl
