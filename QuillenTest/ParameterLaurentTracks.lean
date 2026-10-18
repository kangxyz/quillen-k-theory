/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentNull
import Quillen.KTheory.Bass.SchemeNaturalSeed

/-! # Original parameter units, seeds and independent localization-null clocks -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.ParameterLaurentUnit
open Quillen.PerfectComplexes.ParameterLaurentTrack
open Quillen.PerfectComplexes.ParameterLaurentNull
open NaturalTrack SchemeNaturalSeed
universe u
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

example : seed (supportedTrack f) ≫
    (strictDiagramFunctor squareFunctor).map
      (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) =
    Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor ≫
      seed (ambientTrack Q) :=
  seed_square _ _ _ (forget_equivariant f)

example : seed (ambientTrack Q) ≫
    (strictDiagramFunctor squareFunctor).map
      (Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor) =
    Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor ≫
      seed (openTrack f) :=
  seed_square _ _ _ (changeWeak_equivariant f)

example : seed (openTrack f) ≫
    (strictDiagramFunctor squareFunctor).map
      (Functor.whiskerRight (ParameterModels.openRestriction f) prespectrumFunctor) =
    Functor.whiskerRight (ParameterModels.openRestriction f) prespectrumFunctor ≫
      seed (ambientTrack P) :=
  seed_square _ _ _ (openRestriction_equivariant f)

example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (s t : unitInterval)
    (x : (prespectrum ((ParameterModels.supported f).obj X)).space n) :
    ((ParameterModels.supportedOpenNull f).homotopy (laurent.op.obj X)).level n
      (s, ((supportedTrack f).homotopy X).level n (t, x)) =
    ((openTrack f).homotopy X).level n
      (t, ((ParameterModels.supportedOpenNull f).homotopy X).level n (s, x)) :=
  supportedOpenNull_laurentInterchange f X n s t x

#print axioms projectedLaurentScalar_map
#print axioms projectedLaurentScalar_factor
#print axioms ambientUnit_factor
#print axioms ofModelUnits_equivariant
#print axioms supportedUnit_naturality
#print axioms forget_equivariant
#print axioms openRestriction_equivariant
#print axioms supportedOpenNull_laurentInterchange
#print axioms fullOpenNull_laurentInterchange
