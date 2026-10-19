/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportNull
import Quillen.KTheory.Bass.SchemeNaturalSeed

/-! # Actual auxiliary-support seeds and the original two-time null -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open Quillen.PerfectComplexes.ParameterLaurentTrack
open NaturalTrack SchemeNaturalSeed
universe u
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

example : seed (supportedTrack (unionOpen f T).ι) ≫
    (strictDiagramFunctor squareFunctor).map
      (Functor.whiskerRight (enlargement f T) prespectrumFunctor) =
    Functor.whiskerRight (enlargement f T) prespectrumFunctor ≫ seed (supportedTrack T.ι) :=
  seed_square _ _ _ (enlargement_equivariant f T)

example : seed (supportedTrack T.ι) ≫
    (strictDiagramFunctor squareFunctor).map
      (Functor.whiskerRight (restriction f T) prespectrumFunctor) =
    Functor.whiskerRight (restriction f T) prespectrumFunctor ≫
      seed (supportedTrack (inverseOpen f T).ι) :=
  seed_square _ _ _ (restriction_equivariant f T)

example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (s t : unitInterval)
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    ((fullNull f T).homotopy (laurent.op.obj X)).level n
      (s, ((supportedTrack (unionOpen f T).ι).homotopy X).level n (t, x)) =
    ((supportedTrack (inverseOpen f T).ι).homotopy X).level n
      (t, ((fullNull f T).homotopy X).level n (s, x)) :=
  fullNull_laurentInterchange f T X n s t x
