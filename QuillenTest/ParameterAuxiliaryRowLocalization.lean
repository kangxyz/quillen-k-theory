/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryRowLocalization

/-! # Same-null row localization with arbitrary signed degree and original support -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum Quillen.PerfectComplexes
open GlobalSectionChangeIndex.ParameterAuxiliarySupport
open ParameterAuxiliaryRowLocalization ParameterAuxiliaryCurrentFiber
universe u

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (T : Q.Opens) [CompactSpace T] (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (presentationLift f T (op integerBase))) :=
  presentationLift_integer_signed_isIso f T d

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    presentationLift f T X ≫ homotopyFiberProjection (presentationRestriction f T X) =
      presentationEnlargement f T X := presentationLift_projection f T X

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (t : unitInterval)
    (x : ((Quillen.KTheory.Bass.SchemeNaturalSeed.currentTelescope
      (fiberAction f T)).obj X).space n) :
    (openPresentationComparison f T X).map n
        (((currentNull f T).homotopy X).level n (t, x)) =
      (presentationNull f T X).level n
        (t, (fiberPresentationComparison f T X).map n x) :=
  presentationNull_comparison f T X n t x
