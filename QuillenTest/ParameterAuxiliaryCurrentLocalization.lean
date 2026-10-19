/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryCurrentLocalization

/-! # Original auxiliary support, G7 null time, signed degrees and the actual projection -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open GlobalAuxiliaryParameterCoefficient ParameterAuxiliaryCurrentFiber
universe u

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (T : Q.Opens) [CompactSpace T] (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (currentLift f T (op integerBase))) :=
  currentLift_integer_signed_isIso f T d

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    currentLift f T X ≫ homotopyFiberProjection ((currentRestriction f T).app X) =
      (currentEnlargement f T).app X := currentLift_projection f T X

example {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (currentLift f.left T (specUnder.obj a)) :=
  currentLift_spec_isStableEquivalence f T a

example {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (s : unitInterval)
    (x : ((SchemeNaturalSeed.iteratedTelescope (fiberAction f.left T)).obj
      (specUnder.obj a)).space n) :
    ((openTelescopeComparison f T).app a).map n
      (((iteratedNull f.left T).homotopy (specUnder.obj a)).level n (s, x)) =
      ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a).level n
        (s, ((fiberTelescopeComparison f T).app a).map n x) :=
  telescope_fullNull_square f T a n s x
