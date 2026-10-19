/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFineConnectingComparison

/-!+# Recovering the intrinsic boundary through the actual comparison

The inverse comparison recovers the current boundary in every signed degree.
The two explicit degree specializations retain the zero-degree crossing.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ParameterFullCurrentNull
open Quillen.PerfectComplexes.ParameterLaurentTrack
open Quillen.KTheory.Bass.SchemeNaturalSeed

universe u

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    currentConnecting f a d =
      (currentFineOpenComparison f a (d + 1)).hom ≫
        boundedFlatCoefficientFineLocalizationConnecting f a d ≫
          (currentFineSupportComparison f a d).inv := by
  apply (cancel_mono (currentFineSupportComparison f a d).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    current_fine_connecting f a d

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    stableHomotopyGroup ((currentTelescope (ambientTrack P.left)).obj (specUnder.obj a)) 1 ⟶
      stableHomotopyGroup ((currentTelescope (supportedTrack f.left)).obj (specUnder.obj a)) 0 :=
  currentConnecting f a 0

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    stableHomotopyGroup ((currentTelescope (ambientTrack P.left)).obj (specUnder.obj a)) 0 ⟶
      stableHomotopyGroup ((currentTelescope (supportedTrack f.left)).obj (specUnder.obj a)) (-1) :=
  eqToHom (congrArg
    (fun d => stableHomotopyGroup
      ((currentTelescope (ambientTrack P.left)).obj (specUnder.obj a)) d)
    (show (0 : ℤ) = -1 + 1 by decide)) ≫ currentConnecting f a (-1)
