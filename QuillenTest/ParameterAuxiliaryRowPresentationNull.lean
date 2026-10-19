/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryRowPresentationNull

/-! # Original auxiliary null on the genuine row telescope -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open scoped Topology unitInterval
universe u
namespace QuillenTest.ParameterAuxiliaryRowPresentationNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
  (X : Scheme.{u}ᵒᵖ)

/-- The exact two original input maps form the source of the descended null. -/
theorem original_composite (n : ℕ) (x : (fiberPresentation f T X).space n) :
    (presentationNull f T X).level n (0, x) =
      (presentationRestriction f T X).map n ((presentationEnlargement f T X).map n x) :=
  (presentationNull f T X).at_zero n x

/-- The prescribed endpoint is literally zero in the actual open presentation. -/
theorem original_zero (n : ℕ) (x : (fiberPresentation f T X).space n) :
    (presentationNull f T X).level n (1, x) = (openPresentation f T X).point n :=
  (presentationNull f T X).at_one n x

/-- The entire original current null is retained at each independent time. -/
theorem same_time_comparison (n : ℕ) (r : unitInterval)
    (x : ((SchemeNaturalSeed.currentTelescope (fiberAction f T)).obj X).space n) :
    (openPresentationComparison f T X).map n
        (((currentNull f T).homotopy X).level n (r, x)) =
      (presentationNull f T X).level n
        (r, (fiberPresentationComparison f T X).map n x) :=
  presentationNull_comparison f T X n r x

end QuillenTest.ParameterAuxiliaryRowPresentationNull
