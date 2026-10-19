/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowPresentationNull

/-! # Original auxiliary null on the genuine row telescope -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes.ParameterLaurentTrack
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.KTheory.Bass.GeometricSeedCospan
open scoped Topology unitInterval
universe u
namespace QuillenTest.ParameterAuxiliaryNormalizedRowNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
  (X : Scheme.{u}ᵒᵖ)

/-- The exact two original input maps form the source of the descended null. -/
theorem original_composite (n : ℕ) (x : (normalizedFiberPresentation f T X).space n) :
    (normalizedPresentationNull f T X).level n (0, x) =
      (normalizedPresentationRestriction f T X).map n
    ((normalizedPresentationEnlargement f T X).map n x) :=
  (normalizedPresentationNull f T X).at_zero n x

/-- The prescribed endpoint is literally zero in the actual open presentation. -/
theorem original_zero (n : ℕ) (x : (normalizedFiberPresentation f T X).space n) :
    (normalizedPresentationNull f T X).level n (1, x) =
    (normalizedOpenPresentation f T X).point n :=
  (normalizedPresentationNull f T X).at_one n x

/-- The entire original current null is retained at each independent time. -/
theorem same_time_comparison (n : ℕ) (r : unitInterval)
    (x : ((SchemeNaturalSeed.currentTelescope (fiberAction f T)).obj X).space n) :
    (normalizedOpenPresentationComparison f T X).map n
        (((currentNull f T).homotopy X).level n (r, x)) =
      (normalizedPresentationNull f T X).level n
        (r, (normalizedFiberPresentationComparison f T X).map n x) :=
  normalizedPresentationNull_comparison f T X n r x

/-- Normalization and original null remain independently quantified. -/
theorem independent_normalization_null_times (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (r s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (fiber f T ⋙ prespectrumFunctor)).obj X).space n) :
    (fullTargetNull f T i X).level n
        (r, (SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy (fiber f T)
          (supportedUnit (unionOpen f T).ι) (supportedUnit_naturality (unionOpen f T).ι)
          i X).level n (s, x)) =
      (SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy (openModel f T)
          (supportedUnit (inverseOpen f T).ι) (supportedUnit_naturality (inverseOpen f T).ι)
          i X).level n
        (s, ((strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X).level n
          (r, x)) :=
  fullNull_normalizedBoundaryHomotopy f T i X n r s x

end QuillenTest.ParameterAuxiliaryNormalizedRowNull
