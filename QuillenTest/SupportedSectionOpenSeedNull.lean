/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionOpenSeedNull

/-!
# Original supported seed and relative-open null consumers

The original Laurent action is tested at degree zero with both times. The seed comparison
retains its independent null and output-loop coordinates. Time slices are the original
reversed null values, including their actual zero-map endpoint.
-/
@[expose] public section

open Quillen.PerfectComplexes


open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace QuillenTest.SupportedSectionOpenSeedNull

open Quillen
open PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original degree-zero Laurent loop commutes with the same whole null track. -/
theorem originalDegreeZeroLaurentSquare (a : Under R) (r t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space 0) :
    (boundedFlatAffineSupportedSectionOpenNullHomotopy
        (inclusion j ((laurentUnderFunctor R).obj a))).level 0
        (r, (boundedFlatAffineSupportedDiagramLaurentHomotopy j a).level 0 (t, x)) =
      (boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level 0
        (t, (boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)).level 0
          (r, x)) :=
  boundedFlatAffineSupportedSectionOpenNullHomotopy_laurent_apply j a 0 r t x

/-- The original null time and the seed's output-loop time remain independent. -/
theorem originalSeedNullLoop (a : Under R) (n : ℕ) (r t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
        ((boundedFlatAffineSupportedSectionOpenBassNullHomotopy j a).level n
          (r, (boundedFlatAffineSupportedSectionBassSeedMap j a).map n x)) t =
      Path.toContinuousMap
        ((boundedFlatAffineSectionOpenBassSeedMap j a).map n
          ((boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)).level n
            (r, x))) t :=
  boundedFlatAffineSupportedSectionOpenBassNullHomotopy_seed_apply j a n r t x

/-- A coefficient-natural time slice has the literal original null-cylinder value. -/
theorem originalTimeSliceValue (a : Under R) (n : ℕ) (r : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineSupportedSectionOpenNullTimeSlice j r).app a).map n x =
      (boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)).level n (r, x) := rfl

/-- The original final null time is the actual coarse prespectrum basepoint. -/
theorem originalTimeSliceZeroEndpoint (a : Under R) (n : ℕ)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineSupportedSectionOpenNullTimeSlice j 1).app a).map n x =
      ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).point n :=
  (boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)).at_one n x

end QuillenTest.SupportedSectionOpenSeedNull
