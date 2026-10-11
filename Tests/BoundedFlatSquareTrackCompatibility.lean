/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SquareTrackCompatibility
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSpanMap

/-! # Original polynomial and signed Laurent square tracks -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PerfectComplexes
open Quillen.Scheme.PolynomialLaurent Quillen.PolynomialBaseChange
universe u
namespace Quillen.Tests.BoundedFlatSquareTrackCompatibility
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The entire original polynomial coefficient square retains both composition tracks. -/
theorem original_polynomial (n : ℕ) :
    (boundedFlatPolynomialSquareHomotopy f).level n =
      ((boundedFlatPerfectPrespectrumCompHomotopy (Spec.map (polynomialMap f))
        (polynomialProjection R)).symm.trans
        ((boundedFlatPerfectPrespectrumCompHomotopy (polynomialProjection S) (Spec.map f)).cast
          (congrArg boundedFlatPerfectPrespectrumMap (polynomialMap_projection f)).symm
          rfl)).level n :=
  boundedFlatPerfectPrespectrumSquareHomotopy_level _ _ _ _ _ n

/-- The positive Laurent square retains its own original geometric maps and whole track. -/
theorem original_plus (n : ℕ) :
    (boundedFlatPlusSquareHomotopy f).level n =
      ((boundedFlatPerfectPrespectrumCompHomotopy (Spec.map (laurentMap f))
        (laurentPlus R)).symm.trans
        ((boundedFlatPerfectPrespectrumCompHomotopy (laurentPlus S)
          (Spec.map (polynomialMap f))).cast
          (congrArg boundedFlatPerfectPrespectrumMap (laurentMap_plus f)).symm rfl)).level n :=
  boundedFlatPerfectPrespectrumSquareHomotopy_level _ _ _ _ _ n

/-- The inverse-coordinate square uses the distinct negative Laurent leg. -/
theorem original_minus (n : ℕ) :
    (boundedFlatMinusSquareHomotopy f).level n =
      ((boundedFlatPerfectPrespectrumCompHomotopy (Spec.map (laurentMap f))
        (laurentMinus R)).symm.trans
        ((boundedFlatPerfectPrespectrumCompHomotopy (laurentMinus S)
          (Spec.map (polynomialMap f))).cast
          (congrArg boundedFlatPerfectPrespectrumMap (laurentMap_minus f)).symm rfl)).level n :=
  boundedFlatPerfectPrespectrumSquareHomotopy_level _ _ _ _ _ n

end Quillen.Tests.BoundedFlatSquareTrackCompatibility
