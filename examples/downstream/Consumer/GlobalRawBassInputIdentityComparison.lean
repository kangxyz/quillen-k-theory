/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityComparison

/-! An independent consumer of the whole original global raw comparison identity square. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalRawBassInputIdentityComparison

/-- No identity square or overlap filler is supplied by this independent downstream client. -/
def originalComparisonIdentity (X : Scheme.{u}) :
    (inputComparisonHomotopy (𝟙 X)).Square (coneSquareIdentityTrack (comparison X))
      (Homotopy.precomp (comparison X) (InputIdentity.laurentHomotopy X))
      ((InputIdentity.spanHomotopy X).postcomp (comparison X)) :=
  InputIdentity.comparisonSquare X

/-- The complete original Laurent-unit edge is recovered at every original span point. -/
theorem originalLaurentEdge (X : Scheme.{u}) (n : ℕ) (r : unitInterval)
    (q : (span X).space n) :
    (originalComparisonIdentity X).level n (r, (0, q)) =
      (InputIdentity.laurentHomotopy X).level n (r, (comparison X).map n q) :=
  (originalComparisonIdentity X).left n r q

end Consumer.GlobalRawBassInputIdentityComparison
