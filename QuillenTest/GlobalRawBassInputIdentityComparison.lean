/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityComparison

/-! The original whole comparison square, actual carrier cube, and independent structure time. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.GlobalRawBassInputIdentityComparison
variable (X : Scheme.{u})

/-- Every original span point retains the complete raw input comparison at the initial face. -/
theorem whole_initial (n : ℕ) (s : unitInterval) (q : (span X).space n) :
    (InputIdentity.comparisonSquare X).level n (0, (s, q)) =
      (inputComparisonHomotopy (𝟙 X)).level n (s, q) :=
  (InputIdentity.comparisonSquare X).at_zero n s q

/-- Both whole moving sides keep the actual Laurent identity and the original unpaused span map. -/
theorem whole_sides (n : ℕ) (r : unitInterval) (q : (span X).space n) :
    (InputIdentity.comparisonSquare X).level n (r, (0, q)) =
      (InputIdentity.laurentHomotopy X).level n (r, (comparison X).map n q) ∧
    (InputIdentity.comparisonSquare X).level n (r, (1, q)) =
      (comparison X).map n ((InputIdentity.spanHomotopy X).level n (r, q)) :=
  ⟨(InputIdentity.comparisonSquare X).left n r q,
    (InputIdentity.comparisonSquare X).right n r q⟩

/-- The whole comparison square retains a structure time independent of both square coordinates. -/
theorem whole_structure (n : ℕ) (r s z : unitInterval) (q : (span X).space n) :
    (InputIdentity.comparisonSquare X).level (n + 1)
      (r, (s, (span X).structureMap n q z)) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X))).structureMap n
      ((InputIdentity.comparisonSquare X).level n (r, (s, q))) z :=
  (InputIdentity.comparisonSquare X).comm n r s q z

/-- Every actual overlap point comes from the same carrier cube with all three times independent. -/
theorem original_overlap (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    (InputIdentity.comparisonSquare X).level n (r, (s,
      HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X)) n (t, x))) =
      CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X)
        (InputIdentityCarrierCube.carrierCube X) n (![r, s, t], x) :=
  InputIdentity.comparisonSquare_cylinder X n r s t x

/-- The cube keeps every point of each prescribed actual carrier face, including its endpoints. -/
theorem all_six_faces (a : Fin 3 × Bool) (x : Quillen.SimplexCubeExtension.Cube)
    (h : x a.1 = Quillen.SimplexCubeExtension.endpoint a.2) :
    InputIdentityCarrierCube.carrierCube X x = InputIdentityCarrierCube.globalFaces X a x :=
  InputIdentityCarrierCube.cube_on_face X a x h

end QuillenTest.GlobalRawBassInputIdentityComparison
