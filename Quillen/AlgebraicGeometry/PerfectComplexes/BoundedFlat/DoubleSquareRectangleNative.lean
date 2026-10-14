/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ScalarRectangleParameter
public import Quillen.Waldhausen.SConstruction.Iterated.ScalarRouteExtraction

/-! The complete common-simplex scalar parameter evaluates to the literal native rectangle. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.DoubleSquareScalarPaths
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- Every level and both times of the actual original three-route comparison are one common
simplex scalar homotopy. This retains the native endpoint transports and full pasting word. -/
theorem rectangle_nativeLift :
    HomotopyLift (DoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq)
      rectangleParameter
      (boundedFlatDoubleSquareTrackComparison p q p' q' a b c hp hq) := by
  let S := DoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq
  have hf : HomotopyLift S firstComparison
      (DoubleSquareTrack.firstTriple (p := p) (q := q) (c := c)) :=
    first_native p q p' q' a b c hp hq
  have hm : HomotopyLift S middleComparison
      (DoubleSquareTrack.middleTriple p q q' b c hq) :=
    middle_native p q p' q' a b c hp hq
  have hl : HomotopyLift S lastComparison
      (DoubleSquareTrack.lastTriple p q p' q' a b c hp hq) :=
    last_native p q p' q' a b c hp hq
  have lC := PathLift.trans_left S (HomotopyLift.source S hf)
  have lD := PathLift.trans_right S (HomotopyLift.source S hf)
  have lE := PathLift.trans_left S (HomotopyLift.target S hf)
  have lF := PathLift.trans_right S (HomotopyLift.target S hf)
  have lG := PathLift.trans_left S (HomotopyLift.source S hm)
  have lH := PathLift.trans_right S (HomotopyLift.source S hm)
  have lI := PathLift.trans_right S (HomotopyLift.target S hm)
  have lJ := PathLift.trans_left S (HomotopyLift.target S hl)
  have lK := PathLift.trans_right S (HomotopyLift.target S hl)
  have lL := PathLift.trans_right S (HomotopyLift.source S hl)
  exact HomotopyLift.threeRoutes S lC lD lE lF lG lH lI lJ lK lL hf hm hl

/-- The resulting equality has the exact native all-level rectangle as its right side. -/
theorem rectangle_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen A)).space n) :
    prespectrumSimplexFamily (DoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq) n
      (rectangleParameter (r, s), x) =
      (boundedFlatDoubleSquareTrackComparison p q p' q' a b c hp hq).level n (r, (s, x)) :=
  rectangle_nativeLift p q p' q' a b c hp hq n r s x

end Quillen.PerfectComplexes.DoubleSquareScalarPaths
