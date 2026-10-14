/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SplitTripleParameters
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationPasting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleTrack

/-! The two normalized middle triangles retain the literal native pasting. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.SplitTripleSimplex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- Both complete native normalized triangles are assembled with the existing reversal and pause. -/
theorem normalized_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n
      ((normalizedLeftParameter.symm.trans normalizedRightParameter) (r, s), x) =
      (boundedFlatNormalizedTripleTrackComparison f g h).level n (r, (s, x)) := by
  change _ = (boundedFlatNormalizedTriplePasting f g h).level n (r, (s, x))
  unfold boundedFlatNormalizedTriplePasting
  rw [originalPrespectrumPastingHomotopy_whole_level, Path.Homotopy.trans_apply]
  split
  · exact normalizedLeftParameter_lift f g h n _ s x
  · exact normalizedRightParameter_lift f g h n _ s x

end Quillen.PerfectComplexes.SplitTripleSimplex
