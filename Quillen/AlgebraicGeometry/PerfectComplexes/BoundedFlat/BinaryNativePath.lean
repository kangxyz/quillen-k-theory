/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassChartScalarFaces

/-! The literal split binary path in its original normalization triangle. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BinaryNormalizationSimplex

/-- Both native normalization pieces remain in the binary path, at every original level. -/
theorem native_path {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    prespectrumSimplexFamily (simplex f g) n (binaryPath (k := 2) 0 1 2 t, x) =
      (boundedFlatPerfectPrespectrumCompHomotopy f g).level n (t, x) := by
  have h := (whole_triangle f g n 1 t x).trans (native_apply f g n 1 t x).symm
  rw [Quillen.TheoremB.compositionTriangleHomotopy.apply_one] at h
  exact h.trans (((boundedFlatNormalizedCompTrackComparison f g).level n).apply_one (t, x))

end Quillen.PerfectComplexes.BinaryNormalizationSimplex
