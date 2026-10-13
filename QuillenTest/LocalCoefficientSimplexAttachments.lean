/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.SimplexAttachmentExcision

/-! Strict consumers of the original all-dimensional attachment comparison. -/

@[expose] public section
noncomputable section
open CategoryTheory Limits Convexity Quillen
universe u

example (X : TopCat.{u}) (n : ℕ) {B D : TopCat.{u}}
    {f : TopCat.of (X × simplexBoundary n) ⟶ B}
    {g : TopCat.of (X × StdSimplex ℝ (Fin (n + 1))) ⟶ D} {j : B ⟶ D}
    (sq : IsPushout (Quillen.parameterizedSimplexBoundaryInclusion X n) f g j)
    (L : LocalCoefficients.System.{u, u} D) :
    QuasiIso (LocalCoefficients.relativePushforwardChainMap g.hom
      (SimplexAttachment.sourceBoundary X n) (SimplexAttachment.baseImage (j := j))
      (SimplexAttachment.cell_mapsTo_boundary X n sq) L) :=
  LocalCoefficients.simplexAttachmentCell_relative_quasiIso X n sq L

example (X : TopCat.{u}) {B D : TopCat.{u}}
    {f : TopCat.of (X × simplexBoundary 0) ⟶ B}
    {g : TopCat.of (X × StdSimplex ℝ (Fin 1)) ⟶ D} {j : B ⟶ D}
    (sq : IsPushout (Quillen.parameterizedSimplexBoundaryInclusion X 0) f g j)
    (L : LocalCoefficients.System.{u, u} D) :
    QuasiIso (LocalCoefficients.relativePushforwardChainMap g.hom
      (SimplexAttachment.sourceBoundary X 0) (SimplexAttachment.baseImage (j := j))
      (SimplexAttachment.cell_mapsTo_boundary X 0 sq) L) :=
  LocalCoefficients.simplexAttachmentCell_relative_quasiIso X 0 sq L

