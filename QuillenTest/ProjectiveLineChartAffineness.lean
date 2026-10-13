/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.ChartAffineness

/-! # Genuine affine chart and overlap morphisms over arbitrary base rings -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Quillen.Scheme.ProjectiveLine
open Quillen.Scheme.PolynomialLaurent

namespace QuillenTest.ProjectiveLineChartAffineness

open Quillen

/-- The original overlap-to-line morphism is affine, with its literal factorization. -/
theorem original_overlap_affine (R : CommRingCat.{u}) :
    IsAffineHom (laurentPlus R ≫ plusChart R) := inferInstance

/-- The negative-chart inverse image is the actual Laurent open. -/
theorem original_negative_chart_intersection (R : CommRingCat.{u}) :
    minusChart R ⁻¹ᵁ (plusChart R).opensRange = (laurentMinus R).opensRange :=
  minusChart_preimage_plusRange R

/-- Both original chart immersions remain affine over a nonreduced ring. -/
theorem nonreduced_chart_affineness :
    IsAffineHom (plusChart (.of (ZMod 4))) ∧ IsAffineHom (minusChart (.of (ZMod 4))) :=
  ⟨inferInstance, inferInstance⟩

/-- The empty projective line over the zero ring is included. -/
theorem zero_ring_chart_affineness :
    IsAffineHom (plusChart (.of (ZMod 1))) ∧ IsAffineHom (minusChart (.of (ZMod 1))) :=
  ⟨inferInstance, inferInstance⟩

end QuillenTest.ProjectiveLineChartAffineness
