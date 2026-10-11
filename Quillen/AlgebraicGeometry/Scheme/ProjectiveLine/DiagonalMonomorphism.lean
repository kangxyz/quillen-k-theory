/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalAffine
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.OpenCoverMonomorphisms
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Monicity of the original relative diagonal incidence

The four original rectangle maps jointly cover the actual relative square. The already
proved local scalar monomorphisms therefore give monicity of the original incidence map
over every commutative ring, including the zero ring. No diagonal cokernel or generation
theorem is inferred.
-/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.Scheme.ProjectiveLine
open PolynomialLaurent
/-- One of the two original polynomial charts. -/
def polynomialChart (R : CommRingCat.{u}) (b : Bool) :
    Spec (.of (Polynomial R)) ⟶ twoChartLine R := if b then plusChart R else minusChart R
instance (R : CommRingCat.{u}) (b : Bool) : IsOpenImmersion (polynomialChart R b) := by
  cases b <;> dsimp [polynomialChart] <;> infer_instance
/-- Each original chart lies over the actual polynomial projection. -/
theorem polynomialChart_projection (R : CommRingCat.{u}) (b : Bool) :
    polynomialChart R b ≫ projection R = polynomialProjection R := by
  cases b <;> simp [polynomialChart, plusChart_projection, minusChart_projection]
/-- The four genuine rectangle maps, indexed by ordered pairs of chart choices. -/
def diagonalRectangle (R : CommRingCat.{u}) (b : Bool × Bool) :
    polynomialSquare R ⟶ relativeSquare R :=
  rectangleMap R (polynomialChart R b.1) (polynomialChart R b.2)
    (polynomialChart_projection R b.1) (polynomialChart_projection R b.2)
instance (R : CommRingCat.{u}) (b : Bool × Bool) : IsOpenImmersion (diagonalRectangle R b) :=
  inferInstanceAs (IsOpenImmersion (rectangleMap R _ _ _ _))
/-- The four original rectangles cover the actual relative square. -/
theorem diagonalRectangles_cover (R : CommRingCat.{u}) (x : relativeSquare R) :
    ∃ (b : Bool × Bool) (y : polynomialSquare R), diagonalRectangle R b y = x := by
  have hc (z : twoChartLine R) : ∃ b : Bool, z ∈ Set.range (polynomialChart R b) := by
    have hz : z ∈ (plusChart R).opensRange ⊔ (minusChart R).opensRange := by
      rw [chart_ranges_cover]
      trivial
    rcases hz with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨a, ha⟩ := hc (relativeFirst R x)
  obtain ⟨b, hb⟩ := hc (relativeSecond R x)
  refine ⟨(a,b), ?_⟩
  change x ∈ Set.range (diagonalRectangle R (a,b))
  have h := Scheme.Pullback.range_map (polynomialProjection R) (polynomialProjection R)
    (projection R) (projection R) (polynomialChart R a) (polynomialChart R b) (𝟙 (Spec R))
    (by simpa only [Category.comp_id] using (polynomialChart_projection R a).symm)
    (by simpa only [Category.comp_id] using (polynomialChart_projection R b).symm)
  change Set.range (diagonalRectangle R (a,b)) = _ at h
  rw [h]
  exact ⟨ha,hb⟩
end Quillen.Scheme.ProjectiveLine

namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf
/-- The actual incidence is monic on every original rectangle. -/
theorem mono_diagonalIncidence_rectangle (R : CommRingCat.{u}) (b : Bool × Bool) :
    Mono ((Scheme.Modules.pullback (diagonalRectangle R b)).map (diagonalIncidence R)) := by
  rcases b with ⟨a,b⟩
  cases a <;> cases b
  · exact mono_diagonalIncidence_minus_minus R
  · exact mono_diagonalIncidence_minus_plus R
  · exact mono_diagonalIncidence_plus_minus R
  · exact mono_diagonalIncidence_plus_plus R
/-- The original relative incidence map is a genuine monomorphism over every base ring. -/
theorem mono_diagonalIncidence (R : CommRingCat.{u}) : Mono (diagonalIncidence R) := by
  apply mono_of_restrict_openCover (fun _ : Bool × Bool => polynomialSquare R)
    (diagonalRectangle R) (diagonalRectangles_cover R)
  intro b
  have := mono_diagonalIncidence_rectangle R b
  exact mono_restrict_of_mono_pullback _ _
end Quillen.Scheme.ProjectiveLine
