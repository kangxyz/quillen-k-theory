/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affineness of the original projective-line charts

Both actual chart immersions are affine morphisms: their inverse images of the
two chart opens are respectively the entire affine line and the genuine Laurent
open. This applies over arbitrary commutative rings, including the zero ring.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry

namespace Quillen.Scheme.ProjectiveLine
open Quillen.Scheme.PolynomialLaurent
variable (R : CommRingCat.{u})

/-- The original negative chart meets the positive chart in its actual Laurent open. -/
theorem minusChart_preimage_plusRange :
    minusChart R ⁻¹ᵁ (plusChart R).opensRange = (laurentMinus R).opensRange := by
  ext b
  change (∃ a, plusChart R a = minusChart R b) ↔ ∃ z, laurentMinus R z = b
  constructor
  · rintro ⟨a, h⟩
    obtain ⟨z, _, hz⟩ := (chart_eq_iff R a b).mp h
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨laurentPlus R z, congrArg (fun f => f z) (overlap_equation R)⟩

/-- The original positive chart immersion is an affine morphism. -/
instance plusChart_isAffineHom : IsAffineHom (plusChart R) := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  rcases charts_jointly_surjective R x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · refine ⟨(plusChart R).opensRange, ⟨a, rfl⟩, isAffineOpen_opensRange _, ?_⟩
    simpa using isAffineOpen_top (Spec (.of (Polynomial R)))
  · refine ⟨(minusChart R).opensRange, ⟨b, rfl⟩, isAffineOpen_opensRange _, ?_⟩
    rw [plusChart_preimage_minusRange]
    exact isAffineOpen_opensRange _

/-- The original negative chart immersion is an affine morphism. -/
instance minusChart_isAffineHom : IsAffineHom (minusChart R) := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  rcases charts_jointly_surjective R x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · refine ⟨(plusChart R).opensRange, ⟨a, rfl⟩, isAffineOpen_opensRange _, ?_⟩
    rw [minusChart_preimage_plusRange]
    exact isAffineOpen_opensRange _
  · refine ⟨(minusChart R).opensRange, ⟨b, rfl⟩, isAffineOpen_opensRange _, ?_⟩
    simpa using isAffineOpen_top (Spec (.of (Polynomial R)))

end Quillen.Scheme.ProjectiveLine
