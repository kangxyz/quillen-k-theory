/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Additivity.RealizationHomotopy

/-! # The actual simplicial homotopy between mixed-deformation endpoints -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory
open Quillen.MixedOrdinalCylinder
open scoped Simplicial
universe u

namespace Quillen.Waldhausen.Additivity

/-- The minimum-cut cylinder, restricted to the one endpoint and followed
by the actual deformation. This retains an explicit cylinder for tracking
chosen vertices, before any cancellation of subdivision. -/
def mixedEndpointHomotopy (X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (θ : outerCylinder X ⟶ Y) :
    SSet.Homotopy
      (TheoremA.diagonalMap (OrdinalSubdivision.horizontalEndpoint X) ≫
        TheoremA.diagonalMap (outerZeroSection X ≫ θ))
      (TheoremA.diagonalMap (outerOneSection X ≫ θ)) where
  h := TheoremA.diagonalMap (outerOneSection X) ▷ Δ[1] ≫
    (outerContraction X).h ≫ TheoremA.diagonalMap θ
  h₀ := by
    simp only [SSet.ι₀_comp_assoc, SSet.Homotopy.h₀_assoc]
    change TheoremA.diagonalFunctor.map
      (outerOneSection X ≫ outerProjection X ≫ outerZeroSection X ≫ θ) =
        TheoremA.diagonalFunctor.map
          (OrdinalSubdivision.horizontalEndpoint X ≫ outerZeroSection X ≫ θ)
    exact congrArg TheoremA.diagonalFunctor.map (by
      rw [← Category.assoc (outerOneSection X), outerOneSection_projection])
  h₁ := by simp only [SSet.ι₁_comp_assoc, SSet.Homotopy.h₁_assoc, Category.id_comp]; rfl
  rel := by ext n z; exact z.1.property.elim

end Quillen.Waldhausen.Additivity
