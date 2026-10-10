/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Additivity.MixedEndpointHomotopy
public import Quillen.Waldhausen.Additivity.NormalizedZeroMaps

/-! # The mixed additivity deformation has a genuinely fixed chosen zero -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Quillen.MixedOrdinalCylinder
open scoped Simplicial
universe u v

namespace Quillen.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (hc : IsCofibrationTransformation W a V)

/-- The normalized mixed deformation with its exact identity and separated
endpoint maps. Its underlying cylinder is the actual minimum-cut cylinder. -/
def normalizedMixedEndpointHomotopy :
    SSet.Homotopy
      (TheoremA.diagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) ≫
        TheoremA.diagonalMap (normalizedIdentityMap V W a hF hG hc))
      (TheoremA.diagonalMap (normalizedSeparatedMap V W a hF hG hc)) where
  h := (mixedEndpointHomotopy (bisimplicialSSet V) (bisimplicialSSet W)
    (normalizedMixedMap V W a hF hG hc)).h
  h₀ := by
    rw [SSet.Homotopy.h₀, normalizedMixedMap_zero]; rfl
  h₁ := by
    rw [SSet.Homotopy.h₁, normalizedMixedMap_one]; rfl
  rel := by ext n z; exact z.1.property.elim

/-- At the actual subdivided zero vertex the entire simplicial cylinder is
literally constant. All intermediate cuts retain the same chosen zero. -/
theorem normalizedMixedEndpointHomotopy_fixed_zero :
    SSet.yonedaEquiv.symm
      (show (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)) _⦋0⦌ from
        zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (OrdinalSubdivision.δ.obj ⦋0⦌)) (op ⦋0⦌)) ▷
          Δ[1] ≫
      (normalizedMixedEndpointHomotopy V W a hF hG hc).h =
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) := by
  ext n z
  apply Subtype.ext
  exact diagram_eq_const_of_zero W _
    (fun _ ↦ normalizedPushoutFunctor_obj_zero V W a hF hG hc)

/-- The realized deformation genuinely stays at the chosen target zero. -/
theorem normalizedMixedRealizationHomotopy_fixed_zero (t : unitInterval) :
    realizationSimplicialHomotopy (normalizedMixedEndpointHomotopy V W a hF hG hc)
      (t, realizationPoint
        (show (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)) _⦋0⦌ from
          zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (OrdinalSubdivision.δ.obj ⦋0⦌)) (op ⦋0⦌))) =
        realizationPoint (diagonalZeroVertex W) :=
  realizationSimplicialHomotopy_fixed_vertex _ _ _
    (normalizedMixedEndpointHomotopy_fixed_zero V W a hF hG hc) t

end Quillen.Waldhausen.Additivity
