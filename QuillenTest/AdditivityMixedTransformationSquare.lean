/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.MixedTransformationSquare

/-! Actual middle-square maps, all four full faces, both times and the whole zero face. -/
public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory Opposite MonoidalCategory Quillen
open Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.MixedOrdinalCylinder
open scoped Simplicial Topology
universe u v
namespace QuillenTest.AdditivityMixedTransformationSquare
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G H F' G' H' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')
  (ηF : F ⟶ F') (ηG : G ⟶ G') (haη : a ≫ ηG = ηF ≫ a')
  (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X))

/-- The actual middle square uses the original minimum-cut input followed by the weak cylinder. -/
theorem original_square :
    normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      mixedTransformationInputCylinder V ▷ Δ[1] ≫
        (normalizedMixedTransformationHomotopy V W a a' b b' hs hs'
          ηF ηG haη hηF hηG).h := rfl

/-- The original exported map is retained by this named client. -/
theorem original_transformation_zero :
    SSet.ι₀ ≫ normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      (normalizedMixedEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration).h :=
  normalizedMixedTransformationSquare_transformation_zero V W a a' b b' hs hs' ηF ηG haη hηF hηG

/-- The original exported map is retained by this named client. -/
theorem original_transformation_one :
    SSet.ι₁ ≫ normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      (normalizedMixedEndpointHomotopy V W a' hs'.exactF hs'.exactG hs'.cofibration).h :=
  normalizedMixedTransformationSquare_transformation_one V W a a' b b' hs hs' ηF ηG haη hηF hηG

/-- The original exported map is retained by this named client. -/
theorem original_mixed_zero :
    (SSet.ι₀ ▷ Δ[1]) ≫
        normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      TheoremA.diagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) ▷
          Δ[1] ≫
        (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h :=
  normalizedMixedTransformationSquare_mixed_zero V W a a' b b' hs hs' ηF ηG haη hηF hηG

/-- The original exported map is retained by this named client. -/
theorem original_mixed_one :
    (SSet.ι₁ ▷ Δ[1]) ≫
        normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h :=
  normalizedMixedTransformationSquare_mixed_one V W a a' b b' hs hs' ηF ηG haη hηF hηG

/-- The original exported map is retained by this named client. -/
theorem original_full_zero_cylinder :
    ((SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) ≫
        normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      CartesianMonoidalCategory.fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) :=
  normalizedMixedTransformationSquare_fixed_zero V W a a' b b' hs hs' ηF ηG haη hηF hηG

/-- The original exported map is retained by this named client. -/
theorem original_realization_comparison (t s : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (t, (s, x)) =
      SSet.toTop.map
        (normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG)
        ((realizationCylinderIso
          (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1])).inv
          ((realizationCylinderIso
            (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V))).inv
              (x, ULift.up s), ULift.up t)) :=
  normalizedMixedTransformationRealizationSquare_apply V W a a' b b' hs hs'
    ηF ηG haη hηF hηG t s x

/-- The original exported map is retained by this named client. -/
theorem original_full_zero_square (t s : unitInterval) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (t, (s, subdivisionBasepoint V)) = realizationPoint (diagonalZeroVertex W) :=
  normalizedMixedTransformationRealizationSquare_fixed_zero V W a a' b b' hs hs'
    ηF ηG haη hηF hηG t s

/-- Both times act in the specified transformation/mixed/input order on the actual old maps. -/
theorem original_two_times (t s : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (t, (s, x)) =
      realizationSimplicialHomotopy
        (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
        (t, realizationSimplicialHomotopy (outerContraction (bisimplicialSSet V))
          (s, SSet.toTop.map
            (TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V))) x)) := rfl

end QuillenTest.AdditivityMixedTransformationSquare
