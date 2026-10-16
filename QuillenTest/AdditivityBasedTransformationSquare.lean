/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.BasedTransformationSquare

/-! # The original based-additivity pasting, all four full faces and both zero times -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Additivity
open scoped Simplicial Topology
universe u v
namespace QuillenTest.AdditivityBasedTransformationSquare
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
  {F G H F' G' H' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')
  (ηF : F ⟶ F') (ηG : G ⟶ G') (ηH : H ⟶ H')
  (haη : a ≫ ηG = ηF ≫ a') (hbη : b ≫ ηH = ηG ≫ b')
  (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X))
  (hηH : ∀ X, W.weq (ηH.app X))

/-- Exactly one prefix reversal and the original dyadic concatenation are visible. -/
theorem original_pasting (t s : unitInterval) (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op
  ⋙ bisimplicialSSet V)|) :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (t, (s, x)) =
      ((subdividedIdentityEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF
        hηG).symm.trans
        ((subdividedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).trans
          (subdividedSeparatedEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG ηH haη hbη
            hηF hηG hηH))) (s, (t, x)) :=
  subdividedBasedAdditivityTransformationSquare_apply V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG
    hηH t s x

/-- The entire transformation-zero face is the original based-additivity homotopy. -/
theorem original_transformation_zero (s : unitInterval) (x : |TheoremA.diagonalSSet
  (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (0, (s, x)) =
      subdividedBasedAdditivityHomotopy V W a b hs (s, x) :=
  subdividedBasedAdditivityTransformationSquare_transformation_zero V W a a' b b' hs hs' ηF ηG ηH
    haη hbη hηF hηG hηH s x

/-- The entire transformation-one face is the original based-additivity homotopy. -/
theorem original_transformation_one (s : unitInterval) (x : |TheoremA.diagonalSSet
  (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (1, (s, x)) =
      subdividedBasedAdditivityHomotopy V W a' b' hs' (s, x) :=
  subdividedBasedAdditivityTransformationSquare_transformation_one V W a a' b b' hs hs' ηF ηG ηH
    haη hbη hηF hηG hηH s x

/-- The entire initial face keeps the actual rebased middle cylinder and horizontal restriction. -/
theorem original_middle_face (t : unitInterval) (x : |TheoremA.diagonalSSet
  (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (t, (0, x)) =
      realizationSimplicialHomotopy
        (normalizedMiddleTransformationHomotopy V W a a' b b' hs hs' ηG hηG)
        (t, (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))) x) :=
  subdividedBasedAdditivityTransformationSquare_additivity_zero V W a a' b b' hs hs' ηF ηG ηH haη
    hbη hηF hηG hηH t x

/-- The entire terminal face keeps the actual quotient-first normalized sum cylinder. -/
theorem original_quotient_first_face (t : unitInterval) (x : |TheoremA.diagonalSSet
  (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (t, (1, x)) =
      realizationSimplicialHomotopy
        (normalizedSumTransformationHomotopy V W a a' b b' hs hs' ηF hηF ηH hηH) (t, x) :=
  subdividedBasedAdditivityTransformationSquare_additivity_one V W a a' b b' hs hs' ηF ηG ηH haη
    hbη hηF hηG hηH t x

/-- Both independent continuous times fix the actual subdivision basepoint. -/
theorem original_whole_zero (t s : unitInterval) :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (t, (s, subdivisionBasepoint V)) = realizationPoint (diagonalZeroVertex W) :=
  subdividedBasedAdditivityTransformationSquare_fixed_zero V W a a' b b' hs hs' ηF ηG ηH haη hbη
    hηF hηG hηH t s

end QuillenTest.AdditivityBasedTransformationSquare
