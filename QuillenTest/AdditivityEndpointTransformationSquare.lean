/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.EndpointTransformationSquare

/-! # Whole original endpoint squares and their complete zero surfaces -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Additivity
open scoped Simplicial Topology
universe u v
namespace QuillenTest.AdditivityEndpointTransformationSquare
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G H F' G' H' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')
  (ηF : F ⟶ F') (ηG : G ⟶ G') (haη : a ≫ ηG = ηF ≫ a')
  (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X))

/-- Both horizontal endpoint tracks are exactly the two old entire cylinders. -/
theorem identity_original_endpoint_cylinders :
    SSet.ι₀ ≫ normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
      = (normalizedIdentityEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration).h ∧
      SSet.ι₁ ≫ normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF
        hηG = (normalizedIdentityEndpointHomotopy V W a' hs'.exactF hs'.exactG hs'.cofibration).h :=
  ⟨normalizedIdentityEndpointTransformationSquare_transformation_zero V W a a' b b' hs hs' ηF ηG
    haη hηF hηG,
    normalizedIdentityEndpointTransformationSquare_transformation_one V W a a' b b' hs hs' ηF ηG
      haη hηF hηG⟩

/-- Both vertical tracks retain the complete original transformation cylinders. -/
theorem identity_original_transformation_cylinders :
    (SSet.ι₀ ▷ Δ[1]) ≫ normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG
      haη hηF hηG = (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF
      hηG).h ∧
      (SSet.ι₁ ▷ Δ[1]) ≫ normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG
        haη hηF hηG = (normalizedMiddleTransformationHomotopy V W a a' b b' hs hs' ηG hηG).h :=
  ⟨normalizedIdentityEndpointTransformationSquare_endpoint_zero V W a a' b b' hs hs' ηF ηG haη hηF
    hηG,
    normalizedIdentityEndpointTransformationSquare_endpoint_one V W a a' b b' hs hs' ηF ηG haη hηF
      hηG⟩

/-- The full simplicial zero square retains both independent times. -/
theorem identity_whole_zero_simplex :
    ((SSet.yonedaEquiv.symm (diagonalZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) ≫
      normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      CartesianMonoidalCategory.fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) :=
  normalizedIdentityEndpointTransformationSquare_fixed_zero V W a a' b b' hs hs' ηF ηG haη hηF hηG

/-- The two complete old realized endpoint tracks keep their original parametrizations. -/
theorem identity_original_realized_endpoints (s : unitInterval) (x : |TheoremA.diagonalSSet
  (bisimplicialSSet V)|) :
    normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG (0, (s, x)) = realizationSimplicialHomotopy (normalizedIdentityEndpointHomotopy V W a
      hs.exactF hs.exactG hs.cofibration) (s, x) ∧
      normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
        hηG (1, (s, x)) = realizationSimplicialHomotopy (normalizedIdentityEndpointHomotopy V W a'
        hs'.exactF hs'.exactG hs'.cofibration) (s, x) :=
  ⟨normalizedIdentityEndpointTransformationRealizationSquare_transformation_zero V W a a' b b' hs
    hs' ηF ηG haη hηF hηG s x,
    normalizedIdentityEndpointTransformationRealizationSquare_transformation_one V W a a' b b' hs
      hs' ηF ηG haη hηF hηG s x⟩

/-- The two complete realized transformation faces preserve the actual middle or quotient sum. -/
theorem identity_original_realized_transformations (t : unitInterval) (x : |TheoremA.diagonalSSet
  (bisimplicialSSet V)|) :
    normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG (t, (0, x)) = realizationSimplicialHomotopy (normalizedIdentityTransformationHomotopy V W
      a a' b b' hs hs' ηF ηG haη hηF hηG) (t, x) ∧
      normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
        hηG (t, (1, x)) = realizationSimplicialHomotopy (normalizedMiddleTransformationHomotopy V W
        a a' b b' hs hs' ηG hηG) (t, x) :=
  ⟨normalizedIdentityEndpointTransformationRealizationSquare_endpoint_zero V W a a' b b' hs hs' ηF
    ηG haη hηF hηG t x,
    normalizedIdentityEndpointTransformationRealizationSquare_endpoint_one V W a a' b b' hs hs' ηF
      ηG haη hηF hηG t x⟩

/-- Both original continuous times fix the chosen source zero throughout the square. -/
theorem identity_whole_zero_surface (t s : unitInterval) :
    normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG (t, (s, realizationPoint (diagonalZeroVertex V))) =
      realizationPoint (diagonalZeroVertex W) :=
  normalizedIdentityEndpointTransformationRealizationSquare_fixed_zero V W a a' b b' hs hs' ηF ηG
    haη hηF hηG t s

variable [HasBinaryCoproducts D]
  (ηH : H ⟶ H') (hbη : b ≫ ηH = ηG ≫ b') (hηH : ∀ X, W.weq (ηH.app X))

/-- Both horizontal endpoint tracks are exactly the two old entire cylinders. -/
theorem separated_original_endpoint_cylinders :
    SSet.ι₀ ≫ normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH = (normalizedSeparatedEndpointHomotopy V W a b hs).h ∧
      SSet.ι₁ ≫ normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF
        hηG ηH hbη hηH = (normalizedSeparatedEndpointHomotopy V W a' b' hs').h :=
  ⟨normalizedSeparatedEndpointTransformationSquare_transformation_zero V W a a' b b' hs hs' ηF ηG
    haη hηF hηG ηH hbη hηH,
    normalizedSeparatedEndpointTransformationSquare_transformation_one V W a a' b b' hs hs' ηF ηG
      haη hηF hηG ηH hbη hηH⟩

/-- Both vertical tracks retain the complete original transformation cylinders. -/
theorem separated_original_transformation_cylinders :
    (SSet.ι₀ ▷ Δ[1]) ≫ normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG
      haη hηF hηG ηH hbη hηH = (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF
      ηG haη hηF hηG).h ∧
      (SSet.ι₁ ▷ Δ[1]) ≫ normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG
        haη hηF hηG ηH hbη hηH = (normalizedSumTransformationHomotopy V W a a' b b' hs hs' ηF hηF
        ηH hηH).h :=
  ⟨normalizedSeparatedEndpointTransformationSquare_endpoint_zero V W a a' b b' hs hs' ηF ηG haη hηF
    hηG ηH hbη hηH,
    normalizedSeparatedEndpointTransformationSquare_endpoint_one V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH⟩

/-- The full simplicial zero square retains both independent times. -/
theorem separated_whole_zero_simplex :
    ((SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) ≫
      normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG ηH hbη
      hηH =
      CartesianMonoidalCategory.fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) :=
  normalizedSeparatedEndpointTransformationSquare_fixed_zero V W a a' b b' hs hs' ηF ηG haη hηF hηG
    ηH hbη hηH

/-- The two complete old realized endpoint tracks keep their original parametrizations. -/
theorem separated_original_realized_endpoints (s : unitInterval) (x : |TheoremA.diagonalSSet
  (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedSeparatedEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH (0, (s, x)) = realizationSimplicialHomotopy
      (normalizedSeparatedEndpointHomotopy V W a b hs) (s, x) ∧
      normalizedSeparatedEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
        hηG ηH hbη hηH (1, (s, x)) = realizationSimplicialHomotopy
        (normalizedSeparatedEndpointHomotopy V W a' b' hs') (s, x) :=
  ⟨normalizedSeparatedEndpointTransformationRealizationSquare_transformation_zero V W a a' b b' hs
    hs' ηF ηG haη hηF hηG ηH hbη hηH s x,
    normalizedSeparatedEndpointTransformationRealizationSquare_transformation_one V W a a' b b' hs
      hs' ηF ηG haη hηF hηG ηH hbη hηH s x⟩

/-- The two complete realized transformation faces preserve the actual middle or quotient sum. -/
theorem separated_original_realized_transformations (t : unitInterval) (x : |TheoremA.diagonalSSet
  (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedSeparatedEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH (t, (0, x)) = realizationSimplicialHomotopy
      (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG) (t, x) ∧
      normalizedSeparatedEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
        hηG ηH hbη hηH (t, (1, x)) = realizationSimplicialHomotopy
        (normalizedSumTransformationHomotopy V W a a' b b' hs hs' ηF hηF ηH hηH) (t, x) :=
  ⟨normalizedSeparatedEndpointTransformationRealizationSquare_endpoint_zero V W a a' b b' hs hs' ηF
    ηG haη hηF hηG ηH hbη hηH t x,
    normalizedSeparatedEndpointTransformationRealizationSquare_endpoint_one V W a a' b b' hs hs' ηF
      ηG haη hηF hηG ηH hbη hηH t x⟩

/-- Both original continuous times fix the chosen source zero throughout the square. -/
theorem separated_whole_zero_surface (t s : unitInterval) :
    normalizedSeparatedEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH (t, (s, subdivisionBasepoint V)) =
      realizationPoint (diagonalZeroVertex W) :=
  normalizedSeparatedEndpointTransformationRealizationSquare_fixed_zero V W a a' b b' hs hs' ηF ηG
    haη hηF hηG ηH hbη hηH t s

end QuillenTest.AdditivityEndpointTransformationSquare
