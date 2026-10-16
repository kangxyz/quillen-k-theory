/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.EndpointTransformationSquare
public import Quillen.Waldhausen.Additivity.BasedAdditivity

/-! # The whole based-additivity transformation square on the original subdivision

Transformation time remains an independent source parameter while the unreversed identity
endpoint square, actual minimum-cut middle square and separated endpoint square are pasted.
The definition is literally prefix.symm.trans (middle.trans suffix), with exactly one prefix
reversal and the original half/quarter/quarter times. All four entire faces and the complete
chosen-zero surface are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.Waldhausen.Additivity

/-- A full constant-zero square becomes a relative homotopy with its other time in the source. -/
def transposedSquareHomotopyRel {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (Q : C(unitInterval × (unitInterval × X), Y)) (f g : C(unitInterval × X, Y))
    (h₀ : ∀ t x, Q (t, (0, x)) = f (t, x))
    (h₁ : ∀ t x, Q (t, (1, x)) = g (t, x))
    (x₀ : X) (y₀ : Y) (hz : ∀ t s, Q (t, (s, x₀)) = y₀) :
    f.HomotopyRel g {p | p.2 = x₀} where
  toHomotopy := {
    toFun := fun z ↦ Q (z.2.1, (z.1, z.2.2))
    continuous_toFun := by fun_prop
    map_zero_left := fun p ↦ h₀ p.1 p.2
    map_one_left := fun p ↦ h₁ p.1 p.2 }
  prop' s p hp := by
    change Q (p.1, (s, p.2)) = f p
    have hx : p.2 = x₀ := hp
    rcases p with ⟨t, x⟩
    change x = x₀ at hx
    subst x
    exact (hz t s).trans ((hz t 0).symm.trans (h₀ t x₀))

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
  {F G H F' G' H' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')
  (ηF : F ⟶ F') (ηG : G ⟶ G') (ηH : H ⟶ H')
  (haη : a ≫ ηG = ηF ≫ a') (hbη : b ≫ ηH = ηG ≫ b')
  (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X))
  (hηH : ∀ X, W.weq (ηH.app X))

/-- The actual identity transformation track as a map on the subdivided source. -/
def subdividedIdentityTransformationMap :
    C(unitInterval × |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|,
      |TheoremA.diagonalSSet (bisimplicialSSet W)|) :=
  (realizationSimplicialHomotopy
    (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF
      hηG)).toContinuousMap.comp
      ⟨fun z ↦ (z.1, (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet
        V))) z.2), by fun_prop⟩

/-- The actual middle transformation track as a map on the subdivided source. -/
def subdividedMiddleTransformationMap :
    C(unitInterval × |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|,
      |TheoremA.diagonalSSet (bisimplicialSSet W)|) :=
  (realizationSimplicialHomotopy
    (normalizedMiddleTransformationHomotopy V W a a' b b' hs hs' ηG hηG)).toContinuousMap.comp
      ⟨fun z ↦ (z.1, (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet
        V))) z.2), by fun_prop⟩

/-- The actual separated transformation track as a map on the subdivided source. -/
def subdividedSeparatedTransformationMap :
    C(unitInterval × |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|,
      |TheoremA.diagonalSSet (bisimplicialSSet W)|) :=
  (realizationSimplicialHomotopy
    (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF
      hηG)).toContinuousMap

/-- The actual sum transformation track as a map on the subdivided source. -/
def subdividedSumTransformationMap :
    C(unitInterval × |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|,
      |TheoremA.diagonalSSet (bisimplicialSSet W)|) :=
  (realizationSimplicialHomotopy
    (normalizedSumTransformationHomotopy V W a a' b b' hs hs' ηF hηF ηH hηH)).toContinuousMap

/-- The unreversed identity endpoint square, relative to the entire source zero line. -/
def subdividedIdentityEndpointTransformationHomotopy :
    (subdividedIdentityTransformationMap V W a a' b b' hs hs' ηF ηG haη hηF hηG).HomotopyRel
      (subdividedMiddleTransformationMap V W a a' b b' hs hs' ηG hηG)
      {p | p.2 = subdivisionBasepoint V} :=
  transposedSquareHomotopyRel
    ((normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG).comp
      ⟨fun z ↦ (z.1, (z.2.1, (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint
        (bisimplicialSSet V))) z.2.2)), by fun_prop⟩)
    (subdividedIdentityTransformationMap V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (subdividedMiddleTransformationMap V W a a' b b' hs hs' ηG hηG)
    (fun t x ↦ normalizedIdentityEndpointTransformationRealizationSquare_endpoint_zero
      V W a a' b b' hs hs' ηF ηG haη hηF hηG t ((realizedDiagonalMap
        (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))) x))
    (fun t x ↦ normalizedIdentityEndpointTransformationRealizationSquare_endpoint_one
      V W a a' b b' hs hs' ηF ηG haη hηF hηG t ((realizedDiagonalMap
        (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))) x))
    (subdivisionBasepoint V) (realizationPoint (diagonalZeroVertex W)) (by
      intro t s
      change normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG
        haη hηF hηG
        (t, (s, (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
          (subdivisionBasepoint V))) = _
      rw [horizontalEndpoint_basepoint V]
      exact normalizedIdentityEndpointTransformationRealizationSquare_fixed_zero V W a a' b b' hs
        hs' ηF ηG haη hηF hηG t s)

/-- The actual minimum-cut middle square, relative to the entire source zero line. -/
def subdividedMixedTransformationHomotopy :
    (subdividedIdentityTransformationMap V W a a' b b' hs hs' ηF ηG haη hηF hηG).HomotopyRel
      (subdividedSeparatedTransformationMap V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      {p | p.2 = subdivisionBasepoint V} :=
  transposedSquareHomotopyRel (normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs'
    ηF ηG haη
    hηF hηG)
    (subdividedIdentityTransformationMap V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (subdividedSeparatedTransformationMap V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (normalizedMixedTransformationRealizationSquare_mixed_zero V W a a' b b' hs hs' ηF ηG haη hηF
      hηG)
    (normalizedMixedTransformationRealizationSquare_mixed_one V W a a' b b' hs hs' ηF ηG haη hηF
      hηG)
    (subdivisionBasepoint V) (realizationPoint (diagonalZeroVertex W))
    (normalizedMixedTransformationRealizationSquare_fixed_zero V W a a' b b' hs hs' ηF ηG haη hηF
      hηG)

/-- The unreversed separated endpoint square, retaining the quotient-first sum transformation. -/
def subdividedSeparatedEndpointTransformationHomotopy :
    (subdividedSeparatedTransformationMap V W a a' b b' hs hs' ηF ηG haη hηF hηG).HomotopyRel
      (subdividedSumTransformationMap V W a a' b b' hs hs' ηF ηH hηF hηH)
      {p | p.2 = subdivisionBasepoint V} :=
  transposedSquareHomotopyRel (normalizedSeparatedEndpointTransformationRealizationSquare V W a a'
    b b' hs
    hs' ηF ηG haη hηF hηG ηH hbη hηH)
    (subdividedSeparatedTransformationMap V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (subdividedSumTransformationMap V W a a' b b' hs hs' ηF ηH hηF hηH)
    (normalizedSeparatedEndpointTransformationRealizationSquare_endpoint_zero V W a a' b b' hs hs'
      ηF ηG haη hηF hηG ηH hbη hηH)
    (normalizedSeparatedEndpointTransformationRealizationSquare_endpoint_one V W a a' b b' hs hs'
      ηF ηG haη hηF hηG ηH hbη hηH)
    (subdivisionBasepoint V) (realizationPoint (diagonalZeroVertex W))
    (normalizedSeparatedEndpointTransformationRealizationSquare_fixed_zero V W a a' b b' hs hs' ηF
      ηG haη hηF hηG ηH hbη hηH)

/-- The original pasting reverses the identity prefix exactly once. -/
def subdividedBasedAdditivityTransformationHomotopy :
    (subdividedMiddleTransformationMap V W a a' b b' hs hs' ηG hηG).HomotopyRel
      (subdividedSumTransformationMap V W a a' b b' hs hs' ηF ηH hηF hηH)
      {p | p.2 = subdivisionBasepoint V} :=
  (subdividedIdentityEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF
    hηG).symm.trans
    ((subdividedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).trans
      (subdividedSeparatedEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF
        hηG hηH))

/-- The whole based-additivity square has transformation time first and original input last. -/
def subdividedBasedAdditivityTransformationSquare :
    C(unitInterval × (unitInterval × |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙
      bisimplicialSSet V)|), |TheoremA.diagonalSSet (bisimplicialSSet W)|) :=
  ⟨fun z ↦ subdividedBasedAdditivityTransformationHomotopy V W a a' b b' hs hs' ηF ηG ηH haη hbη
    hηF hηG hηH (z.2.1, (z.1, z.2.2)),
    by fun_prop⟩

/-- Evaluation is the literal once-reversed-prefix, middle, suffix concatenation. -/
theorem subdividedBasedAdditivityTransformationSquare_apply (t s : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (t, (s, x)) =
      ((subdividedIdentityEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF
        hηG).symm.trans
        ((subdividedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).trans
          (subdividedSeparatedEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG ηH haη hbη
            hηF hηG hηH))) (s, (t, x)) := rfl

/-- The complete initial face is the actual rebased middle transformation on horizontal
  restriction. -/
theorem subdividedBasedAdditivityTransformationSquare_additivity_zero (t : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (t, (0, x)) =
      realizationSimplicialHomotopy
        (normalizedMiddleTransformationHomotopy V W a a' b b' hs hs' ηG hηG)
        (t, (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))) x) :=
  (subdividedBasedAdditivityTransformationHomotopy V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG
    hηH).apply_zero (t, x)

/-- The complete terminal face is the actual quotient-first normalized sum transformation. -/
theorem subdividedBasedAdditivityTransformationSquare_additivity_one (t : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (t, (1, x)) =
      realizationSimplicialHomotopy
        (normalizedSumTransformationHomotopy V W a a' b b' hs hs' ηF hηF ηH hηH) (t, x) :=
  (subdividedBasedAdditivityTransformationHomotopy V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG
    hηH).apply_one (t, x)

/-- Both independent times fix the entire actual subdivision zero line. -/
theorem subdividedBasedAdditivityTransformationSquare_fixed_zero (t s : unitInterval) :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (t, (s, subdivisionBasepoint V)) = realizationPoint (diagonalZeroVertex W) := by
  have h := (subdividedBasedAdditivityTransformationHomotopy V W a a' b b' hs hs' ηF ηG ηH haη hbη
    hηF hηG hηH).eq_fst
    s (x := (t, subdivisionBasepoint V)) rfl
  change subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF
    hηG hηH
    (t, (s, subdivisionBasepoint V)) = (subdividedMiddleTransformationMap V W a a' b b' hs hs' ηG
      hηG) (t, subdivisionBasepoint V) at h
  refine h.trans ?_
  change realizationSimplicialHomotopy
    (normalizedMiddleTransformationHomotopy V W a a' b b' hs hs' ηG hηG)
    (t, (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
      (subdivisionBasepoint V)) = _
  rw [horizontalEndpoint_basepoint V]
  exact (normalizedIdentityEndpointTransformationRealizationSquare_endpoint_one
    V W a a' b b' hs hs' ηF ηG haη hηF hηG t (realizationPoint (diagonalZeroVertex V))).symm.trans
      (normalizedIdentityEndpointTransformationRealizationSquare_fixed_zero V W a a' b b' hs hs' ηF
        ηG haη hηF hηG t 1)

/-- Transformation time zero is the whole original based-additivity homotopy. -/
theorem subdividedBasedAdditivityTransformationSquare_transformation_zero
    (s : unitInterval) (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|)
      :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (0, (s, x)) =
      subdividedBasedAdditivityHomotopy V W a b hs (s, x) := by
  change ((subdividedIdentityEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF
    hηG).symm.trans
    ((subdividedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).trans
      (subdividedSeparatedEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF
        hηG hηH))) (s, (0, x)) = _
  unfold subdividedBasedAdditivityHomotopy
  simp only [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact normalizedIdentityEndpointTransformationRealizationSquare_transformation_zero
      V W a a' b b' hs hs' ηF ηG haη hηF hηG _ _
  · exact normalizedMixedTransformationRealizationSquare_transformation_zero
      V W a a' b b' hs hs' ηF ηG haη hηF hηG _ _
  · exact normalizedSeparatedEndpointTransformationRealizationSquare_transformation_zero
      V W a a' b b' hs hs' ηF ηG haη hηF hηG ηH hbη hηH _ _

/-- Transformation time one is the whole original based-additivity homotopy. -/
theorem subdividedBasedAdditivityTransformationSquare_transformation_one
    (s : unitInterval) (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|)
      :
    subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH
      (1, (s, x)) =
      subdividedBasedAdditivityHomotopy V W a' b' hs' (s, x) := by
  change ((subdividedIdentityEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF
    hηG).symm.trans
    ((subdividedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).trans
      (subdividedSeparatedEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF
        hηG hηH))) (s, (1, x)) = _
  unfold subdividedBasedAdditivityHomotopy
  simp only [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact normalizedIdentityEndpointTransformationRealizationSquare_transformation_one
      V W a a' b b' hs hs' ηF ηG haη hηF hηG _ _
  · exact normalizedMixedTransformationRealizationSquare_transformation_one
      V W a a' b b' hs hs' ηF ηG haη hηF hηG _ _
  · exact normalizedSeparatedEndpointTransformationRealizationSquare_transformation_one
      V W a a' b b' hs hs' ηF ηG haη hηF hηG ηH hbη hηH _ _

end Quillen.Waldhausen.Additivity
