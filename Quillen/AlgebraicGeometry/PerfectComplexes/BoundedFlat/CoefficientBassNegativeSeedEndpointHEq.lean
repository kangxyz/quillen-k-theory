/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeSeedReferenceRails

/-! The complete original C0 and C1 source seeds are invariant under factorization. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassNegativeSeedReference
open CoefficientBassNegativeSeedReferenceRails

private theorem trans_heq {Y Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    {f₀ f₁ f₂ : C(I, Y)} {g₀ g₁ g₂ : C(I, Z)}
    (H : f₀.Homotopy f₁) (K : f₁.Homotopy f₂)
    (H' : g₀.Homotopy g₁) (K' : g₁.Homotopy g₂)
    (hH : ∀ s : I, HEq (H (s, 0)) (H' (s, 0)))
    (hK : ∀ s : I, HEq (K (s, 0)) (K' (s, 0))) (s : I) :
    HEq (H.trans K (s, 0)) (H'.trans K' (s, 0)) := by
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH _
  · exact hK _

private theorem symm_heq {Y Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    {f₀ f₁ : C(I, Y)} {g₀ g₁ : C(I, Z)}
    (H : f₀.Homotopy f₁) (H' : g₀.Homotopy g₁)
    (hH : ∀ s : I, HEq (H (s, 0)) (H' (s, 0))) (s : I) :
    HEq (H.symm (s, 0)) (H'.symm (s, 0)) := hH (unitInterval.symm s)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b b' c : Under R} (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c)

/-- The complete minus C0 source null retains its original nested clocks. -/
theorem c0_null_minus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC0CarrierSeed.nullMinus P p q (s, 0))
      (CoefficientBassPositiveC0CarrierSeed.nullMinus P p' q' (s, 0)) :=
  trans_heq _ _ _ _ (c0_projection_minus_heq P p q p' q' h)
    (c0_contraction_minus_heq P p q p' q' h) s

/-- The complete plus C0 source null retains its original nested clocks. -/
theorem c0_null_plus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC0CarrierSeed.nullPlus P p q (s, 0))
      (CoefficientBassPositiveC0CarrierSeed.nullPlus P p' q' (s, 0)) :=
  trans_heq _ _ _ _ (c0_projection_plus_heq P p q p' q' h)
    (c0_contraction_plus_heq P p q p' q' h) s

/-- The whole C0 source seed keeps its literal null-inverse, unit, null parentheses. -/
theorem c0_source_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC0CarrierSeed.face P p q (0, s))
      (CoefficientBassPositiveC0CarrierSeed.face P p' q' (0, s)) := by
  rw [CoefficientBassPositiveC0CarrierSeed.face_word,
    CoefficientBassPositiveC0CarrierSeed.face_word]
  refine trans_heq _ _ _ _ ?_ ?_ s
  · exact symm_heq _ _ (c0_null_minus_heq P p q p' q' h)
  · exact trans_heq _ _ _ _ (c0_unit_heq P p q p' q' h)
      (c0_null_plus_heq P p q p' q' h)


/-- The minus corrected square preserves its entire original lower boundary. -/
theorem c1_corrected_minus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1SeedFace.correctedMinus P p q (s, 0))
      (CoefficientBassPositiveC1SeedFace.correctedMinus P p' q' (s, 0)) := by
  change HEq ((CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P p q).parameter (0, s))
    ((CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P p' q').parameter (0, s))
  rw [(CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P p q).at_zero,
    (CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P p' q').at_zero]
  change HEq ((CoefficientBassPositiveC1InitialMovingNull.firstSwap P p q).trans
    (CoefficientBassPositiveC1InitialMovingNull.lastSwap P p q) (s, 0))
    ((CoefficientBassPositiveC1InitialMovingNull.firstSwap P p' q').trans
      (CoefficientBassPositiveC1InitialMovingNull.lastSwap P p' q') (s, 0))
  exact trans_heq _ _ _ _ (c1_chart_minus_heq P p q p' q' h)
    (c1_cylinder_minus_heq P p q p' q' h) s

/-- The plus corrected square preserves its entire original lower boundary. -/
theorem c1_corrected_plus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1SeedFace.correctedPlus P p q (s, 0))
      (CoefficientBassPositiveC1SeedFace.correctedPlus P p' q' (s, 0)) := by
  change HEq ((CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P p q).parameter
    (0, s))
    ((CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P p' q').parameter (0, s))
  rw [(CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P p q).at_zero,
    (CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P p' q').at_zero]
  change HEq ((CoefficientBassPositiveC1ShiftedInitialMovingNull.firstSwap P p q).trans
    (CoefficientBassPositiveC1ShiftedInitialMovingNull.lastSwap P p q) (s, 0))
    ((CoefficientBassPositiveC1ShiftedInitialMovingNull.firstSwap P p' q').trans
      (CoefficientBassPositiveC1ShiftedInitialMovingNull.lastSwap P p' q') (s, 0))
  exact trans_heq _ _ _ _ (c1_chart_plus_heq P p q p' q' h)
    (c1_cylinder_plus_heq P p q p' q' h) s

/-- The complete minus C1 source null retains its original nested clocks. -/
theorem c1_null_minus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1SeedFace.nullMinus P p q (s, 0))
      (CoefficientBassPositiveC1SeedFace.nullMinus P p' q' (s, 0)) :=
  trans_heq _ _ _ _ (c1_positive_minus_heq P p q p' q' h)
    (c1_corrected_minus_heq P p q p' q' h) s

/-- The complete plus C1 source null retains its original nested clocks. -/
theorem c1_null_plus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1SeedFace.nullPlus P p q (s, 0))
      (CoefficientBassPositiveC1SeedFace.nullPlus P p' q' (s, 0)) :=
  trans_heq _ _ _ _ (c1_positive_plus_heq P p q p' q' h)
    (c1_corrected_plus_heq P p q p' q' h) s

/-- The whole C1 source seed keeps its literal null-inverse, unit, null parentheses. -/
theorem c1_source_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1SeedFace.face P p q (0, s))
      (CoefficientBassPositiveC1SeedFace.face P p' q' (0, s)) := by
  rw [CoefficientBassPositiveC1SeedFace.face_word, CoefficientBassPositiveC1SeedFace.face_word]
  refine trans_heq _ _ _ _ ?_ ?_ s
  · exact symm_heq _ _ (c1_null_minus_heq P p q p' q' h)
  · exact trans_heq _ _ _ _ (c1_unit_heq P p q p' q' h)
      (c1_null_plus_heq P p q p' q' h)


end Quillen.PerfectComplexes.CoefficientBassNegativeSeedReference
