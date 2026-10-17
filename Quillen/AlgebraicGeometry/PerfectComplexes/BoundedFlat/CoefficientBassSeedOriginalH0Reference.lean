/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetH0Chart
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanMReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetMovingNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierAttachment

/-! The original chosen carrier sheets retain their complete whole-input reference triangle. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedOriginalH0Reference
open BassH0Merge CoefficientBassSeedCarrierLaurentReference
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R}
  (p : a ⟶ b) (q : b ⟶ c)

/-- The original polynomial side-row normalization supplies the full sheet reference. -/
def polynomialIso :
    ((inputReference P p q) ≫ normalizedMap (polynomialProjection P c)).functor ≅
      (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q).functor :=
  CoefficientBassSpanCompositionReference.squareAnchor P p q ≪≫
    BassMOuterJoin.movingSideBaseIso P p q

/-- The ordinary attachment triangle uses the original full moving-side reference equality. -/
theorem ordinary_triangle :
    referenceIso P p q ≪≫ CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q =
      isoWhiskerLeft (inputReference P p q).functor
        (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P c)) ≪≫
          isoWhiskerRight (polynomialIso P p q) (normalizedMap (laurentPlus P c)).functor := by
  rw [← CoefficientBassPositiveC0CarrierAttachment.side_anchor]
  change BassMWholeConeCarrier.referenceIso P p q ≪≫
      (BassMReferences.movingIso P p q (underToLaurent R) (laurentPlus_projection P c) ≪≫
        isoWhiskerRight (BassMOuterJoin.movingSideBaseIso P p q)
          (normalizedMap (laurentPlus P c)).functor) = _
  rw [← Iso.trans_assoc, CoefficientBassSpanCompositionReference.moving_chart_anchor]
  simp only [polynomialIso, isoWhiskerRight_trans, Iso.trans_assoc]
  rfl


open CommonReferenceNerve
open scoped Simplicial Topology

/-- Every original ordinary sheet node attaches to the exact whole-input positive chart. -/
theorem ordinary_node
    (N₀ : Node (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)) :
    CommonReferenceProduct.reanchor (referenceIso P p q)
        (CoefficientBassPositiveC1BoundaryLift.ordinaryAttachNode P p q N₀) =
      BassProjectionPath.WholeReference.chartAttachmentNode P c (inputReference P p q)
        (underToLaurent R) (laurentPlus_projection P c)
        (CommonReferenceProduct.reanchor (polynomialIso P p q) N₀) := by
  rcases N₀ with ⟨K, ρ⟩
  change (⟨K ≫ normalizedMap (laurentPlus P c), referenceIso P p q ≪≫
      (CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q ≪≫
        isoWhiskerRight ρ (normalizedMap (laurentPlus P c)).functor)⟩ :
      Node (BassProjectionPath.WholeReference.reference P c (inputReference P p q))) =
    ⟨K ≫ normalizedMap (laurentPlus P c),
      isoWhiskerLeft (inputReference P p q).functor
        (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P c)) ≪≫
          isoWhiskerRight (polynomialIso P p q ≪≫ ρ)
            (normalizedMap (laurentPlus P c)).functor⟩
  apply congrArg (fun e :
    (BassProjectionPath.WholeReference.reference P c (inputReference P p q)).functor ≅
      (K ≫ normalizedMap (laurentPlus P c)).functor ↦
        (⟨K ≫ normalizedMap (laurentPlus P c), e⟩ :
          Node (BassProjectionPath.WholeReference.reference P c (inputReference P p q))))
  rw [← Iso.trans_assoc, ordinary_triangle, isoWhiskerRight_trans, Iso.trans_assoc]

/-- The whole original sheet attachment uses the same reference triangle at every point. -/
theorem ordinary_parameter
    (y : |nerve (Codiscrete
      (Node (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)))|) :
    mapParameter (CommonReferenceProduct.reanchor (referenceIso P p q))
        (mapParameter (CoefficientBassPositiveC1BoundaryLift.ordinaryAttachNode P p q) y) =
      mapParameter (BassProjectionPath.WholeReference.chartAttachmentNode P c
        (inputReference P p q) (underToLaurent R) (laurentPlus_projection P c))
        (mapParameter (CommonReferenceProduct.reanchor (polynomialIso P p q)) y) := by
  obtain ⟨k, ns, z, rfl⟩ := exists_parameter
    (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q) y
  rw [mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ parameter
    (BassProjectionPath.WholeReference.reference P c (inputReference P p q)) ns z)
  funext i
  exact ordinary_node P p q (ns i)


open Quillen.FunctorIdentityAutomorphism LaurentUnitReferenceSpecialization

/-- The complete original common unit transports to the same actual Laurent unit action. -/
theorem unit_triangle :
    referenceIso P p q ≪≫ commonUnit P p q =
      onFunctor (BassProjectionPath.WholeReference.reference P c
        (inputReference P p q)).functor (smallUnit P c) ≪≫ referenceIso P p q := by
  rw [commonUnit_eq_action]
  exact (GlobalUnitReferenceNaturality.reference_intertwine
    (op P, (laurentUnderFunctor R).obj c) (laurentUnit P c) _ _
    (referenceIso P p q)).symm

/-- The original shifted attachment retains the exact whole-input Laurent unit action. -/
theorem shifted_node
    (N₀ : Node (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)) :
    CommonReferenceProduct.reanchor (referenceIso P p q)
        (attachPostcompNode (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)
          (normalizedMap (laurentPlus P c))
          (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q)
          (commonUnit P p q ≪≫ CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q) N₀) =
      CommonReferenceProduct.reanchor
        (onFunctor (BassProjectionPath.WholeReference.reference P c
          (inputReference P p q)).functor (smallUnit P c))
        (BassProjectionPath.WholeReference.chartAttachmentNode P c (inputReference P p q)
          (underToLaurent R) (laurentPlus_projection P c)
          (CommonReferenceProduct.reanchor (polynomialIso P p q) N₀)) := by
  rw [← ordinary_node P p q N₀]
  rcases N₀ with ⟨K, ρ⟩
  change (⟨K ≫ normalizedMap (laurentPlus P c), referenceIso P p q ≪≫
      ((commonUnit P p q ≪≫ CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q) ≪≫
        isoWhiskerRight ρ (normalizedMap (laurentPlus P c)).functor)⟩ :
      Node (BassProjectionPath.WholeReference.reference P c (inputReference P p q))) =
    ⟨K ≫ normalizedMap (laurentPlus P c),
      onFunctor (BassProjectionPath.WholeReference.reference P c
        (inputReference P p q)).functor (smallUnit P c) ≪≫
        (referenceIso P p q ≪≫ (CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q ≪≫
          isoWhiskerRight ρ (normalizedMap (laurentPlus P c)).functor))⟩
  apply congrArg (fun e :
    (BassProjectionPath.WholeReference.reference P c (inputReference P p q)).functor ≅
      (K ≫ normalizedMap (laurentPlus P c)).functor ↦
        (⟨K ≫ normalizedMap (laurentPlus P c), e⟩ :
          Node (BassProjectionPath.WholeReference.reference P c (inputReference P p q))))
  simp only [← Iso.trans_assoc]
  rw [unit_triangle]


/-- The entire shifted attachment maps to the actual unit-shifted whole-input chart. -/
theorem shifted_parameter
    (y : |nerve (Codiscrete
      (Node (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)))|) :
    mapParameter (CommonReferenceProduct.reanchor (referenceIso P p q))
        (mapParameter
          (attachPostcompNode (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)
            (normalizedMap (laurentPlus P c))
            (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q)
            (commonUnit P p q ≪≫ CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q)) y) =
      mapParameter (CommonReferenceProduct.reanchor
        (onFunctor (BassProjectionPath.WholeReference.reference P c
          (inputReference P p q)).functor (smallUnit P c)))
        (mapParameter (BassProjectionPath.WholeReference.chartAttachmentNode P c
          (inputReference P p q) (underToLaurent R) (laurentPlus_projection P c))
          (mapParameter (CommonReferenceProduct.reanchor (polynomialIso P p q)) y)) := by
  obtain ⟨k, ns, z, rfl⟩ := exists_parameter
    (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q) y
  rw [mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ parameter
    (BassProjectionPath.WholeReference.reference P c (inputReference P p q)) ns z)
  funext i
  exact shifted_node P p q (ns i)


/-- The original ordinary anchor is the whole-input anchor followed by its polynomial reference. -/
theorem source_anchor :
    CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q =
      CoefficientBassSeedTargetH0Chart.sourceAnchor P (inputReference P p q)
        (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (referenceIso P p q) ≪≫
          isoWhiskerRight (polynomialIso P p q) (normalizedMap (laurentPlus P c)).functor := by
  have h := congrArg (fun e ↦ (referenceIso P p q).symm ≪≫ e) (ordinary_triangle P p q)
  simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] at h
  calc
    _ = (referenceIso P p q).symm ≪≫
        isoWhiskerLeft (inputReference P p q).functor
          (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P c)) ≪≫
            isoWhiskerRight (polynomialIso P p q) (normalizedMap (laurentPlus P c)).functor :=
      h.trans (Iso.trans_assoc _ _ _)
    _ = _ := by
      apply Iso.ext
      ext X
      simp only [CoefficientBassSeedTargetH0Chart.sourceAnchor, Iso.trans_hom,
        NatTrans.comp_app, Iso.symm_hom, Functor.associator_inv_app,
        Category.assoc]
      dsimp only [CoefficientBassSeedTargetChartAttachment.Ja]
      erw [Category.id_comp]

variable {d : Under R} (f : c ⟶ d)

/-- Every original chosen-sheet moving node has its exact whole-input H0 chart image. -/
theorem moving_node
    (N₀ : Node (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)) (i : Fin 5) :
    CommonReferenceProduct.reanchor
        (CoefficientBassSeedTargetH0Reference.referenceBridge P f (inputReference P p q)
          (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (referenceIso P p q))
        (CoefficientBassSeedTargetChartAttachment.movingNode P f
          (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)
          (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q)
          (CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q) N₀ i) =
      BassProjectionPath.WholeReference.FourEdge.Target.chartNodes P f (inputReference P p q)
        (underToLaurent R) (laurentPlus_projection P c)
        (CommonReferenceProduct.reanchor (polynomialIso P p q) N₀) i := by
  have h := CoefficientBassSeedTargetMovingNormalization.moving_node_change P f
    (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)
    (inputReference P p q ≫ normalizedMap (polynomialProjection P c))
    (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (polynomialIso P p q)
    (CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q)
    (CoefficientBassSeedTargetH0Chart.sourceAnchor P (inputReference P p q)
      (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (referenceIso P p q))
    (source_anchor P p q) N₀ i
  exact (congrArg (CommonReferenceProduct.reanchor
    (CoefficientBassSeedTargetH0Reference.referenceBridge P f (inputReference P p q)
      (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (referenceIso P p q))) h).trans
    (CoefficientBassSeedTargetH0Chart.moving_nodes P f (inputReference P p q)
      (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (referenceIso P p q)
      (CommonReferenceProduct.reanchor (polynomialIso P p q) N₀) i)


open CoefficientBassSeedTargetChartAttachment
open BassProjectionPath.WholeReference.FourEdge
open scoped unitInterval

private theorem parameter_square {V₀ W₀ V₁ W₁ V₂ W₂ V₃ W₃ : Model.{u}}
    (E₀ : V₀ ⟶ W₀) (E₁ : V₁ ⟶ W₁) (F₀ : V₂ ⟶ W₂) (F₁ : V₃ ⟶ W₃) {q₀ : ℕ}
    (g₀ : Node E₀ → Fin (q₀ + 1) → Node F₀)
    (g₁ : Node E₁ → Fin (q₀ + 1) → Node F₁)
    (e : Node E₀ → Node E₁) (h : Node F₀ → Node F₁)
    (hs : ∀ N i, h (g₀ N i) = g₁ (e N) i)
    (y : |nerve (Codiscrete (Node E₀))|) (z : Convexity.StdSimplex ℝ (Fin (q₀ + 1))) :
    mapParameter h (FiniteParameter.parameter E₀ F₀ g₀ (y, z)) =
      FiniteParameter.parameter E₁ F₁ g₁ (mapParameter e y, z) := by
  obtain ⟨k, N₀, w, rfl⟩ := exists_parameter E₀ y
  rw [FiniteParameter.parameter_characteristic, mapParameter_parameter,
    mapParameter_parameter, FiniteParameter.parameter_characteristic]
  apply congrArg (fun ns ↦ parameter F₁ ns (Quillen.SimplexGrid.parameter k q₀ (w, z)))
  funext i
  exact hs (N₀ ((Quillen.SimplexGrid.indexEquiv k q₀).symm i).1)
    ((Quillen.SimplexGrid.indexEquiv k q₀).symm i).2

/-- The actual original moving sheet agrees with the whole H0 chart at its original clock. -/
theorem moving_family
    (y : |nerve (Codiscrete
      (Node (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)))|) (t : I) :
    mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassSeedTargetH0Reference.referenceBridge P f (inputReference P p q)
          (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (referenceIso P p q)))
        (moving P f (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)
          (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q)
          (CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q) (y, t)) =
      Target.chart P f (inputReference P p q) (underToLaurent R) (laurentPlus_projection P c)
        (mapParameter (CommonReferenceProduct.reanchor (polynomialIso P p q)) y, t) := by
  change mapParameter _ (FiniteParameter.parameter _ _ _
    (y, NativeSquareFiveSimplex.parameter t)) =
      FiniteParameter.parameter _ _ _
        (mapParameter _ y, NativeSquareFiveSimplex.parameter t)
  exact parameter_square _ _ _ _ _ _ _ _ (moving_node P p q f) y
    (NativeSquareFiveSimplex.parameter t)


/-- The original shifted moving node keeps the actual target Laurent unit in the H0 reference. -/
theorem shifted_moving_node
    (N₀ : Node (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)) (i : Fin 5) :
    CommonReferenceProduct.reanchor
        (CoefficientBassSeedTargetH0Reference.referenceBridge P f (inputReference P p q)
          (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (referenceIso P p q))
        (movingNode P f (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)
          (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q)
          (commonUnit P p q ≪≫ CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q) N₀ i) =
      CommonReferenceProduct.reanchor
        (onFunctor (Target.reference P f (inputReference P p q)).functor (smallUnit P d))
        (Target.chartNodes P f (inputReference P p q) (underToLaurent R)
          (laurentPlus_projection P c)
          (CommonReferenceProduct.reanchor (polynomialIso P p q) N₀) i) := by
  have hs := congrArg (fun e ↦ commonUnit P p q ≪≫ e) (source_anchor P p q)
  simp only [← Iso.trans_assoc] at hs
  have h := CoefficientBassSeedTargetMovingNormalization.moving_node_change P f
    (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)
    (inputReference P p q ≫ normalizedMap (polynomialProjection P c))
    (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (polynomialIso P p q)
    (commonUnit P p q ≪≫ CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q)
    (commonUnit P p q ≪≫ CoefficientBassSeedTargetH0Chart.sourceAnchor P (inputReference P p q)
      (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (referenceIso P p q))
    hs N₀ i
  have ht := (congrArg (CommonReferenceProduct.reanchor
    (CoefficientBassSeedTargetH0Reference.referenceBridge P f (inputReference P p q)
      (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (referenceIso P p q))) h).trans
    (CoefficientBassSeedTargetH0Chart.shifted_moving_nodes P f (inputReference P p q)
      (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (referenceIso P p q)
      (commonUnit P p q) (CommonReferenceProduct.reanchor (polynomialIso P p q) N₀) i)
  simpa only [commonUnit_eq_action, CoefficientBassSeedTargetH0Chart.shiftedReference_unit] using ht

/-- The full original shifted sheet follows the H0 chart at the unchanged moving-square clock. -/
theorem shifted_moving_family
    (y : |nerve (Codiscrete
      (Node (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)))|) (t : I) :
    mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassSeedTargetH0Reference.referenceBridge P f (inputReference P p q)
          (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) (referenceIso P p q)))
        (moving P f (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q)
          (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q)
          (commonUnit P p q ≪≫ CoefficientBassPositiveC1BoundaryLift.ordinaryAnchor P p q) (y, t)) =
      mapParameter (CommonReferenceProduct.reanchor
        (onFunctor (Target.reference P f (inputReference P p q)).functor (smallUnit P d)))
        (Target.chart P f (inputReference P p q) (underToLaurent R) (laurentPlus_projection P c)
          (mapParameter (CommonReferenceProduct.reanchor (polynomialIso P p q)) y, t)) := by
  obtain ⟨k, ns, z, rfl⟩ := exists_parameter
    (CoefficientBassPositiveC1BoundaryLift.polynomialReference P p q) y
  change mapParameter _ (FiniteParameter.parameter _ _ _
    (parameter _ ns z, NativeSquareFiveSimplex.parameter t)) =
      mapParameter _ (FiniteParameter.parameter _ _ _
        (mapParameter _ (parameter _ ns z), NativeSquareFiveSimplex.parameter t))
  rw [FiniteParameter.parameter_characteristic, mapParameter_parameter,
    mapParameter_parameter, FiniteParameter.parameter_characteristic, mapParameter_parameter]
  apply congrArg (fun ns ↦ parameter (Target.reference P f (inputReference P p q)) ns
    (Quillen.SimplexGrid.parameter k 4 (z, NativeSquareFiveSimplex.parameter t)))
  funext i
  exact shifted_moving_node P p q f (ns ((Quillen.SimplexGrid.indexEquiv k 4).symm i).1)
    ((Quillen.SimplexGrid.indexEquiv k 4).symm i).2

end Quillen.PerfectComplexes.CoefficientBassSeedOriginalH0Reference
