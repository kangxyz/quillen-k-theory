/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H0OuterReferenceNodes
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitPastingLift
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0TenNodes

/-!
# Exact raw positive-rectangle and unit-pasting outer-word bridge

Five complete original H0 nodes identify the entire Laurent movement word with the lower
TenNodes word used by the chosen unit pasting. Both normalization totals are bridged by the
actual small_composite_hom theorem. No native cancellation or new homotopy is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0OuterBridge
open CommonReferenceNerve

/-- Exactly the shared raw outer nodes, including both normalization intermediates. -/
def rawOuterFace : ⦋4⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2, 25, 26], by decide⟩
/-- Exactly the original lower five TenNodes references, not their unit-shifted copies. -/
def unitLowerFace : ⦋4⦌ ⟶ ⦋9⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2, 3, 4], by decide⟩
/-- Literal original Laurent movement word with its two binary paths and original half cut. -/
abbrev outerWord := (binaryPath (k := 4) 0 1 2).symm.trans (binaryPath 0 3 4)

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)

/-- All five dependent references agree, with both original normalization bridges explicit. -/
theorem outer_nodes (i : Fin 5) :
    BassH0Diagram.nodes P w (rawOuterFace.toOrderHom i) =
      CoefficientLaurentUnitTenNodes.nodes P w (unitLowerFace.toOrderHom i) := by
  have hi : rawOuterFace.toOrderHom i = BassH1H0Boundary.outerIndex i := by
    fin_cases i <;> rfl
  rw [hi, BassH1H0Boundary.outer_nodes]
  fin_cases i
  · rfl
  · rfl
  · change (⟨_, BinaryNormalizationSimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a)⟩ :
      CoefficientLaurentUnitTenNodes.Node P w) =
      ⟨_, BinaryNormalizationSimplex.first
        (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a) ≪≫
        BinaryNormalizationSimplex.second
          (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a)⟩
    rw [show BinaryNormalizationSimplex.first
        (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a) ≪≫
        BinaryNormalizationSimplex.second
          (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a) =
        BinaryNormalizationSimplex.total
          (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a) from
      Iso.ext (BinaryNormalizationSimplex.small_composite_hom _ _)]
  · rfl
  · change (⟨_, CoefficientLaurentUnitTenNodes.sourceIso P w ≪≫
      BinaryNormalizationSimplex.total (laurentProjection P b) (coefficientMap P w)⟩ :
      CoefficientLaurentUnitTenNodes.Node P w) =
      ⟨_, CoefficientLaurentUnitTenNodes.sourceIso P w ≪≫
        (BinaryNormalizationSimplex.first (laurentProjection P b) (coefficientMap P w) ≪≫
          BinaryNormalizationSimplex.second (laurentProjection P b) (coefficientMap P w))⟩
    rw [show BinaryNormalizationSimplex.first (laurentProjection P b) (coefficientMap P w) ≪≫
        BinaryNormalizationSimplex.second (laurentProjection P b) (coefficientMap P w) =
        BinaryNormalizationSimplex.total (laurentProjection P b) (coefficientMap P w) from
      Iso.ext (BinaryNormalizationSimplex.small_composite_hom _ _)]

/-- Whole original H0 outer path, without changing either binary route's speed. -/
theorem raw_outer_word (s : I) : embed rawOuterFace (outerWord s) =
    ProjectionRectangleParameters.T BassH0Diagram.plusFace s :=
  map_trans_values (embed rawOuterFace) _ _ _ _
    (fun t ↦ map_binaryPath rawOuterFace 0 1 2 (unitInterval.symm t))
    (map_binaryPath rawOuterFace 0 3 4) s

/-- Whole original lower unit-pasting path, with the same original parenthesization. -/
theorem unit_lower_word (s : I) : embed unitLowerFace (outerWord s) =
    (CoefficientLaurentUnitTenNodes.C0.symm.trans CoefficientLaurentUnitTenNodes.D0) s :=
  map_trans_values (embed unitLowerFace) _ _ _ _
    (fun t ↦ map_binaryPath unitLowerFace 0 1 2 (unitInterval.symm t))
    (map_binaryPath unitLowerFace 0 3 4) s

/-- The entire raw positive rectangle's Laurent movement equals the actual lower unit word. -/
theorem outer_parameter (s : I) :
    parameter (BassH0Diagram.reference P w) (BassH0Diagram.nodes P w)
      (ProjectionRectangleParameters.T BassH0Diagram.plusFace s) =
    parameter (CoefficientLaurentUnitTenNodes.source P w) (CoefficientLaurentUnitTenNodes.nodes P w)
      ((CoefficientLaurentUnitTenNodes.C0.symm.trans CoefficientLaurentUnitTenNodes.D0) s) := by
  rw [← raw_outer_word, ← unit_lower_word]
  change parameter (BassH0Diagram.reference P w) (BassH0Diagram.nodes P w)
      (StdSimplex.map rawOuterFace.toOrderHom (outerWord s)) =
    parameter (CoefficientLaurentUnitTenNodes.source P w)
      (CoefficientLaurentUnitTenNodes.nodes P w)
      (StdSimplex.map unitLowerFace.toOrderHom (outerWord s))
  rw [parameter_face, parameter_face]
  exact congrArg (fun N : Fin 5 → Node (BassH0Diagram.reference P w) ↦
    parameter (BassH0Diagram.reference P w) N (outerWord s)) (funext (outer_nodes P w))

variable {c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The same whole word is identified inside the actual C0/C1 common Laurent reference. -/
theorem anchored_outer_parameter (s : I) :
    mapParameter (BassH0Merge.anchorNode (eqToIso (BassH0Merge.reference_eq P p q)))
      (parameter (BassH0Diagram.reference P (p ≫ q)) (BassH0Diagram.nodes P (p ≫ q))
        (ProjectionRectangleParameters.T BassH0Diagram.plusFace s)) =
    mapParameter (BassH0Merge.anchorNode (eqToIso (BassH0Merge.reference_eq P p q)))
      (parameter (CoefficientLaurentUnitTenNodes.source P (p ≫ q))
        (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q))
        ((CoefficientLaurentUnitTenNodes.C0.symm.trans CoefficientLaurentUnitTenNodes.D0) s)) :=
  congrArg (mapParameter (BassH0Merge.anchorNode
    (eqToIso (BassH0Merge.reference_eq P p q)))) (outer_parameter P (p ≫ q) s)

/-- Actual direct-l specialization retains the prescribed p;q=l source-reference cast. -/
theorem actual_anchored_outer_parameter (d : Under R) (s : I) :
    mapParameter (BassH0Merge.anchorNode
      (eqToIso (CoefficientBassPositiveC0TenNodes.actualSourceReferenceEq P d)))
      (parameter (BassH0Diagram.reference P ((laurentUnderCoefficient R).app d))
        (BassH0Diagram.nodes P ((laurentUnderCoefficient R).app d))
        (ProjectionRectangleParameters.T BassH0Diagram.plusFace s)) =
    mapParameter (BassH0Merge.anchorNode
      (eqToIso (CoefficientBassPositiveC0TenNodes.actualSourceReferenceEq P d)))
      (parameter (CoefficientLaurentUnitTenNodes.source P ((laurentUnderCoefficient R).app d))
        (CoefficientLaurentUnitTenNodes.nodes P ((laurentUnderCoefficient R).app d))
        ((CoefficientLaurentUnitTenNodes.C0.symm.trans CoefficientLaurentUnitTenNodes.D0) s)) :=
  congrArg (mapParameter (BassH0Merge.anchorNode
    (eqToIso (CoefficientBassPositiveC0TenNodes.actualSourceReferenceEq P d))))
    (outer_parameter P ((laurentUnderCoefficient R).app d) s)

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0OuterBridge
