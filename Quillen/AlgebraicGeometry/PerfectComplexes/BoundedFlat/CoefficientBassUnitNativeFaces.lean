/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitScalarEdges
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitBottomSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassPrimitiveSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0Native

/-! The six entire original unit faces in one actual forty-eight-node native family.
Only the used primitive supports are transported; no unused local order is imposed. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassUnitNativeFaces
open CoefficientBassUnitNodes CoefficientBassUnitSupportOrder CoefficientBassUnitScalarEdges
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

private theorem supported_value {V W : Model.{u}} {p q k : ℕ}
    (S : ModelSimplex V W p) (T : ModelSimplex V W q)
    (f : Fin (p + 1) → Fin (q + 1)) (α : ⦋k⦌ ⟶ ⦋p⦌)
    (h : Monotone (f ∘ α.toOrderHom))
    (hf : T.face (BassH1Merged.supportedFace f α h) = S.face α)
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily T n (StdSimplex.map f (StdSimplex.map α.toOrderHom z), x) =
      prespectrumSimplexFamily S n (StdSimplex.map α.toOrderHom z, x) := by
  rw [← StdSimplex.map_comp]
  change prespectrumSimplexFamily T n
    (StdSimplex.map (BassH1Merged.supportedFace f α h).toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, hf, prespectrumSimplexFamily_face]

private theorem supported_point {V W : Model.{u}} {p q k : ℕ}
    (S : ModelSimplex V W p) (T : ModelSimplex V W q)
    (f : Fin (p + 1) → Fin (q + 1)) (α : ⦋k⦌ ⟶ ⦋p⦌)
    (h : Monotone (f ∘ α.toOrderHom))
    (hf : T.face (BassH1Merged.supportedFace f α h) = S.face α)
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (y : StdSimplex ℝ (Fin (p + 1)))
    (hy : StdSimplex.map α.toOrderHom z = y) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily T n (StdSimplex.map f y, x) =
      prespectrumSimplexFamily S n (y, x) := by
  subst y
  exact supported_value S T f α h hf n z x

private theorem family_simplex_congr {V W : Model.{u}} {k : ℕ}
    (S T : ModelSimplex V W k) (h : S = T) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (z, x) = prespectrumSimplexFamily T n (z, x) :=
  congrArg (fun U ↦ prespectrumSimplexFamily U n (z, x)) h

private theorem unit_face (i : Fin 6) :
    OriginalUnitSquareSupport.face i = unitTriangleFace i := by
  fin_cases i <;> rfl

private theorem plus_value (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (plusParameter (r, s), x) =
      prespectrumSimplexFamily
        ((OriginalUnitSquareSimplex.simplex (laurentPlus P a)).precomp
          (OriginalUnitSquareSimplex.sourceMap (polynomialProjection P a))) n
        (OriginalUnitSquareSimplex.squareParameter (r, s), x) := by
  obtain ⟨i, z, hz⟩ := OriginalUnitSquareSupport.square_support (r, s)
  rw [unit_face] at hz
  exact supported_point _ _ plusSideIndex (unitTriangleFace i)
    (plus_side_support i).monotone (plus_side_face P a i) n z _ hz x

private theorem minus_value (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (minusParameter (r, s), x) =
      prespectrumSimplexFamily
        ((OriginalUnitSquareSimplex.simplex (laurentMinus P a)).precomp
          (OriginalUnitSquareSimplex.sourceMap (polynomialProjection P a))) n
        (OriginalUnitSquareSimplex.squareParameter (r, s), x) := by
  obtain ⟨i, z, hz⟩ := OriginalUnitSquareSupport.square_support (r, s)
  rw [unit_face] at hz
  exact supported_point _ _ minusSideIndex (unitTriangleFace i)
    (minus_side_support i).monotone (minus_side_face P a i) n z _ hz x

/-- The whole positive face retains the original chart square and original polynomial premap. -/
theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (plusParameter (r, s), x) =
      (boundedFlatCoefficientBassIdentityPlusChart P a).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) := by
  refine (plus_value P a n r s x).trans ?_
  refine (prespectrumSimplexFamily_precomp (OriginalUnitSquareSimplex.simplex (laurentPlus P a))
    (OriginalUnitSquareSimplex.sourceMap (polynomialProjection P a)) n
    (OriginalUnitSquareSimplex.squareParameter (r, s)) x).trans ?_
  exact OriginalUnitSquareSimplex.square_native (laurentPlus P a) n r s _

/-- The inverse face retains its distinct original chart and all normalization tracks. -/
theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (minusParameter (r, s), x) =
      (boundedFlatCoefficientBassIdentityMinusChart P a).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) := by
  refine (minus_value P a n r s x).trans ?_
  refine (prespectrumSimplexFamily_precomp (OriginalUnitSquareSimplex.simplex (laurentMinus P a))
    (OriginalUnitSquareSimplex.sourceMap (polynomialProjection P a)) n
    (OriginalUnitSquareSimplex.squareParameter (r, s)) x).trans ?_
  exact OriginalUnitSquareSimplex.square_native (laurentMinus P a) n r s _

private theorem bottom_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (bottomParameter.{u} (r, t), x) =
      prespectrumSimplexFamily (CoefficientBassUnitBottom.simplex P a) n
        (CoefficientBassUnitBottom.parameter.{u} (r, t), x) := by
  obtain ⟨i, z, hz⟩ := CoefficientBassUnitBottomSupport.bottom_support.{u} (r, t)
  refine supported_point _ _ bottomIndex (bottomGridSimplexFace i)
    (bottom_grid_support i).monotone ?_ n z _ hz x
  exact (bottom_face P a i).trans
    (congrArg (fun S ↦ S.face (bottomGridSimplexFace i))
      (CoefficientBassUnitBoundaryNodes.bottom_family P a)).symm

/-- The complete bottom is Laurent identity after the unchanged original Bass comparison. -/
theorem bottom_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (bottomParameter.{u} (r, t), x) =
      (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
        (boundedFlatCoefficientLaurentIdentityHomotopy P a)).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (bottom_value P a n r t x).trans (CoefficientBassUnitBottom.native P a n r t x)

private theorem h0_plus_face (i : Fin 3) :
    BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace =
      h0TripleSimplexFace ⟨i.val, by omega⟩ := by
  ext j
  fin_cases i <;> fin_cases j <;> rfl

private theorem h0_minus_face (i : Fin 3) :
    BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace =
      h0TripleSimplexFace ⟨i.val + 3, by omega⟩ := by
  ext j
  fin_cases i <;> fin_cases j <;> rfl

private theorem h0_support (z : unitInterval × unitInterval) :
    ∃ (i : Fin 6) (w : StdSimplex ℝ (Fin 8)),
      StdSimplex.map (h0TripleSimplexFace i).toOrderHom w = BassH0Diagram.parameter z := by
  obtain ⟨α, hα, i, w, hw⟩ := BassPrimitiveSupport.h0_support z
  rcases Set.mem_insert_iff.mp hα with hα | hα
  · subst α
    rw [h0_plus_face] at hw
    exact ⟨_, w, hw⟩
  · have hα := Set.mem_singleton_iff.mp hα
    subst α
    rw [h0_minus_face] at hw
    exact ⟨_, w, hw⟩

private theorem h0_value (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (h0Parameter (s, t), x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P (𝟙 a)) n
        (BassH0Diagram.parameter (s, t), x) := by
  obtain ⟨i, z, hz⟩ := h0_support (s, t)
  exact supported_point _ _ CoefficientBassUnitSupportOrder.h0Index (h0TripleSimplexFace i)
    (h0_triple_support i).monotone (h0_face P a i) n z _ hz x

/-- The entire initial face is the literal original comparison at the coefficient identity. -/
theorem h0_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (h0Parameter (s, t), x) =
      (boundedFlatCoefficientBassComparisonHomotopy P (𝟙 a)).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (h0_value P a n s t x).trans (BassH0Diagram.native P (𝟙 a) n s t x)

/-- The complete top is the constructed original polynomial-span identity after the Bass map. -/
theorem top_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (topParameter.{u} (r, t), x) =
      ((boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a).postcomp
        (boundedFlatCoefficientBassSquareComparison P a)).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  refine (prespectrumSimplexFamily_face (simplex P a) topFace n
    (CoefficientPolynomialSpanUnitTop.topParameter.{u} (r, t)) x).trans ?_
  refine (family_simplex_congr _ _ (top_face P a) n _ x).trans ?_
  exact CoefficientPolynomialSpanUnitTop.top_native P a n r t x

/-- The terminal face is the unpaused original identity track, independent of comparison time. -/
theorem identity_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (identityParameter (s, t), x) =
      (coneSquareIdentityTrack (boundedFlatCoefficientBassSquareComparison P a)).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  refine (prespectrumSimplexFamily_face (simplex P a) topFace n
    (CoefficientPolynomialSpanUnitTop.middleEnd t) x).trans ?_
  refine (family_simplex_congr _ _ (top_face P a) n _ x).trans ?_
  exact CoefficientPolynomialSpanUnitTop.cylinder_native P a n t x

/-- Every common simplex point fixes the unchanged original based point. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 48)) :
    prespectrumSimplexFamily (simplex P a) n
      (z, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj a)))).point n :=
  prespectrumSimplexFamily_point (simplex P a) n z

/-- Original structure time remains independent of every scalar common-simplex point. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 48))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (t : unitInterval) :
    prespectrumSimplexFamily (simplex P a) (n + 1)
      (z, (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, a)))).structureMap n x t) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj a)))).structureMap n
          (prespectrumSimplexFamily (simplex P a) n (z, x)) t :=
  prespectrumSimplexFamily_structure (simplex P a) n z x t

end Quillen.PerfectComplexes.CoefficientBassUnitNativeFaces
