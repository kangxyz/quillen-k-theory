/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionReferenceNodes

/-! Both original projection rectangles in one family with the full common outer path identified. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH0Diagram
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)

/-- The common H0 reference formed from the Laurent coefficient map of `w` and the Laurent
projection. -/
abbrev reference := ProjectionReference.reference
  (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a)

/-- A model map together with a functor isomorphism from the common H0 reference. -/
abbrev Node := Σ F : modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
    modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj b))),
    (reference P w).functor ≅ F.functor

/-- The 18 projection-comparison nodes for a chart satisfying its source projection equation. -/
def chartNodes (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    Fin 18 → Node P w :=
  ProjectionReference.nodes (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b))
    (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) w)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α w)
      (laurentProjection P a) ha

/-- The H0 projection-comparison nodes for the positive Laurent chart. -/
abbrev plusNodes := chartNodes P w (underToLaurent R) (laurentPlus_projection P a)
/-- The H0 projection-comparison nodes for the inverse-coordinate Laurent chart. -/
abbrev minusNodes := chartNodes P w (underToLaurentInvert R) (laurentMinus_projection P a)

/-- All five outer-path nodes, including both raw intermediates, share their actual references. -/
theorem shared_nodes (i : Fin 5) : plusNodes P w (ProjectionReference.sharedIndex i) =
    minusNodes P w (ProjectionReference.sharedIndex i) :=
  ProjectionReference.two_projection_shared (polynomialProjection P a) (laurentPlus P a)
    (polynomialProjection P b) (laurentPlus P b)
    (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) w)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P (underToLaurent R)
      w)
    (laurentProjection P a) (laurentProjection P b)
    (laurentPlus_projection P a) (laurentPlus_projection P b)
    (laurentMinus P a) (laurentMinus P b)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (underToLaurentInvert R) w)
    (laurentMinus_projection P a) (laurentMinus_projection P b) i

/-- Common order retaining both entire 17-faces while sharing exactly the five outer-path nodes. -/
def nodes (i : Fin 31) : Node P w :=
  if h₀ : i.val < 14 then plusNodes P w ⟨i.val, by omega⟩ else
    if h₁ : i.val < 25 then minusNodes P w ⟨i.val - 11, by omega⟩ else
      if h₂ : i.val < 29 then plusNodes P w ⟨i.val - 11, by omega⟩ else
        minusNodes P w ⟨i.val - 13, by omega⟩

/-- The 30-simplex combining both chart diagrams with their five shared outer-path nodes. -/
def simplex : ModelSimplex
    (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj b)))) 30 :=
  ModelSimplex.ofIsos (reference P w) (fun i ↦ (nodes P w i).1) (fun i ↦ (nodes P w i).2)

/-- The vertex map placing the positive chart in the shared 31-vertex order. -/
def plusIndex (i : Fin 18) : Fin 31 :=
  ⟨if i.val < 14 then i.val else i.val + 11, by split_ifs <;> omega⟩
/-- The vertex map placing the inverse-coordinate chart in the shared 31-vertex order. -/
def minusIndex (i : Fin 18) : Fin 31 :=
  ⟨if i.val < 3 then i.val else if i.val < 16 then i.val + 11 else i.val + 13,
    by split_ifs <;> omega⟩

/-- The face inclusion recovering the positive 17-simplex from the combined H0 diagram. -/
def plusFace : ⦋17⦌ ⟶ ⦋30⦌ := SimplexCategory.Hom.mk ⟨plusIndex, by
  intro i j hij
  change (plusIndex i).val ≤ (plusIndex j).val
  dsimp [plusIndex]
  split_ifs <;> omega⟩
/-- The face inclusion recovering the inverse-coordinate 17-simplex from the combined H0 diagram. -/
def minusFace : ⦋17⦌ ⟶ ⦋30⦌ := SimplexCategory.Hom.mk ⟨minusIndex, by
  intro i j hij
  change (minusIndex i).val ≤ (minusIndex j).val
  dsimp [minusIndex]
  split_ifs <;> omega⟩

theorem plus_nodes (i : Fin 18) : nodes P w (plusFace.toOrderHom i) = plusNodes P w i := by
  fin_cases i <;> rfl

theorem minus_nodes (i : Fin 18) : nodes P w (minusFace.toOrderHom i) = minusNodes P w i := by
  fin_cases i
  · exact shared_nodes P w 0
  · exact shared_nodes P w 1
  · exact shared_nodes P w 2
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact shared_nodes P w 3
  · exact shared_nodes P w 4
  · rfl
  · rfl

/-- The complete original positive rectangle diagram is retained. -/
theorem plus_face : (simplex P w).face plusFace =
    DoubleSquareMergedSimplex.simplex (polynomialProjection P a) (laurentPlus P a)
      (polynomialProjection P b) (laurentPlus P b)
      (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
      (coefficientMap P ((laurentUnderFunctor R).map w))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) w)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P (underToLaurent
        R) w) := by
  trans ModelSimplex.ofIsos (reference P w)
    (fun i ↦ (plusNodes P w i).1) (fun i ↦ (plusNodes P w i).2)
  · unfold simplex
    rw [ModelSimplex.ofIsos_face]
    exact ModelSimplex.ofIsos_nodes_congr _ _ (plus_nodes P w)
  · exact ProjectionReference.simplex_original
      (polynomialProjection P a) (laurentPlus P a)
      (polynomialProjection P b) (laurentPlus P b)
      (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
      (coefficientMap P ((laurentUnderFunctor R).map w))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) w)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P (underToLaurent
        R) w)
      (laurentProjection P a) (laurentPlus_projection P a)

/-- The complete original inverse rectangle diagram is retained, including its distinct charts. -/
theorem minus_face : (simplex P w).face minusFace =
    DoubleSquareMergedSimplex.simplex (polynomialProjection P a) (laurentMinus P a)
      (polynomialProjection P b) (laurentMinus P b)
      (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
      (coefficientMap P ((laurentUnderFunctor R).map w))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) w)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (underToLaurentInvert R) w) := by
  trans ModelSimplex.ofIsos (reference P w)
    (fun i ↦ (minusNodes P w i).1) (fun i ↦ (minusNodes P w i).2)
  · unfold simplex
    rw [ModelSimplex.ofIsos_face]
    exact ModelSimplex.ofIsos_nodes_congr _ _ (minus_nodes P w)
  · exact ProjectionReference.simplex_original
      (polynomialProjection P a) (laurentMinus P a)
      (polynomialProjection P b) (laurentMinus P b)
      (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
      (coefficientMap P ((laurentUnderFunctor R).map w))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) w)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (underToLaurentInvert R) w)
      (laurentProjection P a) (laurentMinus_projection P a)

/-- Every positive projection-comparison parameter retains its original native value. -/
theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P w) n
      (StdSimplex.map plusFace.toOrderHom (DoubleSquareScalarPaths.rectangleParameter (r, s)), x) =
      (boundedFlatCoefficientPlusPasting P w).level n (r, (s, x)) := by
  rw [prespectrumSimplexFamily_face, plus_face]
  exact DoubleSquareScalarPaths.original_rectangle_nativeLift _ _ _ _ _ _ _ _ _ n r s x

/-- Every inverse projection-comparison parameter retains its original native value. -/
theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P w) n
      (StdSimplex.map minusFace.toOrderHom (DoubleSquareScalarPaths.rectangleParameter (r, s)), x) =
      (boundedFlatCoefficientMinusPasting P w).level n (r, (s, x)) := by
  rw [prespectrumSimplexFamily_face, minus_face]
  exact DoubleSquareScalarPaths.original_rectangle_nativeLift _ _ _ _ _ _ _ _ _ n r s x

end Quillen.PerfectComplexes.BassH0Diagram
