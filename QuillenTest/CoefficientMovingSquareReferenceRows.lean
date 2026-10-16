/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientMovingSquareReferenceRows

/-! Actual full reference rows, primitive-only supports and original whole moving-square paths. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen Quillen.PerfectComplexes Quillen.PerfectComplexes.CoefficientMovingSquareRows
open Quillen.PerfectComplexes.BassH0Merge Quillen.PerfectComplexes.BassH1Join
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.CoefficientMovingSquareReferenceRows
section Geometric
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- All direct nodes retain both intermediate normalizations and the actual outer transport. -/
theorem direct_nodes (i : Fin 5) :
    nodes p q p' q' a b c hp hq (outerRow i) =
      anchorNode (outerAnchor p q p' q' a b c hp hq)
        (NativeSquareFiveSimplex.nodes (q' ≫ p') a c (q ≫ p)
          (DoubleSquareTrack.total_eq p q p' q' a b c hp hq) i) :=
  outer_row_nodes p q p' q' a b c hp hq i

/-- Every postcomposed first-square node retains its entire dependent reference. -/
theorem first_nodes (i : Fin 5) :
    nodes p q p' q' a b c hp hq (firstRow i) =
      postReferenceNode (reference p q c) (normalizedMap q')
        (firstAnchor p q p' q' a b c hp hq)
        (NativeSquareFiveSimplex.nodes p' a b p hp.symm i) :=
  first_row_nodes p q p' q' a b c hp hq i

/-- Every precomposed second-square node retains its entire dependent reference. -/
theorem second_nodes (i : Fin 5) :
    nodes p q p' q' a b c hp hq (secondRow i) =
      preReferenceNode (reference p q c) (normalizedMap p)
        (secondAnchor p q q' b c hq)
        (NativeSquareFiveSimplex.nodes q' b c q hq.symm i) :=
  second_row_nodes p q p' q' a b c hp hq i

/-- The moving source side is the original two-stage binary composition after c. -/
theorem source_side (i : Fin 3) :
    nodes p q p' q' a b c hp hq (sourceSide i) =
      postReferenceNode (reference p q c) (normalizedMap c)
        (H := BinaryNormalizationSimplex.sourceMap q p)
        (BinaryNormalizationSimplex.total c (q ≫ p)) (binaryNodes q p i) :=
  source_side_nodes p q p' q' a b c hp hq i

/-- The moving target side is the original two-stage binary composition under a. -/
theorem target_side (i : Fin 3) :
    nodes p q p' q' a b c hp hq (targetSide i) =
      preReferenceNode (reference p q c) (normalizedMap a)
        (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
          NormalizedTripleSimplex.rightFirst q' p' a) (binaryNodes q' p' i) :=
  target_side_nodes p q p' q' a b c hp hq i

/-- Literal composite maps may be transported only with their actual geometric equalities. -/
theorem direct_cast_nodes (r : C ⟶ A) (r' : C' ⟶ A')
    (hr : r = q ≫ p) (hr' : r' = q' ≫ p') (h : r' ≫ a = c ≫ r) (i : Fin 5) :
    nodes p q p' q' a b c hp hq (outerRow i) =
      anchorNode (eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedFlatNormalizedPullback
          (h.trans (congrArg (fun k ↦ c ≫ k) hr)).symm)))
        (NativeSquareFiveSimplex.nodes r' a c r h i) :=
  outer_row_nodes_cast p q p' q' a b c hp hq r r' hr hr' h i
end Geometric

/-- The direct row is deliberately nonmonotone, while every used primitive edge is ordered. -/
theorem primitive_support_only (j : Fin 3) (i : Fin 4) :
    ¬ Monotone outerRow ∧
      Monotone ((![outerRow, firstRow, secondRow] j) ∘ (BassH1Support.edgeFace i).toOrderHom) :=
  ⟨outerRow_not_monotone, primitive_rows_monotone j i⟩

/-- Both terminal halves preserve their complete original four-edge path parameters. -/
theorem terminal_halves (s : unitInterval) :
    DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, lower s) =
      StdSimplex.map firstRow (NativeSquareFiveSimplex.parameter s) ∧
    DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, upper s) =
      StdSimplex.map secondRow (NativeSquareFiveSimplex.parameter s) :=
  ⟨moving_one_lower_row s, moving_one_upper_row s⟩

/-- Both whole moving sides retain the original binary normalization parameters. -/
theorem moving_sides (q : unitInterval) :
    DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, 0) =
      StdSimplex.map targetSide (binaryPath (k := 2) 0 1 2 q) ∧
    DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, 1) =
      StdSimplex.map sourceSide (binaryPath (k := 2) 0 1 2 q) :=
  ⟨moving_left_row q, moving_right_row q⟩

/-- Inverse polynomial time swaps the two original terminal halves, without changing speed. -/
theorem inverse_terminal_halves (s : unitInterval) :
    DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, unitInterval.symm (lower s)) =
      StdSimplex.map secondRow (NativeSquareFiveSimplex.parameter (unitInterval.symm s)) ∧
    DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, unitInterval.symm (upper s)) =
      StdSimplex.map firstRow (NativeSquareFiveSimplex.parameter (unitInterval.symm s)) := by
  have hl : unitInterval.symm (lower s) = upper (unitInterval.symm s) := by
    apply Subtype.ext
    change 1 - (s : ℝ) / 2 = ((1 - (s : ℝ)) + 1) / 2
    ring
  have hu : unitInterval.symm (upper s) = lower (unitInterval.symm s) := by
    apply Subtype.ext
    change 1 - ((s : ℝ) + 1) / 2 = (1 - (s : ℝ)) / 2
    ring
  rw [hl, hu]
  exact ⟨moving_one_upper_row _, moving_one_lower_row _⟩

section Coefficients
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {M N : Under R ⥤ Under R} (α : M ⟶ N)
  {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
open CoefficientTransformationComposition

/-- The direct full nodes use the actual functor-applied composite coefficient maps. -/
theorem coefficient_direct_full_nodes (i : Fin 5) :
    nodes (coefficientMap P (M.map u)) (coefficientMap P (M.map v))
      (coefficientMap P (N.map u)) (coefficientMap P (N.map v))
      (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
      (coefficientMap P (α.app c))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α u).symm
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v).symm
        (outerRow i) =
    anchorNode (eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
      (congrArg boundedFlatNormalizedPullback
        ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α
          (u ≫ v)).trans
          (congrArg (fun k ↦ coefficientMap P (α.app c) ≫ k)
            ((congrArg (coefficientMap P) (M.map_comp u v)).trans
              (coefficientMap_comp P (M.map u) (M.map v))))).symm)))
      (NativeSquareFiveSimplex.nodes (coefficientMap P (N.map (u ≫ v)))
        (coefficientMap P (α.app a)) (coefficientMap P (α.app c))
        (coefficientMap P (M.map (u ≫ v)))
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α
          (u ≫ v)) i) :=
  outer_row_nodes_cast _ _ _ _ _ _ _ _ _ _ _
    ((congrArg (coefficientMap P) (M.map_comp u v)).trans
      (coefficientMap_comp P (M.map u) (M.map v)))
    ((congrArg (coefficientMap P) (N.map_comp u v)).trans
      (coefficientMap_comp P (N.map u) (N.map v)))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α (u ≫ v)) i

/-- The relabeled direct row evaluates to the literal original composite-arrow square. -/
theorem original_direct_family (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, M.obj a)))).space n) :
    prespectrumSimplexFamily (Scalar.simplex P α u v) n
      (StdSimplex.map outerRow (NativeSquareFiveSimplex.parameter s), x) =
      (square P α (u ≫ v)).level n (s, x) := by
  rw [← moving_zero_row, Scalar.movingSquare_native]
  exact (movingSquare P α u v).at_zero n s x

/-- The whole first half still evaluates to the original postcomposed square at every level. -/
theorem original_first_family (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, M.obj a)))).space n) :
    prespectrumSimplexFamily (Scalar.simplex P α u v) n
      (StdSimplex.map firstRow (NativeSquareFiveSimplex.parameter s), x) =
      ((square P α u).postcomp
        (boundedFlatPerfectPrespectrumMap (coefficientMap P (N.map v)))).level n (s, x) := by
  rw [← moving_one_lower_row, Scalar.movingSquare_native,
    (movingSquare P α u v).at_one]
  exact Quillen.LoopPrespectrum.Homotopy.trans_lower_cell _ _ n s x

/-- The whole second half keeps the original precomposition and its endpoint casts. -/
theorem original_second_family (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, M.obj a)))).space n) :
    prespectrumSimplexFamily (Scalar.simplex P α u v) n
      (StdSimplex.map secondRow (NativeSquareFiveSimplex.parameter s), x) =
      (square P α v).level n (s,
        (boundedFlatPerfectPrespectrumMap (coefficientMap P (M.map u))).map n x) := by
  rw [← moving_one_upper_row, Scalar.movingSquare_native,
    (movingSquare P α u v).at_one]
  exact Quillen.LoopPrespectrum.Homotopy.trans_upper_cell _ _ n s x

/-- Level zero retains every original input on the entire moving source side. -/
theorem original_source_zero (q : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, M.obj a)))).space 0) :
    prespectrumSimplexFamily (Scalar.simplex P α u v) 0
      (StdSimplex.map sourceSide (binaryPath (k := 2) 0 1 2 q), x) =
      (sourceComposition P α u v).level 0 (q, x) := by
  rw [← moving_right_row, Scalar.movingSquare_native]
  exact (movingSquare P α u v).right 0 q x

/-- The target side retains arbitrary levels and original input points. -/
theorem original_target_family (n : ℕ) (q : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, M.obj a)))).space n) :
    prespectrumSimplexFamily (Scalar.simplex P α u v) n
      (StdSimplex.map targetSide (binaryPath (k := 2) 0 1 2 q), x) =
      (targetComposition P α u v).level n (q, x) := by
  rw [← moving_left_row, Scalar.movingSquare_native]
  exact (movingSquare P α u v).left n q x
end Coefficients
end QuillenTest.CoefficientMovingSquareReferenceRows
