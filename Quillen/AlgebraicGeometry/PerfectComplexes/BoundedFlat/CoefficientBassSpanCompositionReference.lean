/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPrisms
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily

/-!
# The original polynomial moving square in its source-composition reference

The inverse original binary total reanchors all eighteen full nodes. Its source side is
literally the polynomial postcomposition of the original coefficient binary family. The
other side keeps the last-triple geometric transport and the polynomial composition family.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
open BassH0Merge BassH1Join CommonReferenceNerve
attribute [local irreducible] boundedFlatNormalizedPullback
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original coefficient binary source, before its polynomial postcomposition. -/
abbrev coefficientReference :=
  BinaryNormalizationSimplex.sourceMap (coefficientMap P q) (coefficientMap P p)

/-- The literal polynomial projection at the terminal coefficient object. -/
abbrev polynomialMap := normalizedMap (polynomialProjection P c)

/-- The exact source-composition reference of the polynomial seam. -/
abbrev polynomialReference := coefficientReference P p q ≫ polynomialMap P (c := c)

/-- All three original coefficient normalization nodes. -/
abbrev coefficientNodes : Fin 3 → CommonReferenceNerve.Node (coefficientReference P p q) :=
  binaryNodes (coefficientMap P q) (coefficientMap P p)

/-- The unchanged eighteen-node coefficient moving square. -/
abbrev originalNodes := BassMWholeNerve.movingSquareNodes P (polynomialUnderCoefficient R) p q

/-- Its original right-associated geometric source. -/
abbrev originalReference :=
  BassMWholeNerve.movingSquareSource P (polynomialUnderCoefficient R) p q

/-- Invert the original binary total, retaining its normalization and geometric components. -/
def squareAnchor : (polynomialReference P p q).functor ≅ (originalReference P p q).functor :=
  (BinaryNormalizationSimplex.total (polynomialProjection P c)
    (coefficientMap P q ≫ coefficientMap P p)).symm

/-- All eighteen complete old nodes in the literal polynomial-source reference. -/
def squareNodes : Fin 18 → CommonReferenceNerve.Node (polynomialReference P p q) :=
  ModelSimplex.reanchorNodes (squareAnchor P p q) (originalNodes P p q)

/-- The whole source-composition row cancels only the original total and its inverse. -/
theorem square_source_nodes (i : Fin 3) :
    squareNodes P p q (CoefficientMovingSquareRows.sourceSide i) =
      postcompNode (polynomialMap P (c := c)) (coefficientNodes P p q i) := by
  have h : originalNodes P p q (CoefficientMovingSquareRows.sourceSide i) =
      postReferenceNode (originalReference P p q) (polynomialMap P (c := c))
        (H := coefficientReference P p q)
        (BinaryNormalizationSimplex.total (polynomialProjection P c)
          (coefficientMap P q ≫ coefficientMap P p)) (coefficientNodes P p q i) :=
    CoefficientMovingSquareRows.source_side_nodes
      (coefficientMap P p) (coefficientMap P q)
      (coefficientMap P ((polynomialUnderFunctor R).map p))
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
      (coefficientMap_naturality P (polynomialUnderCoefficient R) p).symm
      (coefficientMap_naturality P (polynomialUnderCoefficient R) q).symm i
  calc
    _ = anchorNode (squareAnchor P p q)
        (originalNodes P p q (CoefficientMovingSquareRows.sourceSide i)) := rfl
    _ = anchorNode (squareAnchor P p q)
        (postReferenceNode (originalReference P p q) (polynomialMap P (c := c))
          (H := coefficientReference P p q)
          (BinaryNormalizationSimplex.total (polynomialProjection P c)
            (coefficientMap P q ≫ coefficientMap P p)) (coefficientNodes P p q i)) :=
      congrArg (anchorNode (squareAnchor P p q)) h
    _ = _ := by
      rw [anchor_post_node]
      simp only [squareAnchor, Iso.symm_self_id, postReferenceNode, postcompNode, Iso.refl_trans]

/-- The target binary reference is the original polynomial coefficient composition. -/
abbrev targetReference := coefficientReference P
  ((polynomialUnderFunctor R).map p) ((polynomialUnderFunctor R).map q)

/-- The left-side anchor retains the actual last-triple geometric source cast. -/
def targetAnchor : (polynomialReference P p q).functor ≅
    (normalizedMap (polynomialProjection P a) ≫ targetReference P p q).functor :=
  squareAnchor P p q ≪≫
    (DoubleSquareCommonSimplex.lastSourceIso
      (coefficientMap P p) (coefficientMap P q)
      (coefficientMap P ((polynomialUnderFunctor R).map p))
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
      (coefficientMap_naturality P (polynomialUnderCoefficient R) p).symm
      (coefficientMap_naturality P (polynomialUnderCoefficient R) q).symm ≪≫
        NormalizedTripleSimplex.rightFirst
          (coefficientMap P ((polynomialUnderFunctor R).map q))
          (coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a))

/-- The actual target-side attachment acts on every polynomial-composition node. -/
def targetAttachmentNode (N : CommonReferenceNerve.Node (targetReference P p q)) :
    CommonReferenceNerve.Node (polynomialReference P p q) :=
  preReferenceNode (polynomialReference P p q) (normalizedMap (polynomialProjection P a))
    (targetAnchor P p q) N

/-- All three target-side nodes retain their original full geometric reference. -/
theorem square_target_nodes (i : Fin 3) :
    squareNodes P p q (CoefficientMovingSquareRows.targetSide i) =
      targetAttachmentNode P p q
        (coefficientNodes P ((polynomialUnderFunctor R).map p)
          ((polynomialUnderFunctor R).map q) i) := by
  have h := CoefficientMovingSquareRows.target_side_nodes
    (coefficientMap P p) (coefficientMap P q)
    (coefficientMap P ((polynomialUnderFunctor R).map p))
    (coefficientMap P ((polynomialUnderFunctor R).map q))
    (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
    (coefficientMap_naturality P (polynomialUnderCoefficient R) p).symm
    (coefficientMap_naturality P (polynomialUnderCoefficient R) q).symm i
  exact (congrArg (anchorNode (squareAnchor P p q)) h).trans
    (BassMOuterJoin.anchor_pre_node (normalizedMap (polynomialProjection P a))
      (squareAnchor P p q) _ _)

/-- The unchanged two-half coefficient composition path. -/
def coefficientPath : C(unitInterval,
    |nerve (Codiscrete (CommonReferenceNerve.Node (coefficientReference P p q)))|) :=
  (CommonReferenceNerve.parameter _ (coefficientNodes P p q)).comp
    (binaryPath (k := 2) 0 1 2).toContinuousMap

/-- The original moving square, with no terminal pause inserted. -/
def polynomialSquare : C(unitInterval × unitInterval,
    |nerve (Codiscrete (CommonReferenceNerve.Node (polynomialReference P p q)))|) :=
  (CommonReferenceNerve.parameter _ (squareNodes P p q)).comp
    DoubleSquareScalarPaths.coefficientMovingSquareParameter

/-- The right side is the exact entire coefficient path after polynomial postcomposition. -/
theorem polynomialSquare_right (r : unitInterval) :
    polynomialSquare P p q (r, 1) =
      mapParameter (postcompNode (polynomialMap P (c := c))) (coefficientPath P p q r) := by
  let h : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk
    ⟨CoefficientMovingSquareRows.sourceSide, CoefficientMovingSquareRows.side_rows_monotone 0⟩
  change CommonReferenceNerve.parameter _ (squareNodes P p q)
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, 1)) = _
  rw [CoefficientMovingSquareRows.moving_right_row]
  change CommonReferenceNerve.parameter _ (squareNodes P p q)
      (StdSimplex.map h.toOrderHom (binaryPath (k := 2) 0 1 2 r)) =
    mapParameter (postcompNode (polynomialMap P (c := c)))
      (CommonReferenceNerve.parameter _ (coefficientNodes P p q) (binaryPath 0 1 2 r))
  rw [CommonReferenceNerve.parameter_face, mapParameter_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter (polynomialReference P p q)
    N (binaryPath (k := 2) 0 1 2 r))
  funext i
  exact square_source_nodes P p q i

/-- The left side retains the whole target coefficient path and its actual geometric anchor. -/
theorem polynomialSquare_left (r : unitInterval) :
    polynomialSquare P p q (r, 0) =
      mapParameter (targetAttachmentNode P p q)
        (coefficientPath P ((polynomialUnderFunctor R).map p)
          ((polynomialUnderFunctor R).map q) r) := by
  let h : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk
    ⟨CoefficientMovingSquareRows.targetSide, CoefficientMovingSquareRows.side_rows_monotone 1⟩
  change CommonReferenceNerve.parameter _ (squareNodes P p q)
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, 0)) = _
  rw [CoefficientMovingSquareRows.moving_left_row]
  change CommonReferenceNerve.parameter _ (squareNodes P p q)
      (StdSimplex.map h.toOrderHom (binaryPath (k := 2) 0 1 2 r)) =
    mapParameter (targetAttachmentNode P p q)
      (CommonReferenceNerve.parameter _
        (coefficientNodes P ((polynomialUnderFunctor R).map p)
          ((polynomialUnderFunctor R).map q)) (binaryPath 0 1 2 r))
  rw [CommonReferenceNerve.parameter_face, mapParameter_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter (polynomialReference P p q)
    N (binaryPath (k := 2) 0 1 2 r))
  funext i
  exact square_target_nodes P p q i

/-- Reference change leaves every original finite-square value unchanged. -/
theorem square_parameter_native (n : ℕ) (z : StdSimplex ℝ (Fin 18))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (polynomialReference P p q) (squareNodes P p q) n (z, x) =
      prespectrumSimplexFamily
        (CoefficientTransformationComposition.Scalar.simplex P
          (polynomialUnderCoefficient R) p q) n (z, x) := by
  rw [prespectrumFamily_eq]
  change prespectrumSimplexFamily
    (ModelSimplex.reanchorSimplex (squareAnchor P p q) (originalNodes P p q)) n (z, x) = _
  rw [ModelSimplex.reanchorSimplex_eq]; rfl

/-- The whole moving square recovers its original native value at every level. -/
theorem polynomialSquare_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    pointwisePrespectrumFamily (polynomialReference P p q) n
        (polynomialSquare P p q (r, s)) x =
      (CoefficientTransformationComposition.movingSquare P
        (polynomialUnderCoefficient R) p q).level n (r, (s, x)) := by
  change pointwisePrespectrumFamily _ n (CommonReferenceNerve.parameter _ (squareNodes P p q)
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s))) x = _
  rw [pointwisePrespectrumFamily_parameter, square_parameter_native]
  exact CoefficientTransformationComposition.Scalar.movingSquare_native P
    (polynomialUnderCoefficient R) p q n r s x

/-- The whole left-side native value is the original target-composition track. -/
theorem polynomialSquare_left_native (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    pointwisePrespectrumFamily (polynomialReference P p q) n
        (polynomialSquare P p q (r, 0)) x =
      (CoefficientTransformationComposition.targetComposition P
        (polynomialUnderCoefficient R) p q).level n (r, x) := by
  change pointwisePrespectrumFamily _ n (CommonReferenceNerve.parameter _ (squareNodes P p q)
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, 0))) x = _
  rw [pointwisePrespectrumFamily_parameter, square_parameter_native,
    CoefficientMovingSquareRows.moving_left]
  exact CoefficientTransformationComposition.Scalar.targetComposition_path P
    (polynomialUnderCoefficient R) p q n r x

/-- Both old coefficient normalization halves and the original geometric cast are retained. -/
theorem coefficientPath_native (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    pointwisePrespectrumFamily (coefficientReference P p q) n (coefficientPath P p q r) x =
      (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x) := by
  have hb : ModelSimplex.ofIsos (coefficientReference P p q)
      (fun i ↦ (coefficientNodes P p q i).1) (fun i ↦ (coefficientNodes P p q i).2) =
      BinaryNormalizationSimplex.simplex (coefficientMap P q) (coefficientMap P p) := by
    let Fs := ![BinaryNormalizationSimplex.sourceMap (coefficientMap P q) (coefficientMap P p),
      BinaryNormalizationSimplex.intermediateMap (coefficientMap P q) (coefficientMap P p),
      BinaryNormalizationSimplex.targetMap (coefficientMap P q) (coefficientMap P p)]
    let refs : ∀ i, (coefficientReference P p q).functor ≅ (Fs i).functor :=
      Fin.cases (Iso.refl _) (Fin.cases
        (BinaryNormalizationSimplex.first (coefficientMap P q) (coefficientMap P p))
        (Fin.cases (BinaryNormalizationSimplex.total (coefficientMap P q) (coefficientMap P p))
          (fun j ↦ Fin.elim0 j)))
    exact ModelSimplex.ofIsos_nodes_congr (coefficientNodes P p q)
      (fun i ↦ ⟨Fs i, refs i⟩) (by intro i; fin_cases i <;> rfl)
  change pointwisePrespectrumFamily _ n
    (CommonReferenceNerve.parameter _ (coefficientNodes P p q) (binaryPath 0 1 2 r)) x = _
  rw [pointwisePrespectrumFamily_parameter, prespectrumFamily_eq, hb]
  exact BinaryNormalizationSimplex.native_path (coefficientMap P q) (coefficientMap P p) n r x

end Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
