/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientMovingSquareReferenceRows

/-!
# The original polynomial rectangle in the genuine polynomial input reference

The three original split-triple diagrams lie in the fixed polynomial reference. Their
middle and last transports are retained as full isomorphisms. The two binary side paths
use the original composition clock, before the separate terminal pause in the cone cap.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialRectangle
open BassH0Merge BassH1Join CommonReferenceNerve CoefficientBassRaw1PolynomialReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

/-- The left vertical map acts on the genuine Polynomial(a) source. -/
abbrev aMap := coefficientMap P ((polynomialUnderFunctor R).map f)

/-- The middle vertical map acts at Polynomial(Polynomial(a)). -/
abbrev bMap := coefficientMap P
  ((polynomialUnderFunctor R).map ((polynomialUnderFunctor R).map f))

/-- The first rectangle equation is the actual polynomial-reindexed coefficient naturality. -/
theorem polynomial_square : bMap P f ≫ first P (a := a) =
    first P (a := b) ≫ aMap P f :=
  coefficientMap_naturality P
    (whiskerRight (polynomialUnderCoefficient R) (polynomialUnderFunctor R)) f

/-- The second equation retains the independently selected outer chart. -/
theorem chart_square : last P f ≫ second P α (a := a) =
    second P α (a := b) ≫ bMap P f :=
  coefficientMap_naturality P (whiskerRight α (polynomialUnderFunctor R)) f

/-- All eighteen nodes retain their original merged-triple references. -/
def nodes : Fin 18 → Node (polynomialReference P α f) :=
  DoubleSquareMergedSimplex.nodes (first P (a := a)) (second P α (a := a))
    (first P (a := b)) (second P α (a := b)) (aMap P f) (bMap P f) (last P f)
    (polynomial_square P f) (chart_square P α f)

/-- The middle source transport is the actual chart naturality equality. -/
abbrev middleAnchor := DoubleSquareCommonSimplex.middleSourceIso
  (first P (a := a)) (second P α (a := a)) (second P α (a := b))
  (bMap P f) (last P f) (chart_square P α f)

/-- The last source transport retains both naturality equations and scheme association. -/
abbrev lastAnchor := DoubleSquareCommonSimplex.lastSourceIso
  (first P (a := a)) (second P α (a := a)) (first P (a := b)) (second P α (a := b))
  (aMap P f) (bMap P f) (last P f) (polynomial_square P f) (chart_square P α f)

/-- The first entire split triple has its unchanged full node references. -/
theorem first_nodes (i : Fin 8) :
    nodes P α f (DoubleSquareMergedSimplex.firstFace.toOrderHom i) =
      (⟨SplitTripleSimplex.vertices (last P f) (second P α (a := a)) (first P (a := a)) i,
        SplitTripleSimplex.references (last P f) (second P α (a := a)) (first P (a := a)) i⟩ :
        Node (polynomialReference P α f)) :=
  (DoubleSquareMergedSimplex.first_nodes (first P (a := a)) (second P α (a := a))
    (first P (a := b)) (second P α (a := b)) (aMap P f) (bMap P f) (last P f)
    (polynomial_square P f) (chart_square P α f) i).trans
      (DoubleSquareCommonSimplex.first_nodes (first P (a := a)) (second P α (a := a))
        (first P (a := b)) (second P α (a := b)) (aMap P f) (bMap P f) (last P f)
        (polynomial_square P f) (chart_square P α f) i)

/-- The second split triple keeps its full chart-square reanchor. -/
theorem middle_nodes (i : Fin 8) :
    nodes P α f (DoubleSquareMergedSimplex.middleFace.toOrderHom i) =
      (⟨SplitTripleSimplex.vertices (second P α (a := b)) (bMap P f) (first P (a := a)) i,
        middleAnchor P α f ≪≫ SplitTripleSimplex.references
          (second P α (a := b)) (bMap P f) (first P (a := a)) i⟩ :
        Node (polynomialReference P α f)) :=
  (DoubleSquareMergedSimplex.middle_nodes (first P (a := a)) (second P α (a := a))
    (first P (a := b)) (second P α (a := b)) (aMap P f) (bMap P f) (last P f)
    (polynomial_square P f) (chart_square P α f) i).trans
      (DoubleSquareCommonSimplex.middle_nodes (first P (a := a)) (second P α (a := a))
        (first P (a := b)) (second P α (a := b)) (aMap P f) (bMap P f) (last P f)
        (polynomial_square P f) (chart_square P α f) i)

/-- The third split triple keeps both original source-square transports. -/
theorem last_nodes (i : Fin 8) :
    nodes P α f (DoubleSquareMergedSimplex.lastFace.toOrderHom i) =
      (⟨SplitTripleSimplex.vertices (second P α (a := b)) (first P (a := b)) (aMap P f) i,
        lastAnchor P α f ≪≫ SplitTripleSimplex.references
          (second P α (a := b)) (first P (a := b)) (aMap P f) i⟩ :
        Node (polynomialReference P α f)) :=
  (DoubleSquareMergedSimplex.last_nodes (first P (a := a)) (second P α (a := a))
    (first P (a := b)) (second P α (a := b)) (aMap P f) (bMap P f) (last P f)
    (polynomial_square P f) (chart_square P α f) i).trans
      (DoubleSquareCommonSimplex.last_nodes (first P (a := a)) (second P α (a := a))
        (first P (a := b)) (second P α (a := b)) (aMap P f) (bMap P f) (last P f)
        (polynomial_square P f) (chart_square P α f) i)

/-- The complete source binary row is the original postcomposed normalization. -/
theorem source_side_nodes (i : Fin 3) :
    nodes P α f (CoefficientMovingSquareRows.sourceSide i) =
      postReferenceNode (polynomialReference P α f) (normalizedMap (last P f))
        (H := BinaryNormalizationSimplex.sourceMap (second P α (a := a)) (first P (a := a)))
        (BinaryNormalizationSimplex.total (last P f)
          (second P α (a := a) ≫ first P (a := a)))
        (binaryNodes (second P α (a := a)) (first P (a := a)) i) :=
  CoefficientMovingSquareRows.source_side_nodes
    (first P (a := a)) (second P α (a := a)) (first P (a := b)) (second P α (a := b))
    (aMap P f) (bMap P f) (last P f) (polynomial_square P f) (chart_square P α f) i

/-- The complete target binary row retains the last anchor and original rightFirst. -/
theorem target_side_nodes (i : Fin 3) :
    nodes P α f (CoefficientMovingSquareRows.targetSide i) =
      preReferenceNode (polynomialReference P α f) (normalizedMap (aMap P f))
        (lastAnchor P α f ≪≫ NormalizedTripleSimplex.rightFirst
          (second P α (a := b)) (first P (a := b)) (aMap P f))
        (binaryNodes (second P α (a := b)) (first P (a := b)) i) :=
  CoefficientMovingSquareRows.target_side_nodes
    (first P (a := a)) (second P α (a := a)) (first P (a := b)) (second P α (a := b))
    (aMap P f) (bMap P f) (last P f) (polynomial_square P f) (chart_square P α f) i

/-- The unchanged moving parameter is evaluated in this genuine polynomial reference. -/
def moving : C(I × I, |nerve (Codiscrete (Node (polynomialReference P α f)))|) :=
  (parameter (polynomialReference P α f) (nodes P α f)).comp
    DoubleSquareScalarPaths.coefficientMovingSquareParameter

/-- The complete source binary row is identified at every original composition time. -/
theorem source_side_parameter (t : I) :
    parameter (polynomialReference P α f) (nodes P α f)
      (StdSimplex.map CoefficientMovingSquareRows.sourceSide
        (Quillen.SimplexParameters.binaryPath (k := 2) 0 1 2 t)) =
      parameter (polynomialReference P α f) (fun i ↦
        postReferenceNode (polynomialReference P α f) (normalizedMap (last P f))
          (H := BinaryNormalizationSimplex.sourceMap (second P α (a := a)) (first P (a := a)))
          (BinaryNormalizationSimplex.total (last P f)
            (second P α (a := a) ≫ first P (a := a)))
          (binaryNodes (second P α (a := a)) (first P (a := a)) i))
        (Quillen.SimplexParameters.binaryPath (k := 2) 0 1 2 t) := by
  let ι : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk
    ⟨CoefficientMovingSquareRows.sourceSide, CoefficientMovingSquareRows.side_rows_monotone 0⟩
  have h := parameter_face (polynomialReference P α f) (nodes P α f) ι
    (Quillen.SimplexParameters.binaryPath (k := 2) 0 1 2 t)
  exact h.trans (congrArg (fun N ↦ parameter (polynomialReference P α f) N
    (Quillen.SimplexParameters.binaryPath (k := 2) 0 1 2 t)) (funext (source_side_nodes P α f)))

/-- The complete target binary row retains its original composition time and full anchor. -/
theorem target_side_parameter (t : I) :
    parameter (polynomialReference P α f) (nodes P α f)
      (StdSimplex.map CoefficientMovingSquareRows.targetSide
        (Quillen.SimplexParameters.binaryPath (k := 2) 0 1 2 t)) =
      parameter (polynomialReference P α f) (fun i ↦
        preReferenceNode (polynomialReference P α f) (normalizedMap (aMap P f))
          (lastAnchor P α f ≪≫ NormalizedTripleSimplex.rightFirst
            (second P α (a := b)) (first P (a := b)) (aMap P f))
          (binaryNodes (second P α (a := b)) (first P (a := b)) i))
        (Quillen.SimplexParameters.binaryPath (k := 2) 0 1 2 t) := by
  let ι : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk
    ⟨CoefficientMovingSquareRows.targetSide, CoefficientMovingSquareRows.side_rows_monotone 1⟩
  have h := parameter_face (polynomialReference P α f) (nodes P α f) ι
    (Quillen.SimplexParameters.binaryPath (k := 2) 0 1 2 t)
  exact h.trans (congrArg (fun N ↦ parameter (polynomialReference P α f) N
    (Quillen.SimplexParameters.binaryPath (k := 2) 0 1 2 t)) (funext (target_side_nodes P α f)))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialRectangle
