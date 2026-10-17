/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleSquareRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0ScalarEdges
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveWhiskering
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveReanchorFamily

/-!
# The two actual H0 chart boundaries in their full reference nerve

For an arbitrary polynomial-to-Laurent chart, the original five chart-naturality nodes have
genuine polynomial source. Their precomposition by the polynomial projection, with the original
projection anchor, is exactly the chart row of the original H0 rectangle. The positive and
inverse charts retain their separate projection equations and square equality transports.
The resulting full-node identities identify both complete four-simplex parameters and the
unchanged left and right boundary paths of H0.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.BassH0ChartBoundaryRows
open BassH0Merge CommonReferenceNerve

/-- The actual ordered five-node chart row of the original projection rectangle. -/
def rowFace : ⦋4⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨ProjectionRectangleSquareRows.chartRow, by decide⟩

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The original chart-square reference, with genuine polynomial source at `a`. -/
abbrev squareSource := NativeSquareFiveSimplex.source
  (coefficientMap P ((laurentUnderFunctor R).map w)) (coefficientMap P (α.app a))

/-- Both original binary normalization rows, including the chart's own equality transport. -/
abbrev squareNodes := NativeSquareFiveSimplex.nodes
  (coefficientMap P ((laurentUnderFunctor R).map w)) (coefficientMap P (α.app a))
  (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map w))
  (coefficientMap_naturality P α w)

variable
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/-- The complete original anchor into the polynomially precomposed chart-square reference. -/
abbrev canonicalAnchor := ProjectionRectangleSquareRows.chartAnchor
  (polynomialProjection P a) (coefficientMap P (α.app a))
  (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a) ha

/-- Original projection precomposition on full nodes with genuine polynomial source. -/
def preNode (N : CommonReferenceNerve.Node (squareSource P w α)) :
    CommonReferenceNerve.Node (BassH0Diagram.reference P w) :=
  preReferenceNode (BassH0Diagram.reference P w) (normalizedMap (polynomialProjection P a))
    (canonicalAnchor P w α ha) N

/-- All five original rectangle nodes agree with their canonically anchored polynomial rows. -/
theorem chart_nodes (i : Fin 5) :
    BassH0Diagram.chartNodes P w α ha (rowFace.toOrderHom i) =
      preNode P w α ha (squareNodes P w α i) :=
  ProjectionRectangleSquareRows.chart_row_nodes
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b))
    (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (coefficientMap_naturality P (polynomialUnderCoefficient R) w)
    (coefficientMap_naturality P α w) (laurentProjection P a) ha i

/-- The full positive chart row is present in the actual 31-node H0 diagram. -/
theorem plus_nodes (i : Fin 5) :
    BassH0Diagram.nodes P w ((rowFace ≫ BassH0Diagram.plusFace).toOrderHom i) =
      preNode P w (underToLaurent R) (laurentPlus_projection P a)
        (squareNodes P w (underToLaurent R) i) :=
  (BassH0Diagram.plus_nodes P w (rowFace.toOrderHom i)).trans
    (chart_nodes P w (underToLaurent R) (laurentPlus_projection P a) i)

/-- The full inverse chart row keeps its distinct source projection and naturality casts. -/
theorem minus_nodes (i : Fin 5) :
    BassH0Diagram.nodes P w ((rowFace ≫ BassH0Diagram.minusFace).toOrderHom i) =
      preNode P w (underToLaurentInvert R) (laurentMinus_projection P a)
        (squareNodes P w (underToLaurentInvert R) i) :=
  (BassH0Diagram.minus_nodes P w (rowFace.toOrderHom i)).trans
    (chart_nodes P w (underToLaurentInvert R) (laurentMinus_projection P a) i)

/-- Every point of the complete positive chart simplex retains its full original references. -/
theorem plus_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (BassH0Diagram.reference P w) (BassH0Diagram.nodes P w)
      (StdSimplex.map (rowFace ≫ BassH0Diagram.plusFace).toOrderHom z) =
    CommonReferenceNerve.parameter (BassH0Diagram.reference P w)
      (fun i ↦ preNode P w (underToLaurent R) (laurentPlus_projection P a)
        (squareNodes P w (underToLaurent R) i)) z := by
  rw [CommonReferenceNerve.parameter_face]
  exact congrArg (fun N ↦ CommonReferenceNerve.parameter (BassH0Diagram.reference P w) N z)
    (funext (plus_nodes P w))

/-- Every point of the separate inverse chart simplex retains its full original references. -/
theorem minus_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (BassH0Diagram.reference P w) (BassH0Diagram.nodes P w)
      (StdSimplex.map (rowFace ≫ BassH0Diagram.minusFace).toOrderHom z) =
    CommonReferenceNerve.parameter (BassH0Diagram.reference P w)
      (fun i ↦ preNode P w (underToLaurentInvert R) (laurentMinus_projection P a)
        (squareNodes P w (underToLaurentInvert R) i)) z := by
  rw [CommonReferenceNerve.parameter_face]
  exact congrArg (fun N ↦ CommonReferenceNerve.parameter (BassH0Diagram.reference P w) N z)
    (funext (minus_nodes P w))

/-- H0's entire left boundary is the exact positive chart family at its unchanged square time. -/
theorem left_parameter (t : unitInterval) :
    CommonReferenceNerve.parameter (BassH0Diagram.reference P w) (BassH0Diagram.nodes P w)
      (BassH0Diagram.parameter (t, 0)) =
    CommonReferenceNerve.parameter (BassH0Diagram.reference P w)
      (fun i ↦ preNode P w (underToLaurent R) (laurentPlus_projection P a)
        (squareNodes P w (underToLaurent R) i)) (NativeSquareFiveSimplex.parameter t) := by
  rw [BassH0Diagram.parameter_left]
  have h := ProjectionRectangleSquareRows.chart_parameter BassH0Diagram.plusFace t
  change StdSimplex.map (rowFace ≫ BassH0Diagram.plusFace).toOrderHom
    (NativeSquareFiveSimplex.parameter t) = _ at h
  rw [← h]
  exact plus_parameter P w _

/-- H0's entire right boundary is the exact inverse chart family at its unchanged square time. -/
theorem right_parameter (t : unitInterval) :
    CommonReferenceNerve.parameter (BassH0Diagram.reference P w) (BassH0Diagram.nodes P w)
      (BassH0Diagram.parameter (t, 1)) =
    CommonReferenceNerve.parameter (BassH0Diagram.reference P w)
      (fun i ↦ preNode P w (underToLaurentInvert R) (laurentMinus_projection P a)
        (squareNodes P w (underToLaurentInvert R) i)) (NativeSquareFiveSimplex.parameter t) := by
  rw [BassH0Diagram.parameter_right]
  have h := ProjectionRectangleSquareRows.chart_parameter BassH0Diagram.minusFace t
  change StdSimplex.map (rowFace ≫ BassH0Diagram.minusFace).toOrderHom
    (NativeSquareFiveSimplex.parameter t) = _ at h
  rw [← h]
  exact minus_parameter P w _

/-- The anchored finite family is the original polynomial-source nerve parameter's image. -/
theorem pre_parameter {k : ℕ} (N : Fin (k + 1) → CommonReferenceNerve.Node (squareSource P w α))
    (z : StdSimplex ℝ (Fin (k + 1))) :
    CommonReferenceNerve.parameter (BassH0Diagram.reference P w)
      (fun i ↦ preNode P w α ha (N i)) z =
    mapParameter (preNode P w α ha) (CommonReferenceNerve.parameter (squareSource P w α) N z) :=
  (mapParameter_parameter (preNode P w α ha) N z).symm

/-- Projection precomposition retains the original family on every genuine polynomial input. -/
theorem pre_family {k : ℕ} (N : Fin (k + 1) → CommonReferenceNerve.Node (squareSource P w α))
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    prespectrumFamily (BassH0Diagram.reference P w) (fun i ↦ preNode P w α ha (N i)) n (z, x) =
    prespectrumFamily (squareSource P w α) N n
      (z, (prespectrumMap (normalizedMap (polynomialProjection P a))).map n x) := by
  change prespectrumFamily (BassH0Diagram.reference P w)
    (ModelSimplex.reanchorNodes (canonicalAnchor P w α ha)
      (fun i ↦ precompNode (normalizedMap (polynomialProjection P a)) (N i))) n (z, x) = _
  rw [prespectrumFamily_reanchor, prespectrumFamily_precomp]

/-- The actual five-node family evaluates on arbitrary polynomial-source inputs at every level. -/
theorem square_native (n : ℕ) (t : unitInterval)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a))))).space n) :
    prespectrumFamily (squareSource P w α) (squareNodes P w α) n
      (NativeSquareFiveSimplex.parameter t, x) =
    (boundedFlatPerfectPrespectrumSquareHomotopy
      (coefficientMap P ((laurentUnderFunctor R).map w)) (coefficientMap P (α.app a))
      (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map w))
      (coefficientMap_naturality P α w)).level n (t, x) := by
  rw [prespectrumFamily_eq]
  exact NativeSquareFiveSimplex.native _ _ _ _ _ n t x

end Quillen.PerfectComplexes.BassH0ChartBoundaryRows
