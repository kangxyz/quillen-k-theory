/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitBoundaryNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassConeFaces
public import Quillen.Topology.Realization.SimplexGridColumn

/-! The exact original Bass projection by Laurent identity product. The two scalar coordinates
remain independent, and every boundary is identified before the product is relabeled. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassUnitBottom
open CoefficientPolynomialSpanUnitNodes CoefficientBassUnitBoundaryNodes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The genuine fifteen product nodes with their common reference, unchanged by reanchoring. -/
def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))) 14 :=
  ModelSimplex.ofIsos (source P a) (fun i ↦ (bottomNodes P a i).1)
    (fun i ↦ (bottomNodes P a i).2)

/-- First follow the actual Bass projection, then the original two-step Laurent identity. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 4 2
    (BassProjectionPath.parameter z.2, binaryPath (k := 2) 0 1 2 z.1), by fun_prop⟩

private theorem family_simplex_congr {V W : Model.{u}} {k : ℕ}
    (S T : ModelSimplex V W k) (h : S = T) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (z, x) = prespectrumSimplexFamily T n (z, x) :=
  congrArg (fun U ↦ prespectrumSimplexFamily U n (z, x)) h

/-- The whole native bottom is the original Laurent identity after the unchanged Bass map. -/
theorem native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (parameter.{u} (r, t), x) =
      (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
        (boundedFlatCoefficientLaurentIdentityHomotopy P a)).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  refine (family_simplex_congr _ _ (bottom_family P a) n _ x).trans ?_
  refine (CommonReferenceProduct.prespectrum_comp
    (BassProjectionPath.source P a) (fun j ↦ (BassProjectionPath.nodes P a j).1)
    (fun j ↦ (BassProjectionPath.nodes P a j).2)
    (OriginalUnitSquareSimplex.unitSourceMap (space (op P, (laurentUnderFunctor R).obj a)))
    (CoefficientPolynomialSpanUnitSimplex.identityVertices
      (space (op P, (laurentUnderFunctor R).obj a)))
    (CoefficientPolynomialSpanUnitSimplex.identityReferences
      (space (op P, (laurentUnderFunctor R).obj a))) n x
    (BassProjectionPath.parameter t) (binaryPath (k := 2) 0 1 2 r)).trans ?_
  refine (CoefficientPolynomialSpanUnitSimplex.identity_native
    (space (op P, (laurentUnderFunctor R).obj a)) n r _).trans ?_
  exact congrArg (fun y ↦ (boundedFlatCoefficientLaurentIdentityHomotopy P a).level n (r, y))
    (BassProjectionPath.native P a n t x)

/-- The lower comparison face retains the full initial projection column. -/
theorem parameter_zero (t : unitInterval) :
    parameter.{u} (0, t) =
      StdSimplex.map (SimplexGrid.columnFace 4 2 0).toOrderHom
        (BassProjectionPath.parameter t) := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (BassProjectionPath.parameter t, binaryPath (k := 2) 0 1 2 0) = _
  rw [Path.source, SimplexGrid.parameter_column]

/-- The upper comparison face is precisely the terminal projection column. -/
theorem parameter_one (t : unitInterval) :
    parameter.{u} (1, t) =
      StdSimplex.map (SimplexGrid.columnFace 4 2 2).toOrderHom
        (BassProjectionPath.parameter t) := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (BassProjectionPath.parameter t, binaryPath (k := 2) 0 1 2 1) = _
  rw [Path.target, SimplexGrid.parameter_column]

/-- The complete positive side retains both Laurent identity normalization edges. -/
theorem parameter_left (r : unitInterval) :
    parameter.{u} (r, 0) = binaryPath (k := 14) 6 7 8 r := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (BassProjectionPath.parameter 0, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.source, SimplexGrid.parameter_row]
  exact map_binaryPath (SimplexGrid.rowFace 4 2 2) 0 1 2 r

/-- The inverse side keeps its distinct terminal row and original identity speed. -/
theorem parameter_right (r : unitInterval) :
    parameter.{u} (r, 1) = binaryPath (k := 14) 12 13 14 r := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (BassProjectionPath.parameter 1, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.target, SimplexGrid.parameter_row]
  exact map_binaryPath (SimplexGrid.rowFace 4 2 4) 0 1 2 r

end Quillen.PerfectComplexes.CoefficientBassUnitBottom
