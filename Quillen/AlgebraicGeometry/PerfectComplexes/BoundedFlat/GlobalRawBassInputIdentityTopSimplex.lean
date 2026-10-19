/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityProjection
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialSpanUnitSimplex

/-!
# The three original polynomial-span identity pieces

The original global scheme arrows and full reference data are used directly. Only the pure
scalar parameters are shared with the coefficient development; no coefficient model is identified.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentityTopSimplex
open OriginalUnitSquareSimplex CoefficientPolynomialSpanUnitSimplex
variable (X : Scheme.{u})

/-- The positive moving piece is the original polynomial unit square postcomposed unchanged. -/
def plusSimplex := (OriginalUnitSquareSimplex.simplex (projection.app X)).postcomp
  (sourceMap (plus.app X))

/-- The negative moving piece retains its separate actual Laurent chart. -/
def minusSimplex := (OriginalUnitSquareSimplex.simplex (projection.app X)).postcomp
  (sourceMap (minus.app X))

theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    prespectrumSimplexFamily (plusSimplex X) n (squareParameter (r, s), x) =
      ((InputIdentity.polynomialSquare X).postcompose
        (boundedFlatPerfectPrespectrumMap (plus.app X))).level n (r, (s, x)) := by
  refine (prespectrumSimplexFamily_postcomp
    (OriginalUnitSquareSimplex.simplex (projection.app X))
    (sourceMap (plus.app X)) n (squareParameter (r, s)) x).trans ?_
  exact congrArg ((boundedFlatPerfectPrespectrumMap (plus.app X)).map n)
    (square_native (projection.app X) n r s x)

theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    prespectrumSimplexFamily (minusSimplex X) n (squareParameter (r, s), x) =
      ((InputIdentity.polynomialSquare X).postcompose
        (boundedFlatPerfectPrespectrumMap (minus.app X))).level n (r, (s, x)) := by
  refine (prespectrumSimplexFamily_postcomp
    (OriginalUnitSquareSimplex.simplex (projection.app X))
    (sourceMap (minus.app X)) n (squareParameter (r, s)) x).trans ?_
  exact congrArg ((boundedFlatPerfectPrespectrumMap (minus.app X)).map n)
    (square_native (projection.app X) n r s x)

/-- The moving middle is the actual fifteen-vertex composite grid, retaining both times. -/
def middleSimplex := CommonReferenceProduct.simplex
  (unitSourceMap X) (identityVertices X)
  (identityReferences X)
  (InputIdentityProjection.source X) (fun i ↦ (InputIdentityProjection.nodes X i).1)
  (fun i ↦ (InputIdentityProjection.nodes X i).2)

/-- The product parameter of the binary identity path and the Bass projection path. -/
def middleParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 z.1, InputIdentityProjection.parameter z.2), by fun_prop⟩

/-- The actual moving overlap is the product of the original base identity and Bass cylinder. -/
theorem middle_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    prespectrumSimplexFamily (middleSimplex X) n (middleParameter.{u} (r, s), x) =
      (comparison X).map n
        (HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X)) n
          (s, (boundedFlatPerfectPrespectrumIdHomotopy X).level n (r, x))) := by
  refine (CommonReferenceProduct.prespectrum_comp
    (unitSourceMap X) (identityVertices X)
    (identityReferences X)
    (InputIdentityProjection.source X) (fun i ↦ (InputIdentityProjection.nodes X i).1)
    (fun i ↦ (InputIdentityProjection.nodes X i).2) n x
    (binaryPath (k := 2) 0 1 2 r) (InputIdentityProjection.parameter s)).trans ?_
  refine (congrArg (fun y ↦ prespectrumSimplexFamily (InputIdentityProjection.simplex X) n
    (InputIdentityProjection.parameter s, y)) (identity_native X n r x)).trans ?_
  exact InputIdentityProjection.native X n s
    ((boundedFlatPerfectPrespectrumIdHomotopy X).level n (r, x))


end Quillen.PerfectComplexes.GlobalRawBass.InputIdentityTopSimplex
