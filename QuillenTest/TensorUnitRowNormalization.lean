/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientRowBassComparison
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientKOne
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientRowStructure
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitConeRowComparison
import Quillen.Waldhausen.SConstruction.Iterated.RowLoopStableEquivalence
import Quillen.Waldhausen.SConstruction.Iterated.RowLoopHomotopy
import Quillen.Topology.Prespectrum.RowNormalizedOperationNaturality

/-!
Regression consumers for the original forward coefficient class and the actual normalized
first-row operation through the same raw cofiber. The concrete structure test keeps its row,
unit and structure coordinates distinct. The whole terminal face retains the original scalar
seed at every level; no stability of the row comparison on an arbitrary cone is assumed.
-/
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u

/-- The original forward Laurent representative remains the coefficient class of the same cell.
-/
example (R : CommRingCat.{u}) :
    KMap (boundedFlatPerfectInclusion_exact (Spec (.of (LaurentPolynomial R)))) 1
        (tensorUnitCoefficientKOneClass (Spec (.of (LaurentPolynomial R)))
          (laurentGlobalUnit R)) =
      perfectOpenKRestrict (laurentPlus R) 1
        (perfectScalarForwardKOneClass (laurentPlus R)
          (rankOnePerfect (Spec (.of (Polynomial R)))) (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R)) := by
  rw [tensorUnitCoefficientKOneClass_inclusion,
    polynomialScalarForwardKOneClass_restrict_rankOne]

/-- The actual normalized coefficient operation preserves the genuine row-transposed structure.
-/
example {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R) (k : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space (k + 1))
    (r t s : unitInterval) :
    CoefficientBassRowCone.rowSwap P a k
      ((mappingCone (boundedFlatCoefficientBassSquareComparison P a)).structureMap (k + 2)
        (Path.toContinuousMap (Path.toContinuousMap
          ((boundedFlatCoefficientNormalizedCellBass P a).map (k + 1) x) t) s) r) =
      Path.toContinuousMap (Path.toContinuousMap
        ((boundedFlatCoefficientNormalizedCellBass P a).map (k + 2)
          ((originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap
            (k + 1) x r)) t) s := by
  exact (congrArg (fun p => Path.toContinuousMap (Path.toContinuousMap
    (Path.toContinuousMap p r) t) s)
    ((boundedFlatCoefficientNormalizedCellBass P a).comm (k + 1) x)).symm

/-- The whole comparison ends at the unchanged scalar Bass seed after the displayed row map. -/
example {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R) (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (t : unitInterval) :
    Path.toContinuousMap
      ((boundedFlatCoefficientNormalizedCellScalarHomotopy P a).level n (1, x)) t =
    (CoefficientBassRowRefinement.comparison P a).map n
      (Path.toContinuousMap ((boundedFlatCoefficientBassTransition P a).map n x) t) :=
  congrArg (fun p => Path.toContinuousMap p t)
    ((boundedFlatCoefficientNormalizedCellScalarHomotopy P a).at_one n x)
