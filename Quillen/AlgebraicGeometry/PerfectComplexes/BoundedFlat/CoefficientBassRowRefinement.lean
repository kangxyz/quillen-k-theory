/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRowCone
public import Quillen.Topology.Prespectrum.RowRefinement

/-!
# A genuine distinguished-row target for the original Bass cone

The actual row interchange of the unchanged raw cone supplies a complete prespectrum and
an actual comparison from that same cone. Its zero level uses the original two source
structure maps. Positive fixed-structure-time maps preserve the whole distinguished row.
Stability and tensor-product normalization are separate assertions, not consequences assumed
by this construction.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRowRefinement
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The unchanged actual raw Bass cone. -/
abbrev source := mappingCone (boundedFlatCoefficientBassSquareComparison P a)

/-- The actual row-compatible target, constructed using the original cone transpose. -/
def carrier : LoopPrespectrum.{u + 1} :=
  RowRefinement.spectrum (source P a) (CoefficientBassRowCone.rowSwap P a)
    (CoefficientBassRowCone.rowSwap_point P a)

/-- The original structure maps define a whole comparison into the row-compatible target. -/
def comparison : source P a ⟶ carrier P a :=
  RowRefinement.comparison (source P a) (CoefficientBassRowCone.rowSwap P a)
    (CoefficientBassRowCone.rowSwap_point P a) (CoefficientBassRowCone.structure_rowSwap P a)

/-- The positive comparison level is exactly the original cone structure map. -/
theorem comparison_succ (k : ℕ) :
    (comparison P a).map (k + 1) = (source P a).structureMap (k + 1) := rfl

/-- The original source point is kept at all levels, including degree zero. -/
theorem comparison_point (n : ℕ) :
    (comparison P a).map n ((source P a).point n) = (carrier P a).point n :=
  (comparison P a).map_point n

/-- Degree zero uses both original structure maps, without assuming the cone is a Model. -/
theorem comparison_zero (x : (source P a).space 0) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((comparison P a).map 0 x) r) s =
      (source P a).structureMap 1 ((source P a).structureMap 0 x r) s := rfl

/-- Positive structure preserves the row through one actual based map at each structure time. -/
theorem structure_row (k : ℕ)
    (γ : Path ((source P a).point (k + 2)) ((source P a).point (k + 2)))
    (r : unitInterval) :
    (carrier P a).structureMap (k + 1) γ r =
      basedLoopMap
        (RowRefinement.evaluation (source P a) (CoefficientBassRowCone.rowSwap P a) k r)
        (RowRefinement.evaluation_point (source P a) (CoefficientBassRowCone.rowSwap P a)
          (CoefficientBassRowCone.rowSwap_point P a) k r) γ :=
  by
    apply Path.ext
    rfl

/-- The independent spectrum and row parameters have their exact prescribed positions. -/
theorem structure_apply (k : ℕ)
    (γ : Path ((source P a).point (k + 2)) ((source P a).point (k + 2)))
    (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((carrier P a).structureMap (k + 1) γ) r) s =
      CoefficientBassRowCone.rowSwap P a k ((source P a).structureMap (k + 2) (γ s) r) := rfl

end Quillen.PerfectComplexes.CoefficientBassRowRefinement
