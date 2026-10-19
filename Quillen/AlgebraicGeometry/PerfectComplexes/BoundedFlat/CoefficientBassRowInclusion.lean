/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRowRefinement
public import Quillen.Topology.Prespectrum.RowRefinementMap

/-!
# The original Laurent inclusion on distinguished-row targets

The complete original cone inclusion preserves the actual row transpose, hence induces a
whole map from the genuine Laurent row spectrum to the Bass row spectrum. The strict square
with both original row-comparison maps includes degree zero and retains each independent
loop parameter. This supplies a point-set cofiber input for the standard normalization prism.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRowRefinement
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The actual original Laurent model, with its prescribed chosen zero. -/
abbrev laurentModel :=
  modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a)))

/-- The original Laurent inclusion acts on the entire distinguished-row prespectrum. -/
def inclusionRow : rowLoopPrespectrum (laurentModel P a) ⟶ carrier P a :=
  RowRefinement.map (fun k => RowHomotopyPushout.vertex k (laurentModel P a))
    (CoefficientBassRowCone.rowSwap P a)
    (fun k => RowHomotopyPushout.vertex_point k (laurentModel P a))
    (CoefficientBassRowCone.rowSwap_point P a)
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
    (CoefficientBassRowCone.rowSwap_inclusion P a)

/-- The full positive Laurent row is included pointwise with its row coordinate unchanged. -/
theorem inclusionRow_succ (k : ℕ)
    (γ : Path (stagePoint (k + 1) (laurentModel P a))
      (stagePoint (k + 1) (laurentModel P a))) (s : unitInterval) :
    Path.toContinuousMap ((inclusionRow P a).map (k + 1) γ) s =
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map (k + 2)
        (γ s) := rfl

/-- Degree zero retains both loop coordinates of the genuine Laurent row extension. -/
theorem inclusionRow_zero
    (γ : Path (Path.refl (stagePoint 1 (laurentModel P a)))
      (Path.refl (stagePoint 1 (laurentModel P a)))) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((inclusionRow P a).map 0 γ) r) s =
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map 2 (γ r s) := rfl

/-- The original Laurent inclusion and both actual row comparisons form a strict spectrum square.
-/
theorem inclusion_comparison :
    mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a) ≫ comparison P a =
      rowStabilizationMap (laurentModel P a) ≫ inclusionRow P a :=
  RowRefinement.comparison_naturality
    (fun k => RowHomotopyPushout.vertex k (laurentModel P a))
    (CoefficientBassRowCone.rowSwap P a)
    (fun k => RowHomotopyPushout.vertex_point k (laurentModel P a))
    (CoefficientBassRowCone.rowSwap_point P a)
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
    (CoefficientBassRowCone.rowSwap_inclusion P a)
    (fun k x s t => stageLoopMap_rowSwap k (laurentModel P a) x s t)
    (CoefficientBassRowCone.structure_rowSwap P a)

end Quillen.PerfectComplexes.CoefficientBassRowRefinement
