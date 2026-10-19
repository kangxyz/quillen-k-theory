/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientSpectrum
public import Quillen.Topology.Prespectrum.LoopTailFunctor
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# The genuine first tensor coefficient cell after a specified cofiber map

Postcompose the independently realized coefficient spectrum cell by the actual loop-tail image
of a supplied map. Strict naturality of the original stabilization identifies the endpoints.
The full resulting homotopy is the stabilized image of the original tensor track after the same
map. This applies in particular to the unchanged Bass cofiber inclusion; no new contraction or
point-set inverse is chosen.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)
  {C : Quillen.LoopPrespectrum.{u + 1}}
  (j : originalPrespectrum (boundedFlatPerfectWaldhausen X) ⟶ C)

/-- The actual stabilization square identifies the endpoints without changing any time. -/
theorem tensorUnitPullbackCoefficientCone_endpoint :
    (boundedFlatPerfectTensorUnitPrespectrumMap f ≫
      stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X))) ≫
        loopTailFunctor.map j =
      (boundedFlatPerfectTensorUnitPrespectrumMap f ≫ j) ≫ stabilizationMap C := by
  rw [Category.assoc, ← stabilizationMap_naturality, Category.assoc]

/-- Apply the actual cofiber map to the independently realized coefficient spectrum cell. -/
def tensorUnitPullbackCoefficientConeHomotopy :
    Homotopy ((boundedFlatPerfectTensorUnitPrespectrumMap f ≫ j) ≫ stabilizationMap C)
      ((boundedFlatPerfectTensorUnitPrespectrumMap f ≫ j) ≫ stabilizationMap C) :=
  ((tensorUnitPullbackCoefficientSpectrumHomotopy f r).postcomp
    (loopTailFunctor.map j)).cast
      (tensorUnitPullbackCoefficientCone_endpoint f j)
      (tensorUnitPullbackCoefficientCone_endpoint f j)

/-- The entire coefficient-cell/cofiber track equals the actual stabilized tensor/cofiber track.
-/
theorem tensorUnitPullbackCoefficientConeHomotopy_eq :
    tensorUnitPullbackCoefficientConeHomotopy f r j =
      ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp j).postcomp
        (stabilizationMap C) := by
  apply Quillen.LoopPrespectrum.Homotopy.ext
  funext n
  apply ContinuousMap.ext
  intro z
  change (loopTailFunctor.map j).map n
      ((tensorUnitPullbackCoefficientSpectrumHomotopy f r).level n z) = _
  rw [tensorUnitPullbackCoefficientSpectrumHomotopy_eq]
  apply Path.ext
  funext s
  exact congrArg (fun γ => Path.toContinuousMap γ s)
    (j.comm n ((boundedFlatPerfectTensorUnitHomotopy f r).level n z))

/-- Every positive-level value still displays the independently realized first coefficient cell.
-/
theorem tensorUnitPullbackCoefficientConeHomotopy_succ (k : ℕ) (s t : unitInterval)
    (x : stageSpace k (modelOf (boundedFlatPerfectWaldhausen Y))) :
    Path.toContinuousMap
        ((tensorUnitPullbackCoefficientConeHomotopy f r j).level (k + 1) (t, x)) s =
      j.map ((k + 1) + 1)
        (tensorUnitPullbackCoefficientStageRealization f r k (s, (t, x))) := rfl

end Quillen.PerfectComplexes
