/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeConeEvaluation
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeLaws

/-! The ordinary cone evaluator retains the native point and independent structure time. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier FourEdgeTree
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => BassH0Merge.normalizedMap (polynomialProjection P a)
local notation "F" => reference P a E
local notation "β" => beta P a E

/-- Every scalar cone point sends the actual native base point to the base point. -/
theorem coneEval_point (n : ℕ) (z : scalarCone P a E) :
    coneEval P a E n z ((prespectrum V).point n) = (nativeBassCone P a).point n := by
  have h := SetDescent.funext β
    (SSet.stdSimplex.isTerminalObj₀.from (FourEdgeTree.simplicial E J))
    (fun z ↦ coneEval P a E n z ((prespectrum V).point n))
    (fun _ ↦ (nativeBassCone P a).point n)
    (fun z ↦ by
      have hc := coneEval_cylinder P a E n z.1 z.2.down ((prespectrum V).point n)
      rw [nativeEval_point] at hc
      exact hc.trans (ReducedMappingCone.cylinder_base _ _ _ _))
    (fun y ↦ by
      change coneEval P a E n (laurentInclusion E J F β y) ((prespectrum V).point n) = _
      rw [coneEval_laurent]
      change (LoopPrespectrum.mappingConeInclusion
        (boundedFlatCoefficientBassSquareComparison P a)).map n
          (pointwisePrespectrumFamily F n y ((prespectrum V).point n)) = _
      rw [pointwisePrespectrumFamily_point]
      rfl)
    (fun y ↦ by
      have hy : y = (default : |tipSSet.{u + 1}|) := Subsingleton.elim _ _
      subst y
      exact coneEval_tip P a E n _)
  exact congrFun h z

/-- The entire scalar cone preserves the original structure loop at its independent time. -/
theorem coneEval_structure (n : ℕ) (z : scalarCone P a E)
    (x : (prespectrum V).space n) (r : I) :
    coneEval P a E (n + 1) z ((prespectrum V).structureMap n x r) =
      (nativeBassCone P a).structureMap n (coneEval P a E n z x) r := by
  have h := SetDescent.funext β
    (SSet.stdSimplex.isTerminalObj₀.from (FourEdgeTree.simplicial E J))
    (fun z ↦ coneEval P a E (n + 1) z ((prespectrum V).structureMap n x r))
    (fun z ↦ (nativeBassCone P a).structureMap n (coneEval P a E n z x) r)
    (fun z ↦ by
      change coneEval P a E (n + 1) (cylinder E J F β (z.1, z.2.down))
        ((prespectrum V).structureMap n x r) =
          (nativeBassCone P a).structureMap n
            (coneEval P a E n (cylinder E J F β (z.1, z.2.down)) x) r
      rw [coneEval_cylinder, coneEval_cylinder, nativeEval_structure]
      rfl)
    (fun y ↦ by
      change coneEval P a E (n + 1) (laurentInclusion E J F β y)
        ((prespectrum V).structureMap n x r) =
          (nativeBassCone P a).structureMap n (coneEval P a E n
            (laurentInclusion E J F β y) x) r
      rw [coneEval_laurent, coneEval_laurent]
      change (LoopPrespectrum.mappingConeInclusion
        (boundedFlatCoefficientBassSquareComparison P a)).map (n + 1)
          (pointwisePrespectrumFamily F (n + 1) y ((prespectrum V).structureMap n x r)) = _
      rw [pointwisePrespectrumFamily_structure]
      rfl)
    (fun y ↦ by
      have hy : y = (default : |tipSSet.{u + 1}|) := Subsingleton.elim _ _
      subst y
      change coneEval P a E (n + 1) (tip E J F β) ((prespectrum V).structureMap n x r) =
        (nativeBassCone P a).structureMap n (coneEval P a E n (tip E J F β) x) r
      rw [coneEval_tip, coneEval_tip]
      exact (congrArg (fun p ↦ p r) ((nativeBassCone P a).map_point n)).symm)
  exact congrFun h z

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
