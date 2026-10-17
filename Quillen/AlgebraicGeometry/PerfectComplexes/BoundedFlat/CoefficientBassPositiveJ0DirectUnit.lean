/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0RectangleRails
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveDependentTransport

/-!
# Entire direct-Laurent unit family in the original common carrier

Transport uses the actual polynomialUnderCoefficient_toLaurent equation and the specified
actualSourceReferenceEq. No isomorphisms with different endpoints are identified definitionally.
The whole ten-node simplex is preserved, not merely its outer path or evaluator.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0DirectUnit
open CommonReferenceNerve BassH0Merge CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveJ0Rectangles CoefficientBassPositiveJ0RectangleRails
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- All ten dependent nodes retain their actual reference under the original p;q=l equation. -/
theorem full_nodes (i : Fin 10) :
    anchorNode (eqToIso (BassH0Merge.reference_eq P (firstArrow d) (secondArrow d)))
      (CoefficientLaurentUnitTenNodes.nodes P ((firstArrow d) ≫ (secondArrow d)) i) =
    anchorNode (eqToIso (CoefficientBassPositiveC0TenNodes.actualSourceReferenceEq P d))
      (CoefficientLaurentUnitTenNodes.nodes P ((laurentUnderCoefficient R).app d) i) := by
  have h := reanchorNodes_index_eq
    (fun w : d ⟶ (laurentUnderFunctor R).obj d ↦ CoefficientLaurentUnitTenNodes.source P w)
    (fun w ↦ CoefficientLaurentUnitTenNodes.nodes P w)
    (polynomialUnderCoefficient_toLaurent R d) (laurentRef P d)
    (BassH0Merge.reference_eq P (firstArrow d) (secondArrow d))
    (CoefficientBassPositiveC0TenNodes.actualSourceReferenceEq P d)
  exact congrFun h i

/-- The exact direct-l TenNodes simplex, with the original actual source-reference cast. -/
def directUnitMap : C(StdSimplex ℝ (Fin 10), Carrier P d) :=
  (CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
    (ordinary P d) (shifted P d)).comp
    ((mapParameter (anchorNode
      (eqToIso (CoefficientBassPositiveC0TenNodes.actualSourceReferenceEq P d)))).comp
      (parameter (CoefficientLaurentUnitTenNodes.source P ((laurentUnderCoefficient R).app d))
        (CoefficientLaurentUnitTenNodes.nodes P ((laurentUnderCoefficient R).app d))))

/-- The complete common carrier characteristic map agrees, at every ten-node simplex point. -/
theorem unitMap_direct : unitMap P d = directUnitMap P d := by
  apply ContinuousMap.ext
  intro z
  change CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) (mapParameter _ (parameter _ _ z)) =
    CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) (mapParameter _ (parameter _ _ z))
  rw [mapParameter_parameter, mapParameter_parameter]
  exact congrArg (CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d)
    (laurentRef P d) (ordinary P d) (shifted P d))
    (congrArg (fun N : Fin 10 → Node (laurentRef P d) ↦
      parameter (laurentRef P d) N z) (funext (full_nodes P d)))

/-- The whole ordinary outer rail uses the actual direct-l unit word without reparametrization. -/
theorem outerMinus_direct (s : I) :
    laurentMovementMinus P d s = directUnitMap P d
      ((CoefficientLaurentUnitTenNodes.C0.symm.trans CoefficientLaurentUnitTenNodes.D0) s) := by
  rw [← unitMap_direct]
  exact outerMinus P d s

/-- The whole shifted outer rail uses the original forward-unit word and the same direct cast. -/
theorem outerPlus_direct (s : I) :
    laurentMovementPlus P d s = directUnitMap P d
      ((CoefficientLaurentUnitTenNodes.C1.symm.trans CoefficientLaurentUnitTenNodes.D1) s) := by
  rw [← unitMap_direct]
  exact outerPlus P d s

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0DirectUnit
