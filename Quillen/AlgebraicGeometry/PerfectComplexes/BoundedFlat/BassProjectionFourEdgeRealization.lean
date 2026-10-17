/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteEdge
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeMap

/-!
# Realizing the four original Bass edges over a whole reference

The actual simplicial edge map, evaluated through the original cylinder inverse, is the
five-node whole-reference family at its unchanged affine edge parameter.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
open BassH0Merge CommonReferenceNerve
attribute [local irreducible] boundedFlatNormalizedPullback
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))

/-- The complete realized edge retains every input node, its reference, and the old clock. -/
theorem edgeMap_realization (i j : Fin 5) (hij : i ≤ j)
    (x : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (t : unitInterval) :
    SSet.toTop.map (edgeMap P a E i j)
        ((realizationCylinderIso (nerve (Codiscrete (CommonReferenceNerve.Node E)))).inv
          (x, ULift.up t)) =
      FiniteParameter.parameter E (reference P a E) (nodes P a E)
        (x, SimplexParameters.edge i j t) :=
  FiniteParameter.simplicial_edge E (reference P a E) (nodes P a E)
    (edgeFace i j hij) x t

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
