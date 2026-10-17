/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgePath

/-! The unreduced cone retains the entire Laurent nerve and every tree baseline point. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
open CutOpenCarrier
variable {V W T U : Model.{u}} (E : V ⟶ W) (J : W ⟶ T) (F : V ⟶ U)
  (β : simplicial E J ⟶ parameterSSet F)

/-- The realization of the four-edge cone with full reference attachment `β`. -/
abbrev coneSpace : TopCat.{u} := |cone E J F β|

/-- The inclusion of the full reference parameter space into the realized four-edge cone. -/
def laurentInclusion : C(|parameterSSet F|, coneSpace E J F β) :=
  (SSet.toTop.map (coneLaurent E J F β)).hom

/-- The realized cone cylinder over the four-edge tree with its original interval coordinate. -/
def cylinder : C(space E J × unitInterval, coneSpace E J F β) :=
  realizedEdge (coneCylinder E J F β)

/-- The terminal tip of the realized unreduced four-edge cone. -/
def tip : coneSpace E J F β := SSet.toTop.map (coneTip E J F β) (default : |tipSSet.{u}|)

/-- Every baseline point retains its own whole reference image under β. -/
theorem cone_cylinder_zero (z : space E J) :
    cylinder E J F β (z, 0) = laurentInclusion E J F β (SSet.toTop.map β z) := by
  change realizedEdge (coneCylinder E J F β) (z, 0) = _
  rw [realizedEdge_zero, coneCylinder_zero, Functor.map_comp]
  rfl

/-- Only the terminal cone face is sent to the cone tip. -/
theorem cone_cylinder_one (z : space E J) : cylinder E J F β (z, 1) = tip E J F β := by
  change realizedEdge (coneCylinder E J F β) (z, 1) = _
  rw [realizedEdge_one, coneCylinder_one, Functor.map_comp]
  exact congrArg (fun t ↦ SSet.toTop.map (coneTip E J F β) t)
    (Subsingleton.elim _ (default : |tipSSet.{u}|))

/-- The actual four-quarter overlap travels inside the full baseline of the unreduced cone. -/
def overlapCylinder :
    C((|parameterSSet E| × unitInterval) × unitInterval, coneSpace E J F β) :=
  ⟨fun z ↦ cylinder E J F β (overlap E J z.1, z.2), by fun_prop⟩

theorem overlapCylinder_zero (e : |parameterSSet E|) (s : unitInterval) :
    overlapCylinder E J F β ((e, s), 0) =
      laurentInclusion E J F β (SSet.toTop.map β (overlap E J (e, s))) :=
  cone_cylinder_zero E J F β _

theorem overlapCylinder_one (e : |parameterSSet E|) (s : unitInterval) :
    overlapCylinder E J F β ((e, s), 1) = tip E J F β := cone_cylinder_one E J F β _

/-- Contractibility concerns this same unreduced realization, without a baseline quotient. -/
theorem coneSpace_contractible : ContractibleSpace (coneSpace E J F β) :=
  cone_contractibleSpace E J F β

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
