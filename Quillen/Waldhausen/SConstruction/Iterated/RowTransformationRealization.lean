/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationCylinder
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopy

/-! # The independently constructed first row with both original realization cylinders

The outer coordinate is the first-S row and the inner coordinate is the weak transformation.
The whole realized map agrees with the original structure map applied to that transformation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Opposite MonoidalCategory
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} {F G : V ⟶ W}
  (η : F.functor ⟶ G.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))

/-- Realize the actual finite coefficient cell with its two original intervals. -/
def rowTransformationRealization (k : ℕ) :
    C(unitInterval × (unitInterval × stageSpace k V), stageSpace (k + 1) W) :=
  ⟨fun z => SSet.toTop.map (rowTransformationCylinder η hη k)
    ((Quillen.realizationCylinderIso ((stages k).obj V ⊗ Δ[1])).inv
      ((Quillen.realizationCylinderIso ((stages k).obj V)).inv
        (z.2.2, ULift.up z.2.1), ULift.up z.1)), by fun_prop⟩

/-- The whole independent first row is the unchanged structure of the original track. -/
theorem rowTransformationRealization_structure (k : ℕ) (s t : unitInterval)
    (x : stageSpace k V) :
    rowTransformationRealization η hη k (s, (t, x)) =
      (prespectrum W).structureMap (k + 1)
        ((prespectrumTransformationHomotopy η hη).level (k + 1) (t, x)) s := by
  let A := (stages k).obj V
  let H := stageTransformationCylinder k η hη
  let p := (Quillen.realizationCylinderIso (A ⊗ Δ[1])).inv
    ((Quillen.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  have h := ConcreteCategory.congr_hom (Quillen.realizationCylinderIso_inv_naturality H)
    ((Quillen.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  change SSet.toTop.map (H ▷ Δ[1]) p =
    (Quillen.realizationCylinderIso _).inv
      (SSet.toTop.map H ((Quillen.realizationCylinderIso A).inv (x, ULift.up t)),
        ULift.up s) at h
  change SSet.toTop.map (rowTransformationCylinder η hη k) p = _
  rw [rowTransformationCylinder_eq, Functor.map_comp]
  change SSet.toTop.map (stageCylinder k W) (SSet.toTop.map (H ▷ Δ[1]) p) = _
  rw [h]
  rfl

end Quillen.Waldhausen.IteratedS
