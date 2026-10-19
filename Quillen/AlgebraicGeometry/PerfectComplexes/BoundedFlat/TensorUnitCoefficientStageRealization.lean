/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientStages

/-!
# Whole realization of every genuine finite tensor coefficient cell

The independently prolonged coefficient cells are realized with both original cylinder
isomorphisms. The resulting whole continuous maps are exactly the original structure maps of
the tensor-unit homotopy. The outer time is the coefficient S-row and the inner time is its
forward automorphism edge. No transposition or stable-group detection is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- Realize the actual finite coefficient cell, with its original two interval coordinates. -/
def tensorUnitPullbackCoefficientStageRealization (k : ℕ) :
    C(unitInterval × (unitInterval × stageSpace k (modelOf (boundedFlatPerfectWaldhausen Y))),
      stageSpace (k + 1) (modelOf (boundedFlatPerfectWaldhausen X))) :=
  ⟨fun z => SSet.toTop.map (tensorUnitPullbackCoefficientStageCylinder f r k)
    ((Quillen.realizationCylinderIso
      ((stages k).obj (modelOf (boundedFlatPerfectWaldhausen Y)) ⊗ Δ[1])).inv
      ((Quillen.realizationCylinderIso
        ((stages k).obj (modelOf (boundedFlatPerfectWaldhausen Y)))).inv
          (z.2.2, ULift.up z.2.1), ULift.up z.1)), by fun_prop⟩

/-- The whole realized finite tensor cell agrees with the unchanged original structure track. -/
theorem tensorUnitPullbackCoefficientStageRealization_structure (k : ℕ) (s t : unitInterval)
    (x : stageSpace k (modelOf (boundedFlatPerfectWaldhausen Y))) :
    tensorUnitPullbackCoefficientStageRealization f r k (s, (t, x)) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen X)).structureMap (k + 1)
        ((boundedFlatPerfectTensorUnitHomotopy f r).level (k + 1) (t, x)) s := by
  let A := (stages k).obj (modelOf (boundedFlatPerfectWaldhausen Y))
  let H := stageTransformationCylinder k (tensorUnitPullbackModelTransformation f r)
    (tensorUnitPullbackModelTransformation_weak f r)
  let p := (Quillen.realizationCylinderIso (A ⊗ Δ[1])).inv
    ((Quillen.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  have h := ConcreteCategory.congr_hom (Quillen.realizationCylinderIso_inv_naturality H)
    ((Quillen.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  change SSet.toTop.map (H ▷ Δ[1]) p =
    (Quillen.realizationCylinderIso _).inv
      (SSet.toTop.map H ((Quillen.realizationCylinderIso A).inv (x, ULift.up t)), ULift.up s) at h
  change SSet.toTop.map (tensorUnitPullbackCoefficientStageCylinder f r k) p = _
  rw [tensorUnitPullbackCoefficientStageCylinder_eq, Functor.map_comp]
  change SSet.toTop.map (stageCylinder k (modelOf (boundedFlatPerfectWaldhausen X)))
    (SSet.toTop.map (H ▷ Δ[1]) p) = _
  rw [h]
  rfl

/-- Equality of the complete continuous two-time maps, before taking any homotopy class. -/
theorem tensorUnitPullbackCoefficientStageRealization_eq (k : ℕ) :
    tensorUnitPullbackCoefficientStageRealization f r k =
      ⟨fun z => (originalPrespectrum (boundedFlatPerfectWaldhausen X)).structureMap (k + 1)
        ((boundedFlatPerfectTensorUnitHomotopy f r).level (k + 1) (z.2.1, z.2.2)) z.1,
        by fun_prop⟩ := by
  ext z
  exact tensorUnitPullbackCoefficientStageRealization_structure f r k z.1 z.2.1 z.2.2

end Quillen.PerfectComplexes
