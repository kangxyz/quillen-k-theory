/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientCylinder
public import Quillen.Waldhausen.SConstruction.Iterated.HomotopyTransport

/-!
# Realization of the actual fixed tensor coefficient cell

Realize the independently constructed and zero-normalized first coefficient cell using the
original two cylinder isomorphisms. Its whole value is the original suspension row applied to the
original normalized tensor-unit track. The coefficient object-row time and the forward unit
nerve time stay in their specified order. The original small-model transport identifies the
inner track with the existing tensor-unit prespectrum homotopy at level one.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- Realize the actual fixed coefficient cell: outer time is its S-row, inner time its unit edge. -/
def tensorUnitPullbackCoefficientRealization :
    C(unitInterval × (unitInterval × (boundedFlatPerfectWaldhausen Y).Delooping),
      |doubleDiagonal (boundedFlatPerfectWaldhausen X)|) :=
  ⟨fun z => SSet.toTop.map (tensorUnitPullbackCoefficientCylinder f r)
    ((Quillen.realizationCylinderIso
      (sSet (boundedFlatPerfectWaldhausen Y).cof (boundedFlatPerfectWaldhausen Y).weq ⊗ Δ[1])).inv
      ((Quillen.realizationCylinderIso
        (sSet (boundedFlatPerfectWaldhausen Y).cof (boundedFlatPerfectWaldhausen Y).weq)).inv
          (z.2.2, ULift.up z.2.1), ULift.up z.1)), by fun_prop⟩

/-- The full realized cell is the original suspension row of the original normalized tensor track.
-/
theorem tensorUnitPullbackCoefficientRealization_eq (s t : unitInterval)
    (x : (boundedFlatPerfectWaldhausen Y).Delooping) :
    tensorUnitPullbackCoefficientRealization f r (s, (t, x)) =
      loopStructureMap (boundedFlatPerfectWaldhausen X)
        (weakNaturalTransformationRealizationHomotopy
          (boundedFlatPerfectWaldhausen Y) (boundedFlatPerfectWaldhausen X)
          (boundedFlatPerfectTensorUnitPullback_exact f).rebase
          (boundedFlatPerfectTensorUnitPullback_exact f).rebase
          (normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact f)
            (boundedFlatPerfectTensorUnitPullback_exact f)
            (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
          (normalizedWeakTransformation_weak (boundedFlatPerfectTensorUnitPullback_exact f)
            (boundedFlatPerfectTensorUnitPullback_exact f)
            (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom
            (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)) (t, x)) s := by
  let A := sSet (boundedFlatPerfectWaldhausen Y).cof (boundedFlatPerfectWaldhausen Y).weq
  let H := tensorUnitPullbackNormalizedCylinder f r
  let p := (Quillen.realizationCylinderIso (A ⊗ Δ[1])).inv
    ((Quillen.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  have h := ConcreteCategory.congr_hom (Quillen.realizationCylinderIso_inv_naturality H)
    ((Quillen.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  change SSet.toTop.map (H ▷ Δ[1]) p =
    (Quillen.realizationCylinderIso _).inv
      (SSet.toTop.map H ((Quillen.realizationCylinderIso A).inv (x, ULift.up t)), ULift.up s) at h
  change SSet.toTop.map (tensorUnitPullbackCoefficientCylinder f r) p = _
  rw [tensorUnitPullbackCoefficientCylinder_eq, Functor.map_comp]
  change SSet.toTop.map (suspensionCylinder (boundedFlatPerfectWaldhausen X))
    (SSet.toTop.map (H ▷ Δ[1]) p) = _
  rw [h]
  rfl

/-- The inner coefficient-edge track is the unchanged original tensor prespectrum track. -/
theorem tensorUnitPullbackNormalizedRealization_track (t : unitInterval)
    (x : (boundedFlatPerfectWaldhausen Y).Delooping) :
    (boundedFlatPerfectTensorUnitHomotopy f r).level 1
        (t, (boundedFlatPerfectWaldhausen Y).smallModelDeloopingHomeomorph x) =
      (boundedFlatPerfectWaldhausen X).smallModelDeloopingHomeomorph
        (weakNaturalTransformationRealizationHomotopy
          (boundedFlatPerfectWaldhausen Y) (boundedFlatPerfectWaldhausen X)
          (boundedFlatPerfectTensorUnitPullback_exact f).rebase
          (boundedFlatPerfectTensorUnitPullback_exact f).rebase
          (normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact f)
            (boundedFlatPerfectTensorUnitPullback_exact f)
            (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
          (normalizedWeakTransformation_weak (boundedFlatPerfectTensorUnitPullback_exact f)
            (boundedFlatPerfectTensorUnitPullback_exact f)
            (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom
            (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)) (t, x)) :=
  originalPrespectrumTransformationHomotopy_level_one _ _
    (boundedFlatPerfectTensorUnitPullback_exact f).rebase
    (boundedFlatPerfectTensorUnitPullback_exact f).rebase _ _
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _) t x

/-- The realized fixed cell retains both times and the original prespectrum-track normalization. -/
theorem tensorUnitPullbackCoefficientRealization_track (s t : unitInterval)
    (x : (boundedFlatPerfectWaldhausen Y).Delooping) :
    tensorUnitPullbackCoefficientRealization f r (s, (t, x)) =
      loopStructureMap (boundedFlatPerfectWaldhausen X)
        ((boundedFlatPerfectWaldhausen X).smallModelDeloopingHomeomorph.symm
          ((boundedFlatPerfectTensorUnitHomotopy f r).level 1
            (t, (boundedFlatPerfectWaldhausen Y).smallModelDeloopingHomeomorph x))) s := by
  rw [tensorUnitPullbackNormalizedRealization_track, Homeomorph.symm_apply_apply]
  exact tensorUnitPullbackCoefficientRealization_eq f r s t x

end Quillen.PerfectComplexes
