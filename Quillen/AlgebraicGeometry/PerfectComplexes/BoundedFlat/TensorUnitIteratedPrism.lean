/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitNervePrism

/-!
# Original normalization and structure operators of the restricted tensor prism

The coefficient crossing is written in every original complex degree, with the two canonical
zero-normalization isomorphisms retained. Original small-model transport and quotient-row
prolongation then give the actual iterated-S cylinder. Its original structure parameter is
independent of the coefficient-edge parameter, including at level zero.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes

/-- The actual coefficient tensor on each term of every original pulled-back complex. -/
theorem boundedFlatPerfectTensorUnitPullbackAutomorphism_hom_f {X Y : Scheme.{u}}
    (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) (K : BoundedFlatPerfect Y) (n : ℤ) :
    ((boundedFlatPerfect X).ι.map
      ((boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom.app K)).f n =
      (moduleTensorCoefficientMap X (unitMul X r)).app
        (((boundedFlatPerfectPullback f).obj K).obj.X n) := by
  change ((boundedFlatPerfect X).ι.map
    ((boundedFlatPerfectTensorUnitAutomorphism X r).hom.app
      ((boundedFlatPerfectPullback f).obj K))).f n = _
  rw [boundedFlatPerfectTensorUnitAutomorphism_hom_original,
    complexTensorUnitAutomorphism_hom_f]

/-- The fixed original zero normalization of genuine tensor-unit pullback. -/
def tensorUnitPullbackNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Quillen.rebaseFunctorIso (boundedFlatPerfectTensorUnitPullback f)
    (boundedFlatPerfectWaldhausen Y).zero (boundedFlatPerfectWaldhausen X).zero
    (((boundedFlatPerfectTensorUnitPullback_exact f).zero
      (boundedFlatPerfectWaldhausen Y).isZero).iso (boundedFlatPerfectWaldhausen X).isZero)

/-- Every normalized grid crossing retains the actual tensor coefficient between the two
original zero-normalization components. -/
theorem tensorUnitPullbackNormalized_crossing_f {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (K : BoundedFlatPerfect Y) (n : ℤ) :
    ((boundedFlatPerfect X).ι.map
      ((normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact f)
        (boundedFlatPerfectTensorUnitPullback_exact f)
        (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom).app K)).f n =
      ((boundedFlatPerfect X).ι.map ((tensorUnitPullbackNormalization f).inv.app K)).f n ≫
        (moduleTensorCoefficientMap X (unitMul X r)).app
          (((boundedFlatPerfectPullback f).obj K).obj.X n) ≫
        ((boundedFlatPerfect X).ι.map ((tensorUnitPullbackNormalization f).hom.app K)).f n := by
  simp only [normalizedWeakTransformation, NatTrans.comp_app, Functor.map_comp,
    HomologicalComplex.comp_f, boundedFlatPerfectTensorUnitPullbackAutomorphism_hom_f]
  rfl

/-- The original canonically based model map underlying the unchanged exact tensor spectrum map. -/
def tensorUnitPullbackModelMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modelOf (boundedFlatPerfectWaldhausen Y) ⟶ modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ (boundedFlatPerfectTensorUnitPullback_exact f).rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _)

/-- The actual coefficient crossing with precisely the existing small-model and zero transports. -/
def tensorUnitPullbackModelTransformation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    (tensorUnitPullbackModelMap f).functor ⟶ (tensorUnitPullbackModelMap f).functor :=
  whiskerLeft AsSmall.down (whiskerRight
    (normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact f)
      (boundedFlatPerfectTensorUnitPullback_exact f)
      (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom) AsSmall.up)

/-- Weak equivalences of the original tensor edge survive the specified canonical transports. -/
theorem tensorUnitPullbackModelTransformation_weak {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (A : modelOf (boundedFlatPerfectWaldhausen Y)) :
    (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq
      ((tensorUnitPullbackModelTransformation f r).app A) :=
  normalizedWeakTransformation_weak (boundedFlatPerfectTensorUnitPullback_exact f)
    (boundedFlatPerfectTensorUnitPullback_exact f)
    (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance) (AsSmall.down.obj A)

/-- Prolongation acts on each original quotient-row entry by that same coefficient crossing. -/
theorem tensorUnitPullback_rows_component {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (n : SimplexCategory)
    (A : (rows n).obj (modelOf (boundedFlatPerfectWaldhausen Y))) (p : Interval n) :
    ((rowsTransformation (tensorUnitPullbackModelTransformation f r) n).app A).hom.app p =
      (tensorUnitPullbackModelTransformation f r).app (A.obj.obj p) := rfl

/-- Every finite tensor prism commutes with the original suspension-row structure operator;
the coefficient edge and structure simplex parameters remain independent. -/
theorem tensorUnitPullback_prism_structure {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages k).obj (modelOf (boundedFlatPerfectWaldhausen Y))).obj n)
    (τ θ : (Δ[1]).obj n) :
    stageTransformationFunction (k + 1) (tensorUnitPullbackModelTransformation f r)
      (tensorUnitPullbackModelTransformation_weak f r) n
      ((stageCylinder k (modelOf (boundedFlatPerfectWaldhausen Y))).app n (A, τ)) θ =
    (stageCylinder k (modelOf (boundedFlatPerfectWaldhausen X))).app n
      (stageTransformationFunction k (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) n A θ, τ) :=
  stageTransformationFunction_structure k (tensorUnitPullbackModelTransformation f r)
    (tensorUnitPullbackModelTransformation_weak f r) n A τ θ

/-- The realized positive levels are literally the unchanged iterated-S tensor prisms. -/
theorem tensorUnitPullback_homotopy_succ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (k : ℕ) (s : unitInterval)
    (x : stageSpace k (modelOf (boundedFlatPerfectWaldhausen Y))) :
    (boundedFlatPerfectTensorUnitHomotopy f r).level (k + 1) (s, x) =
      stageTransformationTopHomotopy k (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) (s, x) := rfl

/-- Level zero retains the original loop coordinate, independently of coefficient-edge time. -/
theorem tensorUnitPullback_homotopy_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (s t : unitInterval)
    (x : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen X)))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen X))) from
        (boundedFlatPerfectTensorUnitHomotopy f r).level 0 (s, x)) t =
      stageTransformationTopHomotopy 0 (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) (s, x t) := rfl

end Quillen.PerfectComplexes
