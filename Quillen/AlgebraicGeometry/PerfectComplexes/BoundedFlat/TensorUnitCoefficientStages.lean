/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientSmallModel
public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationCylinder

/-!
# Finite S-prolongation of the genuine first tensor coefficient cell

Apply the original finite S-construction to the actual normalized coefficient-row arrow. The
first-row insertion is kept after the tensor pullback, and the forward unit edge is prolonged
entrywise through the original quotient grids. At stage zero the whole cell is the independent
raw tensor construction, transported by the original small-model maps. At every stage its whole
simplicial map equals the original tensor cylinder followed by the original structure cylinder.
The two interval directions are never interchanged.
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

/-- Apply the genuine finite S-construction to the normalized first-row tensor arrow. -/
def tensorUnitPullbackCoefficientStageSimplex (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages k).obj (modelOf (boundedFlatPerfectWaldhausen Y))).obj n)
    (τ θ : (Δ[1]).obj n) :
    ((stages (k + 1)).obj (modelOf (boundedFlatPerfectWaldhausen X))).obj n :=
  stageTransformationFunction k
    (F := tensorUnitPullbackModelMap f ≫
      (insertion θ.down).app (modelOf (boundedFlatPerfectWaldhausen X)))
    (G := tensorUnitPullbackModelMap f ≫
      (insertion θ.down).app (modelOf (boundedFlatPerfectWaldhausen X)))
    (whiskerRight (tensorUnitPullbackModelTransformation f r)
      ((insertion θ.down).app (modelOf (boundedFlatPerfectWaldhausen X))).functor)
    (fun B => ((insertion θ.down).app (modelOf (boundedFlatPerfectWaldhausen X))).exact.weak _
      (tensorUnitPullbackModelTransformation_weak f r B)) n A τ

/-- Entrywise finite S-prolongation preserves the whole tensor-arrow/first-row composite. -/
theorem tensorUnitPullbackCoefficientStageSimplex_eq (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages k).obj (modelOf (boundedFlatPerfectWaldhausen Y))).obj n)
    (τ θ : (Δ[1]).obj n) :
    tensorUnitPullbackCoefficientStageSimplex f r k n A τ θ =
      (stageCylinder k (modelOf (boundedFlatPerfectWaldhausen X))).app n
        (stageTransformationFunction k (tensorUnitPullbackModelTransformation f r)
          (tensorUnitPullbackModelTransformation_weak f r) n A τ, θ) :=
  stageTransformationFunction_postcomp k (tensorUnitPullbackModelTransformation f r)
    (tensorUnitPullbackModelTransformation_weak f r)
    ((insertion θ.down).app (modelOf (boundedFlatPerfectWaldhausen X))) n A τ

/-- The actual finite coefficient cells assemble under all diagonal simplicial operators. -/
def tensorUnitPullbackCoefficientStageCylinder (k : ℕ) :
    (((stages k).obj (modelOf (boundedFlatPerfectWaldhausen Y))) ⊗ Δ[1]) ⊗ Δ[1] ⟶
      (stages (k + 1)).obj (modelOf (boundedFlatPerfectWaldhausen X)) :=
  rowTransformationCylinder (tensorUnitPullbackModelTransformation f r)
    (tensorUnitPullbackModelTransformation_weak f r) k

/-- This is a whole simplicial-map identity, not an equality merely on homotopy classes. -/
theorem tensorUnitPullbackCoefficientStageCylinder_eq (k : ℕ) :
    tensorUnitPullbackCoefficientStageCylinder f r k =
      (stageTransformationCylinder k (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) ▷ Δ[1]) ≫
        stageCylinder k (modelOf (boundedFlatPerfectWaldhausen X)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact tensorUnitPullbackCoefficientStageSimplex_eq f r k n z.1.1 z.1.2 z.2

/-- The starting cell is exactly the independently constructed genuine coefficient tensor row. -/
theorem tensorUnitPullbackCoefficientStageCylinder_zero :
    tensorUnitPullbackCoefficientStageCylinder f r 0 =
      tensorUnitPullbackSmallCoefficientCylinder f r := by
  rw [tensorUnitPullbackCoefficientStageCylinder_eq,
    tensorUnitPullbackSmallCoefficientCylinder_eq]

end Quillen.PerfectComplexes
