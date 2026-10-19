/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientRealization
public import Quillen.Waldhausen.SmallModel.Double

/-!
# The actual coefficient cell in the original small-model S-prespectrum

Transport the independently constructed first coefficient cell by the original small-model
maps, including the actual exact postcomposition of both quotient-row directions. The complete
result is the original stage-zero tensor transformation followed by the original stage-cylinder.
This is a whole simplicial map identity, with neither time coordinate interchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- Apply precisely the original small-model transport on the input and both output S-directions.
-/
def tensorUnitPullbackSmallCoefficientCylinder :
    (((stages 0).obj (modelOf (boundedFlatPerfectWaldhausen Y))) ⊗ Δ[1]) ⊗ Δ[1] ⟶
      (stages 1).obj (modelOf (boundedFlatPerfectWaldhausen X)) :=
  (((boundedFlatPerfectWaldhausen Y).smallModelSSetIso.inv ▷ Δ[1]) ▷ Δ[1]) ≫
    tensorUnitPullbackCoefficientCylinder f r ≫
      (boundedFlatPerfectWaldhausen X).smallModelDoubleDiagonalMap

/-- The complete actual cell is the original normalized tensor track with its structure cylinder.
-/
theorem tensorUnitPullbackSmallCoefficientCylinder_eq :
    tensorUnitPullbackSmallCoefficientCylinder f r =
      (stageTransformationCylinder 0 (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) ▷ Δ[1]) ≫
        stageCylinder 0 (modelOf (boundedFlatPerfectWaldhausen X)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  change tensorUnitPullbackNormalizedCoefficientPrism f r (z.1.1.val ⋙ AsSmall.down)
      z.1.2.down z.2.down ⋙
        postcompose (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectWaldhausen X).smallModel
          (boundedFlatPerfectWaldhausen X).smallModel_up_exact n.unop =
    nerveCylinderDiagram (whiskerLeft z.1.1.val (tensorUnitPullbackModelTransformation f r))
      z.1.2.down ⋙ suspensionRow (boundedFlatPerfectWaldhausen X).smallModel z.2.down
  rw [tensorUnitPullbackNormalizedCoefficientPrism_eq, Functor.assoc,
    (boundedFlatPerfectWaldhausen X).smallModel_suspensionRow]
  rw [← Functor.assoc, ← iteratedNerveCylinderDiagram_postcomp]
  rfl

end Quillen.PerfectComplexes
