/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientCylinder
public import Quillen.Waldhausen.SmallModel.Double
public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationCylinder

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
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T)

/-- The original canonically based model map underlying the unchanged exact tensor spectrum map. -/
def tensorSupportedPairModelMap :
    modelOf (boundedFlatPerfectSupportedWaldhausen T.obj.hom) ⟶
      modelOf (boundedFlatPerfectSupportedWaldhausen S.obj.hom) :=
  modelMap _ _ (tensorSupportedPair_exact p).rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _)

/-- The actual coefficient crossing with precisely the existing small-model and zero transports. -/
def tensorSupportedPairModelTransformation
    (r : (Γ(S.obj.right, ⊤))ˣ) :
    (tensorSupportedPairModelMap p).functor ⟶ (tensorSupportedPairModelMap p).functor :=
  whiskerLeft AsSmall.down (whiskerRight
    (normalizedWeakTransformation (tensorSupportedPair_exact p)
      (tensorSupportedPair_exact p)
      (tensorSupportedPairAutomorphism p r).hom) AsSmall.up)

/-- Weak equivalences of the original tensor edge survive the specified canonical transports. -/
theorem tensorSupportedPairModelTransformation_weak
    (r : (Γ(S.obj.right, ⊤))ˣ) (A : modelOf (boundedFlatPerfectSupportedWaldhausen T.obj.hom)) :
    (modelOf (boundedFlatPerfectSupportedWaldhausen S.obj.hom)).waldhausen.weq
      ((tensorSupportedPairModelTransformation p r).app A) :=
  normalizedWeakTransformation_weak (tensorSupportedPair_exact p)
    (tensorSupportedPair_exact p)
    (tensorSupportedPairAutomorphism p r).hom
    (fun _ ↦ (boundedFlatPerfectSupportedWaldhausen S.obj.hom).weq_iso _ inferInstance)
    (AsSmall.down.obj A)

variable (r : (Γ(S.obj.right, ⊤))ˣ)

/-- Apply precisely the original small-model transport on the input and both output S-directions.
-/
def tensorSupportedPairSmallCoefficientCylinder :
    (((stages 0).obj (modelOf (boundedFlatPerfectSupportedWaldhausen T.obj.hom))) ⊗ Δ[1]) ⊗ Δ[1] ⟶
      (stages 1).obj (modelOf (boundedFlatPerfectSupportedWaldhausen S.obj.hom)) :=
  (((boundedFlatPerfectSupportedWaldhausen T.obj.hom).smallModelSSetIso.inv ▷ Δ[1]) ▷ Δ[1]) ≫
    tensorSupportedPairCoefficientCylinder p r ≫
      (boundedFlatPerfectSupportedWaldhausen S.obj.hom).smallModelDoubleDiagonalMap

/-- The complete actual cell is the original normalized tensor track with its structure cylinder.
-/
theorem tensorSupportedPairSmallCoefficientCylinder_eq :
    tensorSupportedPairSmallCoefficientCylinder p r =
      (stageTransformationCylinder 0 (tensorSupportedPairModelTransformation p r)
        (tensorSupportedPairModelTransformation_weak p r) ▷ Δ[1]) ≫
        stageCylinder 0 (modelOf (boundedFlatPerfectSupportedWaldhausen S.obj.hom)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  change tensorSupportedPairNormalizedCoefficientPrism p r (z.1.1.val ⋙ AsSmall.down)
      z.1.2.down z.2.down ⋙
        postcompose (boundedFlatPerfectSupportedWaldhausen S.obj.hom)
          (boundedFlatPerfectSupportedWaldhausen S.obj.hom).smallModel
          (boundedFlatPerfectSupportedWaldhausen S.obj.hom).smallModel_up_exact n.unop =
    nerveCylinderDiagram (whiskerLeft z.1.1.val (tensorSupportedPairModelTransformation p r))
      z.1.2.down ⋙
      suspensionRow (boundedFlatPerfectSupportedWaldhausen S.obj.hom).smallModel z.2.down
  rw [tensorSupportedPairNormalizedCoefficientPrism_eq, Functor.assoc,
    (boundedFlatPerfectSupportedWaldhausen S.obj.hom).smallModel_suspensionRow]
  rw [← Functor.assoc, ← iteratedNerveCylinderDiagram_postcomp]
  rfl

/-- The independent supported cell is the genuine original first-row transformation cylinder. -/
theorem tensorSupportedPairSmallCoefficientCylinder_row :
    tensorSupportedPairSmallCoefficientCylinder p r =
      rowTransformationCylinder (tensorSupportedPairModelTransformation p r)
        (tensorSupportedPairModelTransformation_weak p r) 0 := by
  rw [rowTransformationCylinder_eq, tensorSupportedPairSmallCoefficientCylinder_eq]

end Quillen.PerfectComplexes
