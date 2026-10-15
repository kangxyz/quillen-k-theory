/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.ExactCategory.ExtensionIdentityQuotient
public import Quillen.CategoryTheory.ExactCategory.ExtensionProjectionFunctor
public import Quillen.Topology.ClassifyingSpace.ExtensionTotal
public import Quillen.Topology.ClassifyingSpace.AsSmall
/-! # The original Q projection and its specified basepoint path -/
@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject
noncomputable section
universe u v
namespace CategoryTheory.ExactCategory.ExactStructure
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)
/-- The actual extension projection, realized without changing either original space. -/
def extensionProjectionRealization :
    ContinuousMap (ClassifyingSpace E.ExtensionTotal)
      (ClassifyingSpace (Q E.deflation E.inflation)) :=
  let e := Quillen.GroupoidClassifying.asSmallClassifyingHomeomorph E.ExtensionTotal
  let f := Quillen.GroupoidClassifying.asSmallClassifyingHomeomorph
    (Q E.deflation E.inflation)
  (⟨f.symm, f.symm.continuous⟩ : ContinuousMap _ _).comp
    ((classifyingSpaceMap (AsSmall.down ⋙ E.extensionProjection ⋙ AsSmall.up)).hom.comp
      ⟨e, e.continuous⟩)

/-- The realized map retains the original quotient-object vertex. -/
@[simp] theorem extensionProjectionRealization_point (x : E.ExtensionTotal) :
    E.extensionProjectionRealization (classifyingSpacePoint x) =
      classifyingSpacePoint (E.extensionProjection.obj x) := by
  dsimp only [extensionProjectionRealization, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [Quillen.GroupoidClassifying.asSmallClassifyingHomeomorph_point,
    classifyingSpaceMap_point]
  change (Quillen.GroupoidClassifying.asSmallClassifyingHomeomorph
    (Q E.deflation E.inflation)).symm
      (classifyingSpacePoint (AsSmall.up.obj (E.extensionProjection.obj x))) = _
  rw [← Quillen.GroupoidClassifying.asSmallClassifyingHomeomorph_point,
    Homeomorph.symm_apply_apply]

/-- The canonical quotient isomorphism supplies the precise path to the original zero vertex. -/
def extensionProjectionBasepointPath :
    Path (E.extensionProjectionRealization
      (classifyingSpacePoint E.extensionTotalPoint))
      (classifyingSpacePoint (Q.of E.deflation E.inflation (0 : C))) := by
  rw [extensionProjectionRealization_point]
  exact classifyingSpacePath (E.identityProjectionIsoZero (0 : C)).hom
end CategoryTheory.ExactCategory.ExactStructure
