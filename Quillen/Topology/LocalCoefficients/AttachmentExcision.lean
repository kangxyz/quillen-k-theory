/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CylinderAttachment.RelativeCharts
public import Quillen.Topology.LocalCoefficients.RelativeSubspaceInclusion
public import Quillen.Topology.LocalCoefficients.RelativeOpenRestriction

/-!
# Original-map twisted relative excision for a two-ended cylinder attachment

For the actual pushout attaching both cylinder ends to one base, the original
characteristic map induces a quasi-isomorphism from the actual cylinder-boundary
pair to the actual attachment-base-image pair, for every target local system.
The attaching maps may be arbitrary and their images may meet. The proof uses the
verified open collars, their actual deformation retractions, the genuine interior
homeomorphism, and original-map open excision. It does not assume a homology
fibration criterion or any homology equivalence of the attaching maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory
universe u
namespace Quillen.LocalCoefficients

variable {A B D : TopCat.{u}} (f₀ f₁ : A ⟶ B)
  {l : A ⊗ TopCat.I ⟶ D} {e : B ⟶ D}
  (sq : IsPushout (Quillen.intervalEndpoints A) (CylinderAttachment.endMap f₀ f₁) l e)

/-- The original cell map gives a quasi-isomorphism between the actual open-collar pairs. -/
theorem attachmentCell_collar_relative_quasiIso (cut : ℝ) (hpos : 0 < cut)
    (L : System.{u, u} D) :
    QuasiIso (relativePushforwardChainMap l.hom
      (CylinderAttachment.sourceCollar A cut) (CylinderAttachment.collarSet f₀ f₁ sq cut)
      (CylinderAttachment.cell_mapsTo_collar f₀ f₁ sq cut) L) := by
  apply relativePushforwardChainMap_quasiIso_of_openRestriction l.hom
    (CylinderAttachment.sourceInterior A) (CylinderAttachment.sourceCollar A cut)
    (CylinderAttachment.interiorSet f₀ f₁ sq) (CylinderAttachment.collarSet f₀ f₁ sq cut)
    (CylinderAttachment.cell_mapsTo_interior f₀ f₁ sq)
    (CylinderAttachment.cell_mapsTo_collar f₀ f₁ sq cut) L
    (CylinderAttachment.sourceInterior_isOpen A) (CylinderAttachment.sourceCollar_isOpen A cut)
    (CylinderAttachment.sourceInterior_union_collar A cut hpos)
    (CylinderAttachment.interior_isOpen f₀ f₁ sq)
    (CylinderAttachment.collar_isOpen f₀ f₁ sq cut)
    (by rw [Set.union_comm]; exact CylinderAttachment.collar_union_interior f₀ f₁ sq cut hpos)
  apply relativePushforwardChainMap_quasiIso_of_homotopyEquiv
    (subspaceMap l.hom (CylinderAttachment.sourceInterior A)
      (CylinderAttachment.interiorSet f₀ f₁ sq)
      (CylinderAttachment.cell_mapsTo_interior f₀ f₁ sq))
    (intersectionInSubspace (CylinderAttachment.sourceInterior A)
      (CylinderAttachment.sourceCollar A cut))
    (intersectionInSubspace (CylinderAttachment.interiorSet f₀ f₁ sq)
      (CylinderAttachment.collarSet f₀ f₁ sq cut))
    (fun _ hx ↦ CylinderAttachment.cell_mapsTo_collar f₀ f₁ sq cut hx)
    (pullback (subspaceInclusion (CylinderAttachment.interiorSet f₀ f₁ sq)) L)
    (CylinderAttachment.cellInteriorHomeomorph f₀ f₁ sq).toHomotopyEquiv
    (by apply ContinuousMap.ext; intro z; apply Subtype.ext; rfl)
    (CylinderAttachment.cellInteriorCollarHomeomorph f₀ f₁ sq cut).toHomotopyEquiv
    (by apply ContinuousMap.ext; intro z; apply Subtype.ext; apply Subtype.ext; rfl)

/-- The exact square of original relative maps before and after collar enlargement. -/
theorem attachmentCell_relative_collar_square (cut : ℝ) (hpos : 0 < cut)
    (L : System.{u, u} D) :
    relativeSubspaceInclusion (CylinderAttachment.sourceBoundary A)
        (CylinderAttachment.sourceCollar A cut)
        (CylinderAttachment.sourceBoundary_subset_collar A cut hpos) (pullback l.hom L) ≫
      relativePushforwardChainMap l.hom (CylinderAttachment.sourceCollar A cut)
        (CylinderAttachment.collarSet f₀ f₁ sq cut)
        (CylinderAttachment.cell_mapsTo_collar f₀ f₁ sq cut) L =
    relativePushforwardChainMap l.hom (CylinderAttachment.sourceBoundary A)
        (CylinderAttachment.baseImage (e := e))
        (CylinderAttachment.cell_mapsTo_boundary f₀ f₁ sq) L ≫
      relativeSubspaceInclusion (CylinderAttachment.baseImage (e := e))
        (CylinderAttachment.collarSet f₀ f₁ sq cut)
        (CylinderAttachment.baseImage_subset_collar f₀ f₁ sq cut hpos) L :=
  relativeSubspaceInclusion_naturality l.hom _ _ _ _ _ _ _ _ L

/-- The original characteristic map of the actual two-ended attachment is a twisted
relative quasi-isomorphism, without hypotheses on the two attaching maps. -/
theorem attachmentCell_relative_quasiIso (L : System.{u, u} D) :
    QuasiIso (relativePushforwardChainMap l.hom (CylinderAttachment.sourceBoundary A)
      (CylinderAttachment.baseImage (e := e))
      (CylinderAttachment.cell_mapsTo_boundary f₀ f₁ sq) L) := by
  let cut : ℝ := 1 / 4
  have hpos : 0 < cut := by norm_num [cut]
  have hcut : cut ≤ 1 / 2 := by norm_num [cut]
  exact relativePushforwardChainMap_quasiIso_of_subspaceEnlargement l.hom
    (CylinderAttachment.sourceBoundary A) (CylinderAttachment.sourceCollar A cut)
    (CylinderAttachment.baseImage (e := e)) (CylinderAttachment.collarSet f₀ f₁ sq cut)
    (CylinderAttachment.sourceBoundary_subset_collar A cut hpos)
    (CylinderAttachment.baseImage_subset_collar f₀ f₁ sq cut hpos)
    (CylinderAttachment.cell_mapsTo_boundary f₀ f₁ sq)
    (CylinderAttachment.cell_mapsTo_collar f₀ f₁ sq cut) L
    (CylinderAttachment.sourceBoundaryCollarEquiv A cut hpos hcut)
    (CylinderAttachment.sourceBoundaryCollarEquiv_toFun A cut hpos hcut)
    (CylinderAttachment.baseImageCollarEquiv f₀ f₁ sq cut hpos hcut)
    (CylinderAttachment.baseImageCollarEquiv_toFun f₀ f₁ sq cut hpos hcut)
    (attachmentCell_collar_relative_quasiIso f₀ f₁ sq cut hpos L)

end Quillen.LocalCoefficients
