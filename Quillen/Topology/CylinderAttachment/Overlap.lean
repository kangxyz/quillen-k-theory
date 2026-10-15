/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.CylinderAttachment.Collars

/-!
# The overlap of the base collar and the open cylinder

The overlap has its actual product topology, with the interval coordinate in
two short open end bands. These bands are disjoint for cutoffs at most one
half. On the two bands the collar projection is precisely the respective
attaching map, even when their images in the base meet.
-/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.CylinderAttachment

/-- The interval coordinates simultaneously in the collar and the open interior. -/
abbrev OverlapInterval (cut : ℝ) :=
  {t : DoubleCylinder.OpenInterval // endpointDistance t.1 < cut}

/-- The two open bands of a short overlap do not meet. -/
theorem overlap_bands_disjoint (cut : ℝ) (hcut : cut ≤ 1 / 2) :
    Disjoint {t : OverlapInterval cut | (t.1.1 : ℝ) < cut}
      {t : OverlapInterval cut | 1 - (t.1.1 : ℝ) < cut} := by
  apply Set.disjoint_left.mpr
  intro t hl hr
  change (t.1.1 : ℝ) < cut at hl
  change 1 - (t.1.1 : ℝ) < cut at hr
  linarith

/-- Every overlap coordinate lies in one of its two open bands. -/
theorem overlap_bands_cover (cut : ℝ) :
    {t : OverlapInterval cut | (t.1.1 : ℝ) < cut} ∪
      {t : OverlapInterval cut | 1 - (t.1.1 : ℝ) < cut} = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro t
  exact min_lt_iff.mp t.2

variable {A B D : TopCat.{u}} (f₀ f₁ : A ⟶ B)
  {l : A ⊗ TopCat.I ⟶ D} {e : B ⟶ D}
  (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f₀ f₁) l e) (cut : ℝ)

/-- The actual intersection of the two open charts. -/
abbrev Overlap : TopCat.{u} :=
  TopCat.of ↥(collarSet f₀ f₁ sq cut ∩ interiorSet f₀ f₁ sq)

/-- The product coordinates mapped to the actual open overlap. -/
def overlapMap : C(A × OverlapInterval cut, Overlap f₀ f₁ sq cut) where
  toFun z := ⟨l (z.1, ULift.up z.2.1.1), by
    constructor
    · change height f₀ f₁ sq (l (z.1, ULift.up z.2.1.1)) < cut
      rw [height_cylinder]
      exact z.2.2
    · change 0 < height f₀ f₁ sq (l (z.1, ULift.up z.2.1.1))
      rw [height_cylinder]
      exact (endpointDistance_pos_iff _).mpr z.2.1.2⟩
  continuous_toFun := by fun_prop

/-- The overlap is exactly a product with the two open interval end bands. -/
def overlapHomeomorph : A × OverlapInterval cut ≃ₜ Overlap f₀ f₁ sq cut := by
  have hcoord : IsEmbedding (fun z : A × OverlapInterval cut ↦ (z.1, z.2.1)) :=
    IsEmbedding.id.prodMap IsEmbedding.subtypeVal
  have h : IsEmbedding (overlapMap f₀ f₁ sq cut) :=
    IsEmbedding.subtypeVal.of_comp_iff.mp
      ((interior_isOpenEmbedding f₀ f₁ sq).isEmbedding.comp hcoord)
  apply h.toHomeomorphOfSurjective
  intro d
  obtain ⟨z, hz⟩ := interior_surjective f₀ f₁ sq d.1 d.2.2
  have hc : endpointDistance z.2.1 < cut := by
    have hd := d.2.1
    change height f₀ f₁ sq d.1 < cut at hd
    rwa [← hz, height_cylinder] at hd
  exact ⟨(z.1, ⟨z.2, hc⟩), Subtype.ext hz⟩

@[simp] theorem overlapHomeomorph_apply (z : A × OverlapInterval cut) :
    (overlapHomeomorph f₀ f₁ sq cut z).1 = l (z.1, ULift.up z.2.1.1) := rfl

/-- The overlap as a subspace of the base collar. -/
def overlapToCollar : Overlap f₀ f₁ sq cut ⟶ Collar cut f₀ f₁ sq :=
  TopCat.ofHom ⟨fun d ↦ ⟨d.1, d.2.1⟩, by fun_prop⟩

/-- In overlap product coordinates the collar projection is the endpoint map. -/
theorem collarProjection_overlap (hpos : 0 < cut) (hcut : cut ≤ 1 / 2)
    (z : A × OverlapInterval cut) :
    collarProjection cut f₀ f₁ sq hpos hcut
      (overlapToCollar f₀ f₁ sq cut (overlapHomeomorph f₀ f₁ sq cut z)) =
      if (z.2.1.1 : ℝ) < cut then f₀ z.1 else f₁ z.1 :=
  collarProjection_cylinder cut f₀ f₁ sq hpos hcut
    ⟨(z.1, ULift.up z.2.1.1), z.2.2⟩

/-- On the left overlap band the collar projection is the first attaching map. -/
theorem collarProjection_overlap_left (hpos : 0 < cut) (hcut : cut ≤ 1 / 2)
    (z : A × OverlapInterval cut) (hz : (z.2.1.1 : ℝ) < cut) :
    collarProjection cut f₀ f₁ sq hpos hcut
      (overlapToCollar f₀ f₁ sq cut (overlapHomeomorph f₀ f₁ sq cut z)) = f₀ z.1 := by
  rw [collarProjection_overlap]
  exact ite_eq_left hz

/-- On the right overlap band the collar projection is the second attaching map. -/
theorem collarProjection_overlap_right (hpos : 0 < cut) (hcut : cut ≤ 1 / 2)
    (z : A × OverlapInterval cut) (hz : 1 - (z.2.1.1 : ℝ) < cut) :
    collarProjection cut f₀ f₁ sq hpos hcut
      (overlapToCollar f₀ f₁ sq cut (overlapHomeomorph f₀ f₁ sq cut z)) = f₁ z.1 := by
  rw [collarProjection_overlap]
  exact ite_eq_right (by linarith)

end Quillen.CylinderAttachment
