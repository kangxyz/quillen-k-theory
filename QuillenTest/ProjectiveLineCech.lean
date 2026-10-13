/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.AffineCechCover
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.CechDifference
public import Mathlib.Data.ZMod.Basic

/-! Consumers of the genuine affine chart cover and original section difference.
The overlap identification respects the actual projection. The section lifting
statement includes the nonreduced ring `ZMod 4` and the zero ring. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Scheme.PolynomialLaurent Quillen.Scheme.ProjectiveLine
universe u
namespace QuillenTest.ProjectiveLineCech

open Quillen

lemma overlap_projection (R : CommRingCat.{u}) :
    (overlapIso R).hom ≫ (chartOpen R true ⊓ chartOpen R false).ι ≫ projection R =
      laurentProjection R := by
  simp only [chartOpen_true, chartOpen_false]
  rw [← Category.assoc, overlapIso_hom_ι, Category.assoc, plusChart_projection,
    laurentPlus_projection]

lemma mixed_intersection_is_original_overlap (R : CommRingCat.{u}) :
    (⨅ i : Bool, chartOpen R i) = (laurentPlus R ≫ plusChart R).opensRange := by
  exact (iInf_chartOpen_of_mixed R (fun b => b) ⟨true, rfl⟩ ⟨false, rfl⟩).trans
    (chart_ranges_inter R)

lemma lift_overlap_section (R : CommRingCat.{u})
    (z : Γ(Spec (.of (LaurentPolynomial R)), ⊤)) :
    ∃ a b : Γ(Spec (.of (Polynomial R)), ⊤),
      (laurentPlus R).appTop.hom a = z + (laurentMinus R).appTop.hom b := by
  obtain ⟨⟨a, b⟩, h⟩ := chartSectionsDifference_surjective R z
  exact ⟨a, b, sub_eq_iff_eq_add.mp h⟩

example (z : Γ(Spec (.of (LaurentPolynomial (ZMod 4))), ⊤)) :
    ∃ a b : Γ(Spec (.of (Polynomial (ZMod 4))), ⊤),
      (laurentPlus (.of (ZMod 4))).appTop.hom a =
        z + (laurentMinus (.of (ZMod 4))).appTop.hom b :=
  lift_overlap_section (.of (ZMod 4)) z

example : Function.Surjective (chartSectionsDifference (.of (ZMod 1))) :=
  chartSectionsDifference_surjective _

end QuillenTest.ProjectiveLineCech
