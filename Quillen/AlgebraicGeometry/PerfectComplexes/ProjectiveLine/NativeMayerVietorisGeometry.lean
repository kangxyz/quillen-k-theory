/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeInverseImageBoundary

/-! # Original native geometry of a compact two-open Mayer-Vietoris cover -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeMayerVietoris
open Quillen.Scheme Quillen.Scheme.ProjectiveLine

variable {V X : QuasiCompactSchemes.{u}} (f : V ⟶ X) [IsOpenImmersion f.hom]
  [QuasiSeparatedSpace X.obj] (T : X.obj.Opens) [CompactSpace T.toScheme]

instance overlap_compactSpace : CompactSpace (f.hom ⁻¹ᵁ T).toScheme := by
  have hT : IsCompact (T : Set X.obj) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T.toScheme))
  exact isCompact_iff_compactSpace.mp (f.hom.isCompact_preimage hT)

/-- The original base overlap, with its proved compactness. -/
abbrev overlapBase : QuasiCompactSchemes.{u} := nativeOpenBase V (f.hom ⁻¹ᵁ T)

/-- The original overlap inclusion into the second base open. -/
def overlapToV : overlapBase f T ⟶ V := nativeOpenBaseInclusion V (f.hom ⁻¹ᵁ T)

/-- The original resLE map from the overlap to the first base open. -/
def overlapToT : overlapBase f T ⟶ nativeOpenBase X T :=
  ⟨f.hom.resLE T (f.hom ⁻¹ᵁ T) le_rfl⟩

instance overlapToV_isOpenImmersion : IsOpenImmersion (overlapToV f T).hom := by
  change IsOpenImmersion (f.hom ⁻¹ᵁ T).ι
  infer_instance

instance overlapToT_isOpenImmersion : IsOpenImmersion (overlapToT f T).hom := by
  change IsOpenImmersion (f.hom.resLE T (f.hom ⁻¹ᵁ T) le_rfl)
  infer_instance

/-- The original native map of the second open. -/
abbrev lineOpen := (nativeLineFunctor.map f).hom

/-- The actual inverse image of the first base open. -/
abbrev lineT : (nativeLineFunctor.obj X).obj.Opens := (nativeProjection.app X).hom ⁻¹ᵁ T

/-- The actual overlap used by the original target Mayer-Vietoris sequence. -/
abbrev lineOverlap : (nativeLineFunctor.obj V).obj.Opens := lineOpen f ⁻¹ᵁ lineT T

/-- The canonical native overlap comparison, with the literal target intersection. -/
def overlapIso : (nativeLineFunctor.obj (overlapBase f T)).obj ≅ (lineOverlap f T).toScheme :=
  nativeProjectionOpenIso V (f.hom ⁻¹ᵁ T) ≪≫
    (nativeLineFunctor.obj V).obj.isoOfEq (nativeProjection_inverseImage_open f T).symm

omit [IsOpenImmersion f.hom] in
@[reassoc (attr := simp)] theorem overlapIso_hom_inclusion :
    (overlapIso f T).hom ≫ (lineOverlap f T).ι =
      (nativeLineFunctor.map (overlapToV f T)).hom := by
  simp only [overlapIso, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι]
  exact nativeProjectionOpenIso_hom_inclusion V (f.hom ⁻¹ᵁ T)

omit [IsOpenImmersion f.hom] in
@[reassoc (attr := simp)] theorem overlapIso_inv_inclusion :
    (overlapIso f T).inv ≫ (nativeLineFunctor.map (overlapToV f T)).hom =
      (lineOverlap f T).ι := by
  rw [← overlapIso_hom_inclusion, Iso.inv_hom_id_assoc]

instance lineOverlap_compactSpace : CompactSpace (lineOverlap f T).toScheme :=
  (AlgebraicGeometry.Scheme.homeoOfIso (overlapIso f T)).compactSpace

omit [IsOpenImmersion f.hom] in
/-- The original base overlap square, in the T-first Mayer-Vietoris order. -/
theorem overlap_base_square : overlapToV f T ≫ f =
    overlapToT f T ≫ nativeOpenBaseInclusion X T := by
  apply ObjectProperty.hom_ext
  exact (f.hom.resLE_comp_ι le_rfl).symm

omit [IsOpenImmersion f.hom] in
/-- The actual native overlap comparison retains the original restriction into the first open. -/
@[reassoc] theorem overlapIso_hom_toT :
    (overlapIso f T).hom ≫ (lineOpen f).resLE (lineT T) (lineOverlap f T) le_rfl =
      (nativeLineFunctor.map (overlapToT f T)).hom ≫ (nativeProjectionOpenIso X T).hom := by
  apply (cancel_mono (lineT T).ι).mp
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    overlapIso_hom_inclusion, Category.assoc, nativeProjectionOpenIso_hom_inclusion]
  have h := congrArg (fun g => nativeLineFunctor.map g) (overlap_base_square f T)
  simpa only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] using
    congrArg (fun g => g.hom) h

omit [IsOpenImmersion f.hom] in
/-- The inverse comparisons retain the same original overlap map. -/
@[reassoc] theorem overlap_toT_inv :
    (lineOpen f).resLE (lineT T) (lineOverlap f T) le_rfl ≫
        (nativeProjectionOpenIso X T).inv =
      (overlapIso f T).inv ≫ (nativeLineFunctor.map (overlapToT f T)).hom := by
  apply (cancel_epi (overlapIso f T).hom).mp
  rw [← Category.assoc, overlapIso_hom_toT, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

omit [QuasiSeparatedSpace X.obj] in
/-- The original native open has exactly the inverse-image range of the base open. -/
theorem lineOpen_opensRange : (lineOpen f).opensRange =
    (nativeProjection.app X).hom ⁻¹ᵁ f.hom.opensRange := by
  change ((nativeLineFunctor.map f).hom).opensRange = _
  have h : ((nativeMap_isPullback f).isoPullback.hom ≫
      pullback.fst (nativeProjection.app X).hom f.hom).opensRange =
      (nativeProjection.app X).hom ⁻¹ᵁ f.hom.opensRange := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst]
  simpa only [(nativeMap_isPullback f).isoPullback_hom_fst] using h

omit [QuasiSeparatedSpace X.obj] [CompactSpace T.toScheme] in
/-- The original two base opens induce the actual target two-open cover. -/
theorem line_cover (hc : ∀ x : X.obj, x ∈ Set.range f.hom ∨ x ∈ T) :
    ∀ y : (nativeLineFunctor.obj X).obj, y ∈ Set.range (lineOpen f) ∨ y ∈ lineT T := by
  intro y
  rcases hc ((nativeProjection.app X).hom y) with hy | hy
  · left
    change y ∈ (lineOpen f).opensRange
    rw [lineOpen_opensRange]
    exact hy
  · exact Or.inr hy

end Quillen.PerfectComplexes.ProjectiveLine.NativeMayerVietoris
