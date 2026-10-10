/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.SupportedDenominatorComposition
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.OneChartRoofs

/-! # Genuine global qcqs supported denominators and original perfect roofs -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] Affine.standardDerivedSheaves

lemma hasSupportedQCDenominators_of_isIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsIso j] : HasSupportedQCDenominators j := by
  intro A B hA b hb hB hz α
  have hzB := (isZero_toDerived_restrict_iff_of_isIso j B).mp hz
  refine ⟨A, 𝟙 A, hA, ?_, ?_⟩
  · rw [(restrict j).map_id]
    infer_instance
  · rw [(toDerived X).map_id, Category.id_comp]
    exact hzB.eq_of_tgt _ _

lemma hasSupportedQCDenominators_finite_affine_union {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X))
    (s : Finset X.affineOpens) :
    ∃ h : U ≤ U ⊔ s.sup (fun V => V.val), HasSupportedQCDenominators (X.homOfLE h) := by
  classical
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, sup_bot_eq]
    have : IsIso (X.homOfLE (le_refl U)) := by rw [X.homOfLE_rfl]; infer_instance
    exact ⟨le_rfl, hasSupportedQCDenominators_of_isIso _⟩
  | @insert V s hV ih =>
    rw [Finset.sup_insert, show U ⊔ (V.val ⊔ s.sup (fun V => V.val)) =
      (U ⊔ s.sup (fun V => V.val)) ⊔ V.val by ac_rfl]
    let S := U ⊔ s.sup (fun V => V.val)
    let T := S ⊔ V.val
    have hS : IsCompact (S : Set X) := hU.union (isCompact_finite_affine_sup s)
    let : CompactSpace S.toScheme := isCompact_iff_compactSpace.mp hS
    let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp (hS.union V.property.isCompact)
    let : QuasiSeparatedSpace T.toScheme := QuasiSeparatedSpace.of_isOpenEmbedding
      T.ι.isOpenEmbedding
    let : IsAffine V.val.toScheme := V.property
    obtain ⟨hUS, ih⟩ := ih
    let i := X.homOfLE hUS
    let j := X.homOfLE (le_sup_left : S ≤ T)
    let k := X.homOfLE (le_sup_right : V.val ≤ T)
    have hcover (x : T.toScheme) : x ∈ Set.range j ∨ x ∈ Set.range k := by
      rcases x.property with hx | hx
      · exact Or.inl ⟨⟨x.val, hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩
      · exact Or.inr ⟨⟨x.val, hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩
    have h₂ := affineChart_hasSupportedQCDenominators j k hcover
    have h := hasSupportedQCDenominators_comp i j ih h₂
    refine ⟨hUS.trans le_sup_left, ?_⟩
    simpa only [i, j, Scheme.homOfLE_homOfLE] using h

/-- Every original compact open of a qcqs scheme has genuine supported QC
source denominators, obtained by finite affine induction. -/
lemma qcqs_hasSupportedQCDenominators {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) : HasSupportedQCDenominators U.ι := by
  classical
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  obtain ⟨s, hs, hcover⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (X := X) (U := ⊤)).mp (by simpa using (CompactSpace.isCompact_univ : IsCompact (Set.univ : Set
      X)))
  have ht : hs.toFinset.sup (fun V => V.val) = (⊤ : X.Opens) := by
    simpa only [Finset.sup_eq_iSup, Set.Finite.mem_toFinset] using hcover.symm
  have h := hasSupportedQCDenominators_finite_affine_union U hU hs.toFinset
  rw [ht, sup_top_eq] at h
  obtain ⟨hUTop, h⟩ := h
  let : CompactSpace (⊤ : X.Opens).toScheme := isCompact_iff_compactSpace.mp (by simpa using
    (CompactSpace.isCompact_univ : IsCompact (Set.univ : Set X)))
  have h' := hasSupportedQCDenominators_comp (X.homOfLE (le_top : U ≤ ⊤)) X.topIso.hom h
    (hasSupportedQCDenominators_of_isIso X.topIso.hom)
  have he : X.homOfLE (le_top : U ≤ ⊤) ≫ X.topIso.hom = U.ι :=
    Scheme.homOfLE_ι X (le_top : U ≤ ⊤)
  simpa only [he] using h'

/-- The same theorem for the original compact open immersion, retaining its
actual source and restriction functor. -/
lemma qcqs_hasSupportedQCDenominators_of_openImmersion {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] : HasSupportedQCDenominators j := by
  let W := j.opensRange
  have hW : IsCompact (W : Set X) := isCompact_range j.continuous
  let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  have h := hasSupportedQCDenominators_comp j.isoOpensRange.hom W.ι
    (hasSupportedQCDenominators_of_isIso _) (qcqs_hasSupportedQCDenominators W hW)
  change HasSupportedQCDenominators (j.isoOpensRange.hom ≫ j.opensRange.ι) at h
  simpa only [j.isoOpensRange_hom_ι] using h

/-- Genuine global perfect morphism roofs on every compact open immersion
into a qcqs scheme. No geometric replacement or roof property is supplied. -/
lemma qcqs_hasDerivedRoofs {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] : HasDerivedRoofs j :=
  hasDerivedRoofs_of_supportedQCDenominators j
    (qcqs_hasSupportedQCDenominators_of_openImmersion j)

end Quillen.PerfectComplexes.OpenDerivedImage
