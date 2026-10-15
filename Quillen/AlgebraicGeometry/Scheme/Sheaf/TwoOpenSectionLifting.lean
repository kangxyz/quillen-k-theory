/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.SectionsHomologyZero
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Original section lifting on a two-open cover

For a short exact sequence of module sheaves, local quotient lifts glue whenever the signed
restriction difference for the kernel is surjective. The construction corrects the actual lifts
by actual kernel sections. Further lemmas preserve signed-difference surjectivity under products
and surjective overlap maps, and obtain local lifts from genuine restricted splittings.
-/
@[expose] public section
open Quillen
open Quillen.SchemeSheaf


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules.TwoOpen
variable {X : Scheme.{u}}

private lemma app_comp_apply {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C)
    (W : X.Opens) (a : Γ(A, W)) :
    ((f ≫ g).app W).hom a = (g.app W).hom ((f.app W).hom a) := rfl

/-- Original additive sections preserve exactness at the middle of a short exact sequence. -/
lemma sections_exact {S : ShortComplex X.Modules} (hS : S.ShortExact) (W : X.Opens) :
    (S.map (sectionsFunctor X W)).Exact :=
  ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (sectionsFunctor X W)).mp inferInstance S hS).1

/-- Local quotient lifts glue after correcting their difference by original kernel sections. -/
lemma globalSections_surjective_of_difference_surjective
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (hU : Function.Surjective (S.g.app U).hom)
    (hV : Function.Surjective (S.g.app V).hom)
    (hD : Function.Surjective (difference S.X₁ U V)) :
    Function.Surjective (S.g.app ⊤).hom := by
  intro z
  obtain ⟨a, ha⟩ := hU (res S.X₃ le_top z)
  obtain ⟨b, hb⟩ := hV (res S.X₃ le_top z)
  have hz : (S.g.app (U ⊓ V)).hom (difference S.X₂ U V (a, b)) = 0 := by
    simp only [difference_apply, map_sub, app_res, ha, hb, res_res, sub_self]
  obtain ⟨c, hc⟩ := ((ShortComplex.ab_exact_iff _).mp (sections_exact hS (U ⊓ V))) _ hz
  obtain ⟨⟨d, e⟩, hde⟩ := hD c
  have hzero : difference S.X₂ U V
      (a - (S.f.app U).hom d, b - (S.f.app V).hom e) = 0 := by
    have hh := congrArg (S.f.app (U ⊓ V)).hom hde
    simp only [difference_apply, map_sub, app_res] at hh
    change res S.X₂ inf_le_left (a - (S.f.app U).hom d) -
      res S.X₂ inf_le_right (b - (S.f.app V).hom e) = 0
    rw [map_sub, map_sub]
    have hhc : res S.X₂ inf_le_left ((S.f.app U).hom d) -
        res S.X₂ inf_le_right ((S.f.app V).hom e) =
        res S.X₂ inf_le_left a - res S.X₂ inf_le_right b := hh.trans hc
    exact sub_eq_zero.mpr (sub_eq_sub_iff_add_eq_add.mpr
      (by simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp hhc).symm))
  obtain ⟨w, hw⟩ := ((ShortComplex.ab_exact_iff _).mp (sectionSequence_exact S.X₂ U V hUV)) _ hzero
  refine ⟨w, ?_⟩
  apply augmentation_injective S.X₃ U V hUV
  apply Prod.ext
  · change res S.X₃ le_top ((S.g.app ⊤).hom w) = res S.X₃ le_top z
    rw [← app_res]
    have hwU := congrArg Prod.fst hw
    change res S.X₂ le_top w = a - (S.f.app U).hom d at hwU
    rw [hwU, map_sub, ← app_comp_apply, S.zero]
    simpa using ha
  · change res S.X₃ le_top ((S.g.app ⊤).hom w) = res S.X₃ le_top z
    rw [← app_res]
    have hwV := congrArg Prod.snd hw
    change res S.X₂ le_top w = b - (S.f.app V).hom e at hwV
    rw [hwV, map_sub, ← app_comp_apply, S.zero]
    simpa using hb

/-- Original signed difference surjectivity descends along a surjective overlap section map. -/
lemma difference_surjective_of_section_surjective {M N : X.Modules} (f : M ⟶ N)
    (U V : X.Opens) (hf : Function.Surjective (f.app (U ⊓ V)).hom)
    (hD : Function.Surjective (difference M U V)) :
    Function.Surjective (difference N U V) := by
  intro z
  obtain ⟨w, hw⟩ := hf z
  obtain ⟨⟨a, b⟩, hab⟩ := hD w
  refine ⟨((f.app U).hom a, (f.app V).hom b), ?_⟩
  rw [← hw, ← hab]
  simp only [difference_apply, map_sub, app_res]

/-- Surjective original signed differences remain surjective for the actual sheaf product. -/
lemma difference_surjective_prod (M N : X.Modules) (U V : X.Opens)
    (hM : Function.Surjective (difference M U V))
    (hN : Function.Surjective (difference N U V)) :
    Function.Surjective (difference (M ⨯ N) U V) := by
  intro z
  let i : M ⟶ M ⨯ N := prod.lift (𝟙 M) 0
  let j : N ⟶ M ⨯ N := prod.lift 0 (𝟙 N)
  obtain ⟨⟨a, b⟩, hab⟩ := hM ((Scheme.Modules.Hom.app prod.fst (U ⊓ V)).hom z)
  obtain ⟨⟨c, d⟩, hcd⟩ := hN ((Scheme.Modules.Hom.app prod.snd (U ⊓ V)).hom z)
  refine ⟨((i.app U).hom a + (j.app U).hom c,
    (i.app V).hom b + (j.app V).hom d), ?_⟩
  have he : difference (M ⨯ N) U V
      ((i.app U).hom a + (j.app U).hom c, (i.app V).hom b + (j.app V).hom d) =
      (i.app (U ⊓ V)).hom (difference M U V (a, b)) +
        (j.app (U ⊓ V)).hom (difference N U V (c, d)) := by
    simp only [difference_apply, map_add, map_sub, app_res]
    abel
  rw [he, hab, hcd]
  have hid : (prod.fst : M ⨯ N ⟶ M) ≫ i + prod.snd ≫ j = 𝟙 (M ⨯ N) := by
    apply prod.hom_ext <;> simp [i, j, Preadditive.add_comp]
  have hh := congrArg (fun f : M ⨯ N ⟶ M ⨯ N => (f.app (U ⊓ V)).hom z) hid
  exact hh

end AlgebraicGeometry.Scheme.Modules.TwoOpen

namespace AlgebraicGeometry.Scheme.Modules
open TwoOpen
/-- A splitting of the actual restricted sheaf morphism gives surjectivity on original image
sections. -/
lemma section_surjective_of_restriction_split {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {M N : X.Modules} (f : M ⟶ N)
    [IsSplitEpi ((Scheme.Modules.restrictFunctor j).map f)] (W : U.Opens) :
    Function.Surjective (f.app (j ''ᵁ W)).hom := by
  apply (AddCommGrpCat.epi_iff_surjective _).mp
  change Epi ((sectionsFunctor U W).map ((Scheme.Modules.restrictFunctor j).map f))
  infer_instance
end AlgebraicGeometry.Scheme.Modules
