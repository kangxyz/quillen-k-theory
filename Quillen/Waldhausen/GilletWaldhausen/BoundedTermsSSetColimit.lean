/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Waldhausen.GilletWaldhausen.BoundedTermsSSet
public import Quillen.Waldhausen.GilletWaldhausen.BoundedSSetColimit

/-! # The actual filtered simplicial union of bounded termwise strata

Finite-grid coverage and injectivity prove the actual simplicial colimit.
Only after that proof is the accepted filtered-realization API applied to
compact maps and relative homotopies. No global term bound or stagewise
K-equivalence is assumed.
-/
@[expose] public section

open Topology

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u w
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
variable (w : MorphismProperty (boundedTerms P).FullSubcategory)

/-- The strict increasing diagram of actual bounded S-sets. -/
@[implicit_reducible]
def boundedTermsSSetDiagram : BoundedStageIndex.{max u v} ⥤ SSet.{max u v} where
  obj j := boundedTermsStratumSSet P w (boundedStageRank j)
  map f := boundedTermsStratumSSetTransition P w (leOfHom (AsSmall.down.map f))
  map_id _ := boundedTermsStratumSSetTransition_id P w _
  map_comp _ _ := (boundedTermsStratumSSetTransition_comp P w _ _).symm

/-- Its actual canonical cocone into the original bounded-term S-set. -/
@[implicit_reducible]
def boundedTermsSSetCocone : Cocone (boundedTermsSSetDiagram P w) where
  pt := boundedTermsSSet P w
  ι :=
    { app j := boundedTermsStratumSSetInclusion P w (boundedStageRank j)
      naturality {j k} f := by
        change boundedTermsStratumSSetTransition P w (leOfHom (AsSmall.down.map f)) ≫
          boundedTermsStratumSSetInclusion P w (boundedStageRank k) =
            boundedTermsStratumSSetInclusion P w (boundedStageRank j) ≫ 𝟙 _
        rw [Category.comp_id]
        exact boundedTermsStratumSSetTransition_inclusion P w (leOfHom (AsSmall.down.map f)) }

/-- The original S-set is genuinely the filtered colimit of its actual
bounded strata, proved degreewise from finite-grid coverage and injectivity. -/
def boundedTermsSSetCoconeIsColimit : IsColimit (boundedTermsSSetCocone P w) := by
  apply evaluationJointlyReflectsColimits
  intro n
  apply Types.FilteredColimit.isColimitOf'
  · intro F
    obtain ⟨N, G, hG⟩ := boundedTermsStratumSSetInclusion_surjective P w n F
    exact ⟨boundedStageIndex N, G, hG.symm⟩
  · intro j F G h
    have hFG := boundedTermsStratumSSetInclusion_injective P w (boundedStageRank j) n h
    exact ⟨j, 𝟙 j, congrArg (((boundedTermsSSetDiagram P w).map (𝟙 j)).app n) hFG⟩

/-- Every compact-source continuous map into the actual S-realization has
an exact continuous factorization through one genuine bounded stage. -/
theorem boundedTermsSSet_compact_factors {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, |boundedTermsSSet P w|)) :
    ∃ N : ℕ, ∃ g : C(T, |boundedTermsStratumSSet P w N|),
      (SSet.toTop.map (boundedTermsStratumSSetInclusion P w N)).hom.comp g = f := by
  obtain ⟨j, g, hg⟩ := FilteredRealization.compact_factors
    (boundedTermsSSetDiagram P w) (boundedTermsSSetCocone P w) (boundedTermsSSetCoconeIsColimit
      P w) f
  exact ⟨boundedStageRank j, g, hg⟩

/-- Equal compact-source maps from one bounded stage become literally equal
in an actual larger bounded stage. -/
theorem boundedTermsSSet_compact_eq_eventually {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (N : ℕ) (f g : C(T, |boundedTermsStratumSSet P w N|))
    (he : (SSet.toTop.map (boundedTermsStratumSSetInclusion P w N)).hom.comp f =
      (SSet.toTop.map (boundedTermsStratumSSetInclusion P w N)).hom.comp g) :
    ∃ M : ℕ, ∃ h : N ≤ M,
      (SSet.toTop.map (boundedTermsStratumSSetTransition P w h)).hom.comp f =
        (SSet.toTop.map (boundedTermsStratumSSetTransition P w h)).hom.comp g := by
  obtain ⟨j, h, hh⟩ := FilteredRealization.compact_eq_eventually
    (boundedTermsSSetDiagram P w) (boundedTermsSSetCocone P w) (boundedTermsSSetCoconeIsColimit
      P w)
    (boundedStageIndex N) f g he
  exact ⟨boundedStageRank j, leOfHom (AsSmall.down.map h), hh⟩

/-- Compact factorization can retain any prescribed initial bound. -/
theorem boundedTermsSSet_compact_factors_above {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (N : ℕ) (f : C(T, |boundedTermsSSet P w|)) :
    ∃ M : ℕ, N ≤ M ∧ ∃ g : C(T, |boundedTermsStratumSSet P w M|),
      (SSet.toTop.map (boundedTermsStratumSSetInclusion P w M)).hom.comp g = f := by
  obtain ⟨j, h, g, hg⟩ := FilteredRealization.compact_factors_above
    (boundedTermsSSetDiagram P w) (boundedTermsSSetCocone P w) (boundedTermsSSetCoconeIsColimit
      P w)
    (boundedStageIndex N) f
  exact ⟨boundedStageRank j, leOfHom (AsSmall.down.map h), g, hg⟩

/-- An actual ambient homotopy relative to a compact subset is represented
in a larger genuine bounded stage, with both original endpoints retained. -/
theorem boundedTermsSSet_homotopyRel_factors {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (N : ℕ) {a b : C(T, |boundedTermsStratumSSet P w N|)} (S : Set T) (hS : IsCompact S)
    (H : ((SSet.toTop.map (boundedTermsStratumSSetInclusion P w N)).hom.comp a).HomotopyRel
      ((SSet.toTop.map (boundedTermsStratumSSetInclusion P w N)).hom.comp b) S) :
    ∃ M : ℕ, ∃ h : N ≤ M,
      Nonempty (((SSet.toTop.map (boundedTermsStratumSSetTransition P w h)).hom.comp a).HomotopyRel
        ((SSet.toTop.map (boundedTermsStratumSSetTransition P w h)).hom.comp b) S) := by
  obtain ⟨j, h, hH⟩ := FilteredRealization.homotopyRel_factors
    (boundedTermsSSetDiagram P w) (boundedTermsSSetCocone P w) (boundedTermsSSetCoconeIsColimit
      P w)
    (boundedStageIndex N) S hS H
  exact ⟨boundedStageRank j, leOfHom (AsSmall.down.map h), hH⟩

end Quillen.Waldhausen.GilletWaldhausen
