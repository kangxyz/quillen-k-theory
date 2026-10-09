import Quillen.Waldhausen.GilletWaldhausen.BoundedSSet
import Quillen.Topology.FilteredRealization.Homotopy
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # The genuine filtered simplicial union of bounded acyclic strata

The actual S-construction is the filtered colimit of its symmetric term-bound
strata. Every compact-source map into its realization factors continuously and
exactly through one actual bounded stage. Neither a global bound nor any
stage equivalence is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial
universe v u w
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
variable (w : MorphismProperty (boundedAcyclic P).FullSubcategory)

/-- A universe-compatible copy of the natural-number indexing category. -/
abbrev BoundedStageIndex := AsSmall.{u} ℕ

/-- The actual symmetric term bound at this stage. -/
abbrev boundedStageRank (j : BoundedStageIndex.{u}) : ℕ := AsSmall.down.obj j

/-- A concrete natural-number bound as a stage index. -/
abbrev boundedStageIndex (N : ℕ) : BoundedStageIndex.{u} := AsSmall.up.obj N

/-- The strict increasing diagram of actual bounded S-sets. -/
@[implicit_reducible]
def boundedSSetDiagram : BoundedStageIndex.{max u v} ⥤ SSet.{max u v} where
  obj j := boundedStratumSSet P w (boundedStageRank j)
  map f := boundedStratumSSetTransition P w (leOfHom (AsSmall.down.map f))
  map_id _ := boundedStratumSSetTransition_id P w _
  map_comp _ _ := (boundedStratumSSetTransition_comp P w _ _).symm

/-- Its actual canonical cocone into the original bounded-acyclic S-set. -/
@[implicit_reducible]
def boundedSSetCocone : Cocone (boundedSSetDiagram P w) where
  pt := boundedAcyclicSSet P w
  ι :=
    { app j := boundedStratumSSetInclusion P w (boundedStageRank j)
      naturality {j k} f := by
        change boundedStratumSSetTransition P w (leOfHom (AsSmall.down.map f)) ≫
          boundedStratumSSetInclusion P w (boundedStageRank k) =
            boundedStratumSSetInclusion P w (boundedStageRank j) ≫ 𝟙 _
        rw [Category.comp_id]
        exact boundedStratumSSetTransition_inclusion P w (leOfHom (AsSmall.down.map f)) }

/-- The original S-set is genuinely the filtered colimit of its actual
bounded strata, proved degreewise from finite-grid coverage and injectivity. -/
def boundedSSetCocone_isColimit : IsColimit (boundedSSetCocone P w) := by
  apply evaluationJointlyReflectsColimits
  intro n
  apply Types.FilteredColimit.isColimitOf'
  · intro F
    obtain ⟨N, G, hG⟩ := boundedStratumSSetInclusion_surjective P w n F
    exact ⟨boundedStageIndex N, G, hG.symm⟩
  · intro j F G h
    have hFG := boundedStratumSSetInclusion_injective P w (boundedStageRank j) n h
    exact ⟨j, 𝟙 j, congrArg (((boundedSSetDiagram P w).map (𝟙 j)).app n) hFG⟩

/-- Every compact-source continuous map into the actual S-realization has
an exact continuous factorization through one genuine bounded stage. -/
theorem boundedSSet_compact_factors {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, |boundedAcyclicSSet P w|)) :
    ∃ N : ℕ, ∃ g : C(T, |boundedStratumSSet P w N|),
      (SSet.toTop.map (boundedStratumSSetInclusion P w N)).hom.comp g = f := by
  obtain ⟨j, g, hg⟩ := FilteredRealization.compact_factors
    (boundedSSetDiagram P w) (boundedSSetCocone P w) (boundedSSetCocone_isColimit P w) f
  exact ⟨boundedStageRank j, g, hg⟩

/-- Equal compact-source maps from one bounded stage become literally equal
in an actual larger bounded stage. -/
theorem boundedSSet_compact_eq_eventually {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (N : ℕ) (f g : C(T, |boundedStratumSSet P w N|))
    (he : (SSet.toTop.map (boundedStratumSSetInclusion P w N)).hom.comp f =
      (SSet.toTop.map (boundedStratumSSetInclusion P w N)).hom.comp g) :
    ∃ M : ℕ, ∃ h : N ≤ M,
      (SSet.toTop.map (boundedStratumSSetTransition P w h)).hom.comp f =
        (SSet.toTop.map (boundedStratumSSetTransition P w h)).hom.comp g := by
  obtain ⟨j, h, hh⟩ := FilteredRealization.compact_eq_eventually
    (boundedSSetDiagram P w) (boundedSSetCocone P w) (boundedSSetCocone_isColimit P w)
    (boundedStageIndex N) f g he
  exact ⟨boundedStageRank j, leOfHom (AsSmall.down.map h), hh⟩

/-- Compact factorization can retain any prescribed initial bound. -/
theorem boundedSSet_compact_factors_above {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (N : ℕ) (f : C(T, |boundedAcyclicSSet P w|)) :
    ∃ M : ℕ, N ≤ M ∧ ∃ g : C(T, |boundedStratumSSet P w M|),
      (SSet.toTop.map (boundedStratumSSetInclusion P w M)).hom.comp g = f := by
  obtain ⟨j, h, g, hg⟩ := FilteredRealization.compact_factors_above
    (boundedSSetDiagram P w) (boundedSSetCocone P w) (boundedSSetCocone_isColimit P w)
    (boundedStageIndex N) f
  exact ⟨boundedStageRank j, leOfHom (AsSmall.down.map h), g, hg⟩

/-- An actual ambient homotopy relative to a compact subset is represented
in a larger genuine bounded stage, with both original endpoints retained. -/
theorem boundedSSet_homotopyRel_factors {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (N : ℕ) {a b : C(T, |boundedStratumSSet P w N|)} (S : Set T) (hS : IsCompact S)
    (H : ((SSet.toTop.map (boundedStratumSSetInclusion P w N)).hom.comp a).HomotopyRel
      ((SSet.toTop.map (boundedStratumSSetInclusion P w N)).hom.comp b) S) :
    ∃ M : ℕ, ∃ h : N ≤ M,
      Nonempty (((SSet.toTop.map (boundedStratumSSetTransition P w h)).hom.comp a).HomotopyRel
        ((SSet.toTop.map (boundedStratumSSetTransition P w h)).hom.comp b) S) := by
  obtain ⟨j, h, hH⟩ := FilteredRealization.homotopyRel_factors
    (boundedSSetDiagram P w) (boundedSSetCocone P w) (boundedSSetCocone_isColimit P w)
    (boundedStageIndex N) S hS H
  exact ⟨boundedStageRank j, leOfHom (AsSmall.down.map h), hH⟩

end Quillen.Waldhausen.GilletWaldhausen
