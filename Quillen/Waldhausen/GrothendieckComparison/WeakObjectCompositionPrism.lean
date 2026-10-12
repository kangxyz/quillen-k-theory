/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Rows.NerveReindex
public import Quillen.Waldhausen.GrothendieckComparison.WeakRelations
public import Quillen.Waldhausen.SConstruction.BisimplexRealization

/-!
# The actual nerve triangle of two weak object arrows

The original two weak arrows determine their genuine weak-row nerve triangle. All three faces
retain the original component squares, including the literal composite arrow. Both simplicial
coordinates and their continuous realizations remain independent.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Convexity
open Quillen.Waldhausen.QuotientRows
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)

/-- The one-row embedding preserves the original composite as an actual weak-row arrow. -/
theorem oneWeakArrow_comp :
    W.oneWeakArrow f hf ≫ W.oneWeakArrow g hg =
      W.oneWeakArrow (f ≫ g) (W.weq.comp_mem _ _ hf hg) := by
  apply WideSubcategory.hom_ext
  exact ((oneEmbedding W).map_comp f g).symm

/-- The original weak-row chain on the genuine two-simplex. -/
def weakObjectCompositionPrism : Grid₂ ⦋1⦌ ⦋2⦌ ⥤ C :=
  weakChainToGrid W (ComposableArrows.mk₂ (W.oneWeakArrow f hf) (W.oneWeakArrow g hg))

/-- Every original quotient row and every original weak nerve arrow remains certified. -/
theorem weakObjectCompositionPrism_isSimplex₂ :
    IsSimplex₂ W.cof W.weq (W.weakObjectCompositionPrism f g hf hg) :=
  weakChainToGrid_isSimplex₂ W _

/-- The first nerve edge is the entire original first weak-arrow square. -/
theorem weakObjectCompositionPrism_first :
    gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.δ 2) ⋙ W.weakObjectCompositionPrism f g hf hg =
      (W.weakObjectSimplex f hf).val := by
  rw [weakObjectCompositionPrism, weakChainToGrid_precomp_nerve]
  change weakChainToGrid W ((nerve (WeakRows W ⦋1⦌)).δ 2
    (ComposableArrows.mk₂ (W.oneWeakArrow f hf) (W.oneWeakArrow g hg))) = _
  rw [nerve.δ₂_mk₂_eq]
  rfl

/-- The second nerve edge is the entire original second weak-arrow square. -/
theorem weakObjectCompositionPrism_second :
    gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.δ 0) ⋙ W.weakObjectCompositionPrism f g hf hg =
      (W.weakObjectSimplex g hg).val := by
  rw [weakObjectCompositionPrism, weakChainToGrid_precomp_nerve]
  change weakChainToGrid W ((nerve (WeakRows W ⦋1⦌)).δ 0
    (ComposableArrows.mk₂ (W.oneWeakArrow f hf) (W.oneWeakArrow g hg))) = _
  rw [nerve.δ₀_mk₂_eq]
  rfl

/-- The long nerve edge is the original literal composite weak-arrow square. -/
theorem weakObjectCompositionPrism_composite :
    gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.δ 1) ⋙ W.weakObjectCompositionPrism f g hf hg =
      (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).val := by
  rw [weakObjectCompositionPrism, weakChainToGrid_precomp_nerve]
  change weakChainToGrid W ((nerve (WeakRows W ⦋1⦌)).δ 1
    (ComposableArrows.mk₂ (W.oneWeakArrow f hf) (W.oneWeakArrow g hg))) = _
  rw [nerve.δ₁_mk₂_eq, oneWeakArrow_comp]
  rfl

/-- The actual independent object-edge and nerve-triangle coordinates. -/
def weakObjectCompositionRealization :
    C(StdSimplex ℝ (Fin 2) × StdSimplex ℝ (Fin 3), W.Delooping) :=
  bisimplexRealization W (W.weakObjectCompositionPrism f g hf hg)
    (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg)

/-- The whole product-simplex realization retains both original coordinates. -/
theorem weakObjectCompositionRealization_apply
    (t : StdSimplex ℝ (Fin 2)) (z : StdSimplex ℝ (Fin 3)) :
    W.weakObjectCompositionRealization f g hf hg (t, z) =
      bisimplexRealization W (W.weakObjectCompositionPrism f g hf hg)
        (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) (t, z) := rfl

/-- The first continuous face is the entire original weak-arrow square. -/
theorem weakObjectCompositionRealization_first
    (t z : StdSimplex ℝ (Fin 2)) :
    W.weakObjectCompositionRealization f g hf hg (t, z.map (SimplexCategory.δ 2)) =
      bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex f hf).property) (t, z) := by
  have h := bisimplexRealization_precomp W (W.weakObjectCompositionPrism f g hf hg)
    (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) (𝟙 ⦋1⦌) (SimplexCategory.δ 2) t z
  have he := bisimplexRealization_congr W _
    ((W.weakObjectCompositionPrism_isSimplex₂ f g hf hg).precomp W.cof W.weq
      (𝟙 ⦋1⦌) (SimplexCategory.δ 2))
    ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
      (W.weakObjectSimplex f hf).property)
    (W.weakObjectCompositionPrism_first f g hf hg)
  rw [he] at h
  rw [weakObjectCompositionRealization_apply]
  simpa using h

/-- The second continuous face is the entire original weak-arrow square. -/
theorem weakObjectCompositionRealization_second
    (t z : StdSimplex ℝ (Fin 2)) :
    W.weakObjectCompositionRealization f g hf hg (t, z.map (SimplexCategory.δ 0)) =
      bisimplexRealization W (W.weakObjectSimplex g hg).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex g hg).property) (t, z) := by
  have h := bisimplexRealization_precomp W (W.weakObjectCompositionPrism f g hf hg)
    (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) (𝟙 ⦋1⦌) (SimplexCategory.δ 0) t z
  have he := bisimplexRealization_congr W _
    ((W.weakObjectCompositionPrism_isSimplex₂ f g hf hg).precomp W.cof W.weq
      (𝟙 ⦋1⦌) (SimplexCategory.δ 0))
    ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
      (W.weakObjectSimplex g hg).property)
    (W.weakObjectCompositionPrism_second f g hf hg)
  rw [he] at h
  rw [weakObjectCompositionRealization_apply]
  simpa using h

/-- The composite continuous face is the entire original weak-arrow square. -/
theorem weakObjectCompositionRealization_composite
    (t z : StdSimplex ℝ (Fin 2)) :
    W.weakObjectCompositionRealization f g hf hg (t, z.map (SimplexCategory.δ 1)) =
      bisimplexRealization W (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).property) (t, z) := by
  have h := bisimplexRealization_precomp W (W.weakObjectCompositionPrism f g hf hg)
    (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) (𝟙 ⦋1⦌) (SimplexCategory.δ 1) t z
  have he := bisimplexRealization_congr W _
    ((W.weakObjectCompositionPrism_isSimplex₂ f g hf hg).precomp W.cof W.weq
      (𝟙 ⦋1⦌) (SimplexCategory.δ 1))
    ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
      (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).property)
    (W.weakObjectCompositionPrism_composite f g hf hg)
  rw [he] at h
  rw [weakObjectCompositionRealization_apply]
  simpa using h

end Quillen.Waldhausen.Structure
