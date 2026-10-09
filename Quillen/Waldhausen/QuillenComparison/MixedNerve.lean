import Quillen.Topology.Realization.HomotopyBridge
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Topology.Homotopy.Equiv

/-! # Nerves for categories with different hom universes

The row groupoid has small isomorphism types, whereas a Q-arrow includes an
arbitrary apex object. Both nerves live in the common object universe. The
usual nerve-map and equivalence argument works unchanged without identifying
those two hom universes.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial
universe u v w

namespace Quillen.Waldhausen.QuillenComparison.MixedNerve

variable {C D : Type (max u v w)} [Category.{v} C] [Category.{w} D]

/-- Postcomposition on nerves, retaining the possibly different hom universes. -/
def map (F : C ⥤ D) : nerve C ⟶ nerve D where
  app _ := ↾fun G ↦ G ⋙ F
  naturality _ _ _ := rfl

/-- The categorical-interval cylinder has the same explicit formula in mixed universes. -/
def cylinder {F G : C ⥤ D} (α : F ⟶ G) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app _ := ↾fun z ↦ (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α)
  naturality _ _ _ := rfl

@[simp]
theorem cylinder_zero {F G : C ⥤ D} (α : F ⟶ G) : SSet.ι₀ ≫ cylinder.{u, v, w} α = map.{u, v, w} F := by
  ext n z
  change ((Functor.const (Fin (n.unop.len + 1))).obj (0 : Fin 2)).prod' z ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α) = z ⋙ F
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  simp [Functor.uncurry, ComposableArrows.mk₁, Functor.prod']

@[simp]
theorem cylinder_one {F G : C ⥤ D} (α : F ⟶ G) : SSet.ι₁ ≫ cylinder.{u, v, w} α = map.{u, v, w} G := by
  ext n z
  change ((Functor.const (Fin (n.unop.len + 1))).obj (1 : Fin 2)).prod' z ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α) = z ⋙ G
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  simp [Functor.uncurry, ComposableArrows.mk₁, Functor.prod']

/-- Natural transformations give actual simplicial homotopies. -/
def homotopy {F G : C ⥤ D} (α : F ⟶ G) : SSet.Homotopy (map.{u, v, w} F) (map.{u, v, w} G) where
  h := cylinder.{u, v, w} α
  h₀ := cylinder_zero.{u, v, w} α
  h₁ := cylinder_one.{u, v, w} α
  rel := by ext n z; exact z.1.property.elim

/-- Categorical equivalences induce realization homotopy equivalences with
the exact postcomposition nerve map, even when the hom universes differ. -/
def realizationEquivalence (e : C ≌ D) :
    ContinuousMap.HomotopyEquiv |nerve C| |nerve D| where
  toFun := (SSet.toTop.map (map.{u, v, w} e.functor)).hom
  invFun := (SSet.toTop.map (map.{u, w, v} e.inverse)).hom
  left_inv := by
    have h := realizationSimplicialHomotopy (homotopy.{max u w, v, v} e.unitIso.hom)
    have h₀ : map.{max u w, v, v} (𝟭 C) = 𝟙 (nerve C) := rfl
    have h₁ : map.{max u w, v, v} (e.functor ⋙ e.inverse) = map.{u, v, w} e.functor ≫ map.{u, w, v} e.inverse := rfl
    rw [h₀, h₁, SSet.toTop.map_id, SSet.toTop.map_comp] at h
    exact ⟨h.symm⟩
  right_inv := by
    have h := realizationSimplicialHomotopy (homotopy.{max u v, w, w} e.counitIso.hom)
    have h₀ : map.{max u v, w, w} (𝟭 D) = 𝟙 (nerve D) := rfl
    have h₁ : map.{max u v, w, w} (e.inverse ⋙ e.functor) = map.{u, w, v} e.inverse ≫ map.{u, v, w} e.functor := rfl
    rw [h₀, h₁, SSet.toTop.map_id, SSet.toTop.map_comp] at h
    exact ⟨h⟩

@[simp]
theorem realizationEquivalence_toFun (e : C ≌ D) :
    (realizationEquivalence.{u, v, w} e).toFun = (SSet.toTop.map (map.{u, v, w} e.functor)).hom := rfl

end Quillen.Waldhausen.QuillenComparison.MixedNerve
