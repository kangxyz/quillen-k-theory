import Quillen.Topology.Realization.Homotopy
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Natural transformations and the simplicial nerve cylinder

A natural transformation determines a functor `[1] × C ⥤ D`. Evaluating
this functor on a chain in `C` and a monotone map to `[1]` constructs the
simplicial cylinder map explicitly in all dimensions.
-/

noncomputable section

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

universe u v

namespace Quillen

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F G : C ⥤ D}

/-- Evaluation of a natural transformation as a functor on the categorical interval. -/
def naturalTransformationCylinderFunctor (α : F ⟶ G) : Fin 2 × C ⥤ D :=
  Functor.uncurry.obj (ComposableArrows.mk₁ α)

/-- The nerve cylinder map associated to a natural transformation. -/
def naturalTransformationNerveCylinder (α : F ⟶ G) :
    nerve C ⊗ Δ[1] ⟶ nerve D where
  app n := ↾fun z ↦
    (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
      naturalTransformationCylinderFunctor α
  naturality n m f := by
    ext z
    rfl

@[simp]
theorem naturalTransformationNerveCylinder_zero (α : F ⟶ G) :
    SSet.ι₀ ≫ naturalTransformationNerveCylinder α = nerveMap F := by
  ext n z
  change ((Functor.const (Fin (n.unop.len + 1))).obj (0 : Fin 2)).prod' z ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α) = z ⋙ F
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · rfl
  · intro i j f
    simp [Functor.uncurry, ComposableArrows.mk₁, Functor.prod']
    rfl


@[simp]
theorem naturalTransformationNerveCylinder_one (α : F ⟶ G) :
    SSet.ι₁ ≫ naturalTransformationNerveCylinder α = nerveMap G := by
  ext n z
  change ((Functor.const (Fin (n.unop.len + 1))).obj (1 : Fin 2)).prod' z ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α) = z ⋙ G
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · rfl
  · intro i j f
    simp [Functor.uncurry, ComposableArrows.mk₁, Functor.prod']
    rfl


/-- Restriction of the categorical cylinder to one object is its component arrow. -/
theorem naturalTransformationCylinderFunctor_vertex (α : F ⟶ G) (c : C) :
    (𝟭 (Fin 2)).prod' ((Functor.const (Fin 2)).obj c) ⋙
      naturalTransformationCylinderFunctor α = ComposableArrows.mk₁ (α.app c) := by
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp [naturalTransformationCylinderFunctor, Functor.uncurry, Functor.prod',
      ComposableArrows.mk₁, ComposableArrows.hom]
    change α.app c = 𝟙 _ ≫ α.app c
    simp

/-- On an object vertex, the simplicial cylinder is exactly its component edge. -/
theorem naturalTransformationNerveCylinder_vertex (α : F ⟶ G) (c : C) :
    nerveVertexMap c ▷ Δ[1] ≫ naturalTransformationNerveCylinder α =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫
        SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (α.app c)) := by
  ext n z
  change (z.2.down.toOrderHom.monotone.functor.prod'
      ((Functor.const (Fin (n.unop.len + 1))).obj c)) ⋙
      naturalTransformationCylinderFunctor α =
    z.2.down.toOrderHom.monotone.functor ⋙ ComposableArrows.mk₁ (α.app c)
  rw [← naturalTransformationCylinderFunctor_vertex α c]
  rfl

/-- If the component at the chosen object is the identity after transport,
the entire simplicial cylinder fixes that vertex. -/
theorem naturalTransformationNerveCylinder_based (α : F ⟶ G) (c : C)
    (h : F.obj c = G.obj c) (hα : α.app c = eqToHom h) :
    nerveVertexMap c ▷ Δ[1] ≫ naturalTransformationNerveCylinder α =
      CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫ nerveVertexMap (F.obj c) := by
  rw [naturalTransformationNerveCylinder_vertex]
  have hm : ComposableArrows.mk₁ (α.app c) = ComposableArrows.mk₁ (𝟙 (F.obj c)) := by
    rw [hα]
    simpa using ComposableArrows.mk₁_comp_eqToHom (𝟙 (F.obj c)) h
  erw [hm, ← CategoryTheory.nerve.σ₀_mk₀_eq,
    ← SSet.stdSimplex.σ_comp_yonedaEquiv_symm, ← Category.assoc]


/-- A natural transformation induces a genuine simplicial homotopy between nerve maps. -/
def naturalTransformationNerveHomotopy (α : F ⟶ G) :
    SSet.Homotopy (nerveMap F) (nerveMap G) where
  h := naturalTransformationNerveCylinder α
  h₀ := naturalTransformationNerveCylinder_zero α
  h₁ := naturalTransformationNerveCylinder_one α
  rel := by
    ext n z
    exact z.1.property.elim

end Quillen
