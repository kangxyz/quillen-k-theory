/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexFaces
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationPasting

/-!
# Simplex Isomorphism

A concrete common simplex for original exact functors with actual comparison isomorphisms.
Old triangles are identified from their two ORIGINAL component equations, not from endpoints.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.ModelSimplex
variable {V W : Model.{u}}

/-- A common original comparison functor gives an actual chain of all selected exact functors. -/
def ofIsos {k : ℕ} (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (F i).functor) : ModelSimplex V W k where
  diagram := {
    obj i := (F i).functor
    map {i j} _ := (ρ i).inv ≫ (ρ j).hom
    map_id _ := by simp
    map_comp _ _ := by simp [Category.assoc] }
  exact i := (F i).exact
  zero i := (F i).zero
  weak _i _j _f _X := W.waldhausen.weq_iso _ inferInstance

/-- Two original transformation equations identify an entire triangle face of the common simplex. -/
theorem ofIsos_face_triangle {k : ℕ} (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (F i).functor) (α : ⦋2⦌ ⟶ ⦋k⦌)
    (η : (F (α.toOrderHom 0)).functor ⟶ (F (α.toOrderHom 1)).functor)
    (θ : (F (α.toOrderHom 1)).functor ⟶ (F (α.toOrderHom 2)).functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))
    (eη : (ρ (α.toOrderHom 0)).hom ≫ η = (ρ (α.toOrderHom 1)).hom)
    (eθ : (ρ (α.toOrderHom 1)).hom ≫ θ = (ρ (α.toOrderHom 2)).hom) :
    (ofIsos F₀ F ρ).face α = triangle η θ hη hθ := by
  apply ext_diagram
  refine ComposableArrows.ext₂
    (f := ((ofIsos F₀ F ρ).face α).diagram) (g := (triangle η θ hη hθ).diagram)
    rfl rfl rfl ?_ ?_
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (ρ (α.toOrderHom 0)).inv ≫ (ρ (α.toOrderHom 1)).hom = η
    rw [← eη]
    simp
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (ρ (α.toOrderHom 1)).inv ≫ (ρ (α.toOrderHom 2)).hom = θ
    rw [← eθ]
    simp

/-- The original realized triangle is exactly the selected face of one common realized family. -/
theorem ofIsos_realized_triangle {k : ℕ} (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (F i).functor) (α : ⦋2⦌ ⟶ ⦋k⦌)
    (η : (F (α.toOrderHom 0)).functor ⟶ (F (α.toOrderHom 1)).functor)
    (θ : (F (α.toOrderHom 1)).functor ⟶ (F (α.toOrderHom 2)).functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))
    (eη : (ρ (α.toOrderHom 0)).hom ≫ η = (ρ (α.toOrderHom 1)).hom)
    (eθ : (ρ (α.toOrderHom 1)).hom ≫ θ = (ρ (α.toOrderHom 2)).hom)
    (r : ℕ) (x : stageSpace r V) (z : |(Δ[2] : SSet.{u})|) :
    stageSimplexRealization r (ofIsos F₀ F ρ)
      (x, SSet.toTop.map (SSet.stdSimplex.map α) z) =
      stageTriangleRealization η θ hη hθ r (x, z) := by
  rw [stageSimplexRealization_face, ofIsos_face_triangle F₀ F ρ α η θ hη hθ eη eθ,
    stageSimplexRealization_triangle]

/-- Four actual functors and an original commuting diamond define a whole common tetrahedron. -/
def diamond {F₀ F₁ F₂ F₃ : V ⟶ W}
    (η : F₀.functor ≅ F₁.functor) (θ : F₁.functor ≅ F₃.functor)
    (η' : F₀.functor ≅ F₂.functor) : ModelSimplex V W 3 :=
  ofIsos F₀ ![F₀, F₁, F₂, F₃]
    (Fin.cases (Iso.refl _) (Fin.cases η (Fin.cases η'
      (Fin.cases (η ≪≫ θ) (fun i ↦ Fin.elim0 i)))))

/-- The first original diamond triangle is retained as an entire simplex face. -/
theorem diamond_first {F₀ F₁ F₂ F₃ : V ⟶ W}
    (η : F₀.functor ≅ F₁.functor) (θ : F₁.functor ≅ F₃.functor)
    (η' : F₀.functor ≅ F₂.functor) :
    (diamond η θ η').face (SimplexCategory.δ 2) =
      triangle η.hom θ.hom
        (fun _ ↦ W.waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ W.waldhausen.weq_iso _ inferInstance) := by
  unfold diamond
  apply ofIsos_face_triangle
  · exact Category.id_comp η.hom
  · rfl

/-- The second original diamond triangle uses its exact original commutative equation. -/
theorem diamond_second {F₀ F₁ F₂ F₃ : V ⟶ W}
    (η : F₀.functor ≅ F₁.functor) (θ : F₁.functor ≅ F₃.functor)
    (η' : F₀.functor ≅ F₂.functor) (θ' : F₂.functor ≅ F₃.functor)
    (he : η.hom ≫ θ.hom = η'.hom ≫ θ'.hom) :
    (diamond η θ η').face (SimplexCategory.δ 1) =
      triangle η'.hom θ'.hom
        (fun _ ↦ W.waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ W.waldhausen.weq_iso _ inferInstance) := by
  unfold diamond
  apply ofIsos_face_triangle
  · exact Category.id_comp η'.hom
  · exact he.symm

end Quillen.Waldhausen.IteratedS.ModelSimplex
