/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexIsomorphism

/-! Restriction and change of the common reference preserve entire original simplex diagrams. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Simplicial
universe u
namespace Quillen.Waldhausen.IteratedS.ModelSimplex
variable {V W : Model.{u}}

theorem ofIsos_face {k l : ℕ} (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (F i).functor) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    (ofIsos F₀ F ρ).face α =
      ofIsos F₀ (fun i ↦ F (α.toOrderHom i)) (fun i ↦ ρ (α.toOrderHom i)) := by
  apply ext_diagram
  rfl

theorem ofIsos_change_reference {k : ℕ} {F₀ F₁ : V ⟶ W}
    (e : F₀.functor ≅ F₁.functor) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₁.functor ≅ (F i).functor) :
    ofIsos F₀ F (fun i ↦ e ≪≫ ρ i) = ofIsos F₁ F ρ := by
  apply ext_diagram
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  apply heq_of_eq
  dsimp only [ofIsos]
  simp [Category.assoc]
/-- Congruence keeps the exact-functor and reference-isomorphism components together. -/
theorem ofIsos_nodes_congr {k : ℕ} {F₀ : V ⟶ W}
    (N M : Fin (k + 1) → Σ F : V ⟶ W, F₀.functor ≅ F.functor)
    (e : ∀ i, N i = M i) :
    ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2) =
      ofIsos F₀ (fun i ↦ (M i).1) (fun i ↦ (M i).2) := by
  have h := funext e
  subst M
  rfl

end Quillen.Waldhausen.IteratedS.ModelSimplex
