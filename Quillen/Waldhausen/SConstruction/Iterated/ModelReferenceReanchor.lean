/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceFaces

/-! Full dependent-node reference transport, factored before geometric specialization. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Waldhausen.IteratedS.ModelSimplex
variable {V W : Model.{u}} {k : ℕ} {F₀ F₁ : V ⟶ W}

/-- The same model nodes with their reference comparisons transported from `F₁` to `F₀` by
composition with `e`.
-/
def reanchorNodes (e : F₀.functor ≅ F₁.functor)
    (N : Fin (k + 1) → Σ F : V ⟶ W, F₁.functor ≅ F.functor)
    (i : Fin (k + 1)) : Σ F : V ⟶ W, F₀.functor ≅ F.functor :=
  ⟨(N i).1, e ≪≫ (N i).2⟩

/-- The model simplex constructed from the given nodes using `F₀` as reference and the comparisons
transported along `e`.
-/
def reanchorSimplex (e : F₀.functor ≅ F₁.functor)
    (N : Fin (k + 1) → Σ F : V ⟶ W, F₁.functor ≅ F.functor) : ModelSimplex V W k :=
  ofIsos F₀ (fun i ↦ (reanchorNodes e N i).1) (fun i ↦ (reanchorNodes e N i).2)

theorem reanchorSimplex_eq (e : F₀.functor ≅ F₁.functor)
    (N : Fin (k + 1) → Σ F : V ⟶ W, F₁.functor ≅ F.functor) :
    reanchorSimplex e N = ofIsos F₁ (fun i ↦ (N i).1) (fun i ↦ (N i).2) :=
  ofIsos_change_reference e _ _

end Quillen.Waldhausen.IteratedS.ModelSimplex
