/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1SupportOrder

/-! Genuine face preservation under a relabeling that is ordered only on the used support. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes.BassH1Merged

/-- Only the actual support face, not an unused enclosing simplex, is required to be monotone. -/
def supportedFace {p q k : ℕ} (f : Fin (p + 1) → Fin (q + 1))
    (α : ⦋k⦌ ⟶ ⦋p⦌) (h : Monotone (f ∘ α.toOrderHom)) : ⦋k⦌ ⟶ ⦋q⦌ :=
  SimplexCategory.Hom.mk ⟨f ∘ α.toOrderHom, h⟩

/-- Whole diagrams on supported faces agree through the supplied proved full original nodes. -/
theorem supported_reference_face {V W : Model.{u}} {p q k : ℕ}
    (F : V ⟶ W) (N : Fin (p + 1) → Σ G : V ⟶ W, F.functor ≅ G.functor)
    (M : Fin (q + 1) → Σ G : V ⟶ W, F.functor ≅ G.functor)
    (f : Fin (p + 1) → Fin (q + 1)) (hn : ∀ i, M (f i) = N i)
    (α : ⦋k⦌ ⟶ ⦋p⦌) (h : Monotone (f ∘ α.toOrderHom)) :
    (ModelSimplex.ofIsos F (fun i ↦ (M i).1) (fun i ↦ (M i).2)).face
      (supportedFace f α h) =
    (ModelSimplex.ofIsos F (fun i ↦ (N i).1) (fun i ↦ (N i).2)).face α := by
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (fun i ↦ hn (α.toOrderHom i))

end Quillen.PerfectComplexes.BassH1Merged
