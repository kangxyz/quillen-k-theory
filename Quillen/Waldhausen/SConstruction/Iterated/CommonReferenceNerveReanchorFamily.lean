/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerve
public import Quillen.Waldhausen.SConstruction.Iterated.ModelReferenceReanchor

/-! Whole native families are invariant under the specified full reference reanchoring. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve

/-- Reanchoring preserves the complete family, including its genuine loop level zero. -/
theorem prespectrumFamily_reanchor {V W : Model.{u}} {F G : V ⟶ W} {k : ℕ}
    (e : F.functor ≅ G.functor) (N : Fin (k + 1) → Node G) (n : ℕ) :
    prespectrumFamily F (ModelSimplex.reanchorNodes e N) n = prespectrumFamily G N n := by
  rw [prespectrumFamily_eq, prespectrumFamily_eq]
  change prespectrumSimplexFamily (ModelSimplex.reanchorSimplex e N) n = _
  rw [ModelSimplex.reanchorSimplex_eq]

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve
