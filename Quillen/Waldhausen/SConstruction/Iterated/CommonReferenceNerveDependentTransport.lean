/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveParameter
public import Quillen.Waldhausen.SConstruction.Iterated.ModelReferenceReanchor

/-! Dependent full-node families transported by actual index and reference equalities. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve

/-- Index equality transports every full node; reference equality proofs are proof-irrelevant. -/
theorem reanchorNodes_index_eq {V W : Model.{u}} {α : Sort v} {k : ℕ}
    (H : α → (V ⟶ W)) (N : (a : α) → Fin (k + 1) → Node (H a))
    {a b : α} (h : a = b) (F : V ⟶ W)
    (e : F.functor = (H a).functor) (e' : F.functor = (H b).functor) :
    ModelSimplex.reanchorNodes (eqToIso e) (N a) =
      ModelSimplex.reanchorNodes (eqToIso e') (N b) := by
  subst b
  rfl

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve
