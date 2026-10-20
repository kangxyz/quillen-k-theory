/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceWeakZeroVertex

/-!
# Whole ordered faces of the finite weak-zero cone

The original zero and reference vertices stay fixed while an ordered normalization subchain
is selected. The entire cone family restricts exactly, with independent null and simplex times.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open Quillen.NumerableConnectorCover
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceWeakZero

/-- Extend an ordered face by retaining the initial vertex. -/
def keepInitial {l k : ℕ} (α : ⦋l⦌ ⟶ ⦋k⦌) : ⦋l + 1⦌ ⟶ ⦋k + 1⦌ :=
  SimplexCategory.Hom.mk ⟨Fin.cases 0 (fun i ↦ (α.toOrderHom i).succ), by
    intro i j hij
    cases i using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim (by simp at hij)
      | succ j =>
        exact Fin.succ_le_succ_iff.mpr
          (α.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hij))⟩

variable {V W : Model.{u}} (F : V ⟶ W) {l k : ℕ}
  (N : Fin (k + 1) → CommonReferenceNerve.Node F)
  (η : (zeroHom V W).functor ⟶ F.functor)
  (hη : ∀ X, W.waldhausen.weq (η.app X))

/-- Both distinguished initial vertices and the complete original transformation chain survive. -/
theorem simplex_face (α : ⦋l⦌ ⟶ ⦋k⦌) :
    (simplex F N η hη).face (keepInitial (keepInitial α)) =
      simplex F (N ∘ α.toOrderHom) η hη := by
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      cases i using Fin.cases <;> rfl
  · intro i j f
    have hij := leOfHom f
    cases i using Fin.cases with
    | zero =>
      ext X
      exact W.waldhausen.isZero.eq_of_src _ _
    | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim (by simp at hij)
      | succ j =>
        cases i using Fin.cases <;> cases j using Fin.cases <;>
          simp only [eqToHom_refl, Category.id_comp, Category.comp_id] <;> rfl

/-- The complete scalar cone commutes with a face that retains its initial vertex. -/
theorem coneParameter_face (α : ⦋l⦌ ⟶ ⦋k⦌) (r : unitInterval)
    (z : StdSimplex ℝ (Fin (l + 2))) :
    StdSimplex.map (keepInitial (keepInitial α)).toOrderHom (coneParameter (r, z)) =
      coneParameter (r, StdSimplex.map (keepInitial α).toOrderHom z) :=
  simplexCone_map_tail (keepInitial α).toOrderHom r z

/-- Restricting an entire normalization face preserves every original weak-null coordinate. -/
theorem coneFamily_face (α : ⦋l⦌ ⟶ ⦋k⦌) (n : ℕ) (r : unitInterval)
    (z : StdSimplex ℝ (Fin (l + 2))) (x : (prespectrum V).space n) :
    coneFamily F N η hη n
      ((r, StdSimplex.map (keepInitial α).toOrderHom z), x) =
      coneFamily F (N ∘ α.toOrderHom) η hη n ((r, z), x) := by
  change prespectrumSimplexFamily (simplex F N η hη) n
    (coneParameter (r, StdSimplex.map (keepInitial α).toOrderHom z), x) = _
  rw [← coneParameter_face, prespectrumSimplexFamily_face, simplex_face]
  rfl

end Quillen.Waldhausen.IteratedS.CommonReferenceWeakZero
