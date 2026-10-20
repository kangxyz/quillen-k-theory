/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceWeakZeroCone

/-!
# Original weak nulls on every normalization vertex

Every vertex slice of the finite normalization cone retains the entire original weak null.
Uniqueness from the chosen zero identifies an independently specified transformation, without
requiring that weak transformation to be invertible.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open Quillen.SimplexParameters Quillen.NumerableConnectorCover
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceWeakZero
variable {V W : Model.{u}} (F : V ⟶ W) {k : ℕ}
  (N : Fin (k + 1) → CommonReferenceNerve.Node F)
  (η : (zeroHom V W).functor ⟶ F.functor)
  (hη : ∀ X, W.waldhausen.weq (η.app X))

/-- Repetition isolates the original directed edge to the specified normalization vertex. -/
def vertexTriangle (i : Fin (k + 1)) : ⦋2⦌ ⟶ ⦋k + 2⦌ :=
  SimplexCategory.Hom.mk
    ⟨![0, i.succ.succ, i.succ.succ], by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all⟩

/-- The selected weak transformation is the exact edge of the original finite simplex. -/
theorem vertexTriangle_face (i : Fin (k + 1))
    (θ : (zeroHom V W).functor ⟶ (N i).1.functor)
    (hθ : ∀ X, W.waldhausen.weq (θ.app X)) :
    (simplex F N η hη).face (vertexTriangle i) =
      ModelSimplex.triangle θ (𝟙 _) hθ (fun _ ↦ W.waldhausen.weq.id_mem _) := by
  apply ModelSimplex.ext_diagram
  refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    ext X
    exact W.waldhausen.isZero.eq_of_src _ _
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    change (simplex F N η hη).diagram.map (𝟙 i.succ.succ) = 𝟙 _
    exact (simplex F N η hη).diagram.map_id _

/-- All times of an independently specified original weak zero edge are recovered. -/
theorem vertex_edge_native (i : Fin (k + 1))
    (θ : (zeroHom V W).functor ⟶ (N i).1.functor)
    (hθ : ∀ X, W.waldhausen.weq (θ.app X)) :
    PathLift (simplex F N η hη) (edge 0 i.succ.succ)
      (prespectrumTransformationHomotopy θ hθ) :=
  PathLift.trans_left _ (HomotopyLift.target _
    (triangle_lift _ _ _ _ _ _ (vertexTriangle_face F N η hη i θ hθ)))

/-- The scalar cone slice retains the exact original reversed edge coordinate. -/
theorem cone_vertex (i : Fin (k + 1)) (r : unitInterval) :
    coneParameter (r, StdSimplex.single i.succ) =
      (edge (k := k + 2) 0 i.succ.succ).symm r := by
  apply StdSimplex.ext
  change (simplexBoundaryCone r (StdSimplex.single i.succ)).weights = _
  rw [simplexCone_weights]
  simp only [StdSimplex.weights_single, Finsupp.mapDomain_single]
  simp [edge, StdSimplex.duple, Path.symm, Finsupp.smul_single]

/-- Every normalization vertex retains its specified weak null at all levels and times. -/
theorem coneFamily_vertex (i : Fin (k + 1))
    (θ : (zeroHom V W).functor ⟶ (N i).1.functor)
    (hθ : ∀ X, W.waldhausen.weq (θ.app X))
    (n : ℕ) (r : unitInterval) (x : (prespectrum V).space n) :
    coneFamily F N η hη n ((r, StdSimplex.single i.succ), x) =
      (prespectrumTransformationHomotopy θ hθ).level n (unitInterval.symm r, x) := by
  change prespectrumSimplexFamily (simplex F N η hη) n
    (coneParameter (r, StdSimplex.single i.succ), x) = _
  rw [cone_vertex]
  exact vertex_edge_native F N η hη i θ hθ n (unitInterval.symm r) x

end Quillen.Waldhausen.IteratedS.CommonReferenceWeakZero
