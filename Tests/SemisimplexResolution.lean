/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.CategoryTheory.SemisimplexResolution.Contraction
import Quillen.Topology.HomotopyGroups.WeakEquivalenceProperty

/-! Consumers of the actual all-semisimplex resolution, including degenerate chains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.SemisimplexResolution Quillen.ComposableArrows
open scoped Topology
universe u
namespace Quillen.Tests.SemisimplexResolution
variable (C : Type u) [SmallCategory C]

/-- The supplied equivalence has the original functor's forward map. -/
theorem original_forward_map :
    (lastVertexHomotopyEquiv C).toFun = (classifyingSpaceMap (lastVertex C)).hom :=
  lastVertexHomotopyEquiv_toFun C

/-- Every degree uses the original last-vertex map, including degree zero. -/
theorem original_homotopy_maps (x : ClassifyingSpace (Obj C)) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (classifyingSpaceMap (lastVertex C)).hom
      (x := x) rfl) := by
  have h := isWeakHomotopyEquivalence_of_homotopyEquiv (lastVertexHomotopyEquiv C)
  rw [lastVertexHomotopyEquiv_toFun] at h
  exact h.homotopy_bijective x n

/-- The exact face equation retains the entire original chain. -/
theorem original_chain_retained {d : C} (A : CostructuredArrow (lastVertex C) d) :
    indexFunctor (originalToAppendHom C A).index ⋙ (appendObj C A).chain = A.left.chain :=
  (originalToAppendHom C A).face

/-- The original displayed comma arrow is preserved strictly. -/
theorem original_comma_arrow {d : C} (A : CostructuredArrow (lastVertex C) d) :
    (lastVertex C).map (originalToAppend C A).left ≫ (appendCommaObj C A).hom = A.hom :=
  CostructuredArrow.w _

/-- Chains containing repeated identity arrows remain actual resolution objects. -/
def degenerateTwoSimplex (d : C) : Obj C :=
  ⟨2, (CategoryTheory.Functor.const (Fin 3)).obj d⟩

/-- No nondegeneracy hypothesis deletes a repeated-vertex original chain. -/
theorem degenerate_chain_vertex (d : C) :
    (lastVertex C).obj (degenerateTwoSimplex C d) = d := rfl

/-- An empty original category gives an empty resolution, with no chosen object. -/
theorem empty_resolution [IsEmpty C] : IsEmpty (Obj C) :=
  ⟨fun A => isEmptyElim (A.chain.obj 0)⟩

/-- The resolution inclusion uses the literal old index embedding. -/
theorem original_index {d : C} (A : CostructuredArrow (lastVertex C) d)
    (i : Fin (A.left.dim+1)) : (originalToAppend C A).left.index i = i.castSucc := rfl

end Quillen.Tests.SemisimplexResolution
