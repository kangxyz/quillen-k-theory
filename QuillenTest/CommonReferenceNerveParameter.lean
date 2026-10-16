/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveParameter

/-! An entire common-reference edge is retained under a cyclic, globally nonmonotone relabeling.
The three actual model morphisms and their specified reference isomorphisms remain full nodes. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Convexity Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology
universe u
namespace QuillenTest.CommonReferenceNerveParameter
variable {V W : Model.{u}} (F : V ⟶ W)

/-- The enclosing cyclic order is not a simplex map; only the original first edge is used. -/
theorem cyclic_relabel_original_edge (A B C : CommonReferenceNerve.Node F)
    (z : StdSimplex ℝ (Fin 2)) :
    CommonReferenceNerve.parameter F ![C, A, B]
        (StdSimplex.map (![1, 2, 0] : Fin 3 → Fin 3)
          (StdSimplex.map (![0, 1] : Fin 2 → Fin 3) z)) =
      CommonReferenceNerve.parameter F ![A, B, C]
        (StdSimplex.map (![0, 1] : Fin 2 → Fin 3) z) := by
  exact CommonReferenceNerve.parameter_supported F ![A, B, C] ![C, A, B]
    ![1, 2, 0] (by intro i; fin_cases i <;> rfl)
    (SimplexCategory.Hom.mk ⟨![0, 1], by decide⟩) (by decide) z

end QuillenTest.CommonReferenceNerveParameter
