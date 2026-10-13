/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.FinitePosetSupport

/-! Semantic tests of actual finite full-subposet support, including empty support. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Quillen Quillen.FiniteNervePosetSupport
open scoped Topology Simplicial
universe u v
namespace QuillenTest.FiniteNervePosetSupport

open Quillen

/-- Every vertex of every original simplex is unchanged, including degenerate simplices. -/
theorem original_vertices {P : Type u} [PartialOrder P] (A : (nerve P).Subcomplex)
    (n : SimplexCategoryᵒᵖ) (a : A.toSSet.obj n) (i : Fin (n.unop.len + 1)) :
    (((factor A).app n a).obj i).val = a.val.obj i := rfl

/-- The entire original simplicial inclusion is retained. -/
theorem original_inclusion {P : Type u} [PartialOrder P] (A : (nerve P).Subcomplex) :
    factor A ≫ nerveMap (inclusion (vertices A)) = A.ι := factor_comp_inclusion A

/-- The chosen full subposet has finitely many actual objects. -/
theorem finite_actual_objects {P : Type u} [PartialOrder P] (A : (nerve P).Subcomplex)
    [SSet.Finite A] : Finite (vertices A) := (vertices_finite A).to_subtype

/-- The empty subcomplex yields the actual empty full subposet. -/
theorem empty_support {P : Type u} [PartialOrder P] :
    vertices (⊥ : (nerve P).Subcomplex) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨a, _⟩
  exact a.property

/-- A separate compact-source universe and an infinite-allowed ambient poset are supported. -/
theorem original_compact_map {P : Type u} [PartialOrder P] {T : Type v}
    [TopologicalSpace T] [CompactSpace T] (f : C(T, ClassifyingSpace P)) :
    ∃ s : Set P, s.Finite ∧ ∃ g : C(T, ClassifyingSpace s),
      (classifyingSpaceMap (inclusion s)).hom.comp g = f := compactMap_factors f

/-- Actual points in the infinite poset of natural numbers have exact finite support. -/
theorem infinite_poset_point (n : ℕ) :
    ∃ s : Set ℕ, s.Finite ∧ ∃ g : C(PUnit, ClassifyingSpace s),
      (classifyingSpaceMap (inclusion s)).hom.comp g =
        ContinuousMap.const PUnit (classifyingSpacePoint n) :=
  compactMap_factors (ContinuousMap.const PUnit (classifyingSpacePoint n))

end QuillenTest.FiniteNervePosetSupport
