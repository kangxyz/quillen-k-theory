/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.ClassifyingSpace.Groupoid

/-! # Consumers of original groupoid asphericity and its actual comparison maps -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe u v
namespace Quillen.Tests.GroupoidAsphericity

/-- Positive discrete loops are literally constant before homotopy quotienting. -/
theorem discrete_cube {X : Type u} [TopologicalSpace X] [DiscreteTopology X]
    (x : X) (n : ℕ) (p : GenLoop (Fin (n + 1)) X x) : p = GenLoop.const :=
  genLoop_eq_const_of_discrete x n p

/-- No nonemptiness assumption is added for the discrete category's arbitrary points. -/
theorem discrete_category (A : Type u) (x : ClassifyingSpace (Discrete A)) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 1) (ClassifyingSpace (Discrete A)) x) :=
  discreteClassifying_subsingleton_pi A x n

/-- The categorical comma equivalence retains each original arrow exactly. -/
theorem original_comma_arrow {C : Type u} [SmallCategory C] (c d : C)
    (X : CostructuredArrow (GroupoidClassifying.pointFunctor c) d) :
    ((GroupoidClassifying.pointCommaEquivalence c d).functor.obj X).as = X.hom := rfl

/-- Common-universe passage preserves the original chosen object vertex. -/
theorem original_vertex {C : Type u} [Category.{v} C] (c : C) :
    GroupoidClassifying.asSmallClassifyingHomeomorph C (classifyingSpacePoint c) =
      classifyingSpacePoint (AsSmall.up.obj c) :=
  GroupoidClassifying.asSmallClassifyingHomeomorph_point C c

/-- Arbitrary groupoids, independent universes, arbitrary basepoints, and degree two are included.
  -/
theorem original_groupoid {C : Type u} [Category.{v} C] [IsGroupoid C]
    (x : ClassifyingSpace C) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 2) (ClassifyingSpace C) x) : a = 1 := by
  let := GroupoidClassifying.subsingleton_higher_pi_at x n
  exact Subsingleton.elim _ _

/-- The one-object nerve uses an arbitrary group; no abelian-group premise is needed. -/
theorem original_group (G : Type u) [Group G] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 2) (ClassifyingSpace (SingleObj G))
      (classifyingSpacePoint (SingleObj.star G))) : a = 1 := by
  let := GroupoidClassifying.singleObj_subsingleton_higher_pi G n
  exact Subsingleton.elim _ _

end Quillen.Tests.GroupoidAsphericity
