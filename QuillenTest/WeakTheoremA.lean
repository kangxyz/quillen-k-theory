/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.TheoremA.WeakComma

/-!
# Consumers of weak Quillen Theorem A

These consumers retain the original functor map, all degrees including zero,
actual vertex-fiber comparison, independent discrete-base universes, and the
empty-source obstruction. No global contraction is part of the hypotheses.
-/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology Simplicial unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
namespace QuillenTest.WeakTheoremA

open Quillen

/-- The original functor map induces bijections in every degree. -/
theorem original_homotopy_maps {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D)
    (h : ∀ d : D, IsWeakHomotopyEquivalence
      (ContinuousMap.const (ClassifyingSpace (CostructuredArrow F d))
        (PUnit.unit : PUnit.{u + 1}))) (x : ClassifyingSpace C) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (classifyingSpaceMap F).hom
      (x := x) rfl) :=
  (TheoremA.classifyingSpaceMap_isWeakHomotopyEquivalence_of_weak_comma F h).homotopy_bijective x n

/-- Component surjectivity is retained for every actual target point. -/
theorem original_component_surjectivity {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D)
    (h : ∀ d : D, IsWeakHomotopyEquivalence
      (ContinuousMap.const (ClassifyingSpace (CostructuredArrow F d))
        (PUnit.unit : PUnit.{u + 1}))) (y : ClassifyingSpace D) :
    ∃ x, Joined ((classifyingSpaceMap F).hom x) y :=
  (TheoremA.classifyingSpaceMap_isWeakHomotopyEquivalence_of_weak_comma F h).component_surjective y

/-- Finite nullhomotopies control the original zeroth map, not just groups. -/
theorem finite_comma_zeroth {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D)
    (h : ∀ d : D, ∀ A : (nerve (CostructuredArrow F d)).Subcomplex,
      SSet.Finite A → (SSet.toTop.map A.ι).hom.Nullhomotopic) (x : ClassifyingSpace C) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (classifyingSpaceMap F).hom
      (x := x) rfl) :=
  (TheoremA.classifyingSpaceMap_isWeakHomotopyEquivalence_of_finite_comma_nullhomotopic
    F h).homotopy_bijective x 0

/-- A source with empty realization cannot satisfy the weak-comma tests when
there is a target object. -/
theorem empty_source_obstruction {C D : Type u} [SmallCategory C] [SmallCategory D]
    [IsEmpty (ClassifyingSpace C)] (F : C ⥤ D) (d : D) :
    ¬ (∀ e : D, IsWeakHomotopyEquivalence
      (ContinuousMap.const (ClassifyingSpace (CostructuredArrow F e))
        (PUnit.unit : PUnit.{u + 1}))) := by
  intro h
  obtain ⟨x, _⟩ := (TheoremA.classifyingSpaceMap_isWeakHomotopyEquivalence_of_weak_comma
    F h).component_surjective (classifyingSpacePoint d)
  exact isEmptyElim x

/-- The complete weak vertex comparison uses the literal existing map. -/
theorem actual_vertex_fiber {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})
    (h : Quillen.CartesianRealization.Skeletal.TransitionWeakCartesian
      (TheoremA.replacementPointAugmentation H)) (d : D) (x : |H.obj d|) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (TheoremB.vertexFiberComparison H d) (x := x) rfl) :=
  (TheoremB.vertexFiberComparison_isWeakHomotopyEquivalence H h d).homotopy_bijective x n

/-- Discrete restriction allows unrelated source, target and base universes. -/
theorem separate_discrete_universes {X : Type u} {Y : Type v} {B : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B] [DiscreteTopology B]
    (p : C(X, B)) (q : C(Y, B)) (f : C(X, Y)) (sq : q.comp f = p) (b : B)
    (h : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence (discreteStrictFiberMap p q f sq b) :=
  discreteStrictFiberMap_isWeakHomotopyEquivalence p q f sq b h

/-- A homotopy need not keep the image of the chosen source point fixed. -/
theorem unbased_homotopy {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : IsWeakHomotopyEquivalence f) (H : f.Homotopy g)
    (x : X) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) g (x := x) rfl) :=
  (h.of_homotopy H).homotopy_bijective x n

/-- The singleton-base equivalence retains the actual total coordinate. -/
theorem point_pullback_original_coordinate {X A B : Type u}
    [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    [Unique A] [Subsingleton B] (q : C(X, B)) (g : C(A, B))
    (z : HomotopyPullback q g) : pointBasePullbackHomeomorph q g z = z.val.2.1 := rfl

end QuillenTest.WeakTheoremA
