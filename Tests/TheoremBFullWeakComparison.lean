/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.TheoremB.FullWeakComparison

/-! # Consumers retaining arbitrary comma vertices and actual projections -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

example (h : TransitionWeakEquivalences F) (d : D)
    (z : HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :
    ∃ x, Joined (fiberComparison F d x) z :=
  (fiberComparison_isWeakHomotopyEquivalence F h d).component_surjective z

example (h : TransitionWeakEquivalences F) (d : D) [IsEmpty (CostructuredArrow F d)] :
    IsWeakHomotopyEquivalence (fiberComparison F d) :=
  fiberComparison_isWeakHomotopyEquivalence F h d

example (h : TransitionWeakEquivalences F) (d : D)
    (hD : IsWeakHomotopyEquivalence (ContinuousMap.const (ClassifyingSpace D)
      (PUnit.unit : PUnit.{u + 1}))) :
    IsWeakHomotopyEquivalence (classifyingSpaceMap (CostructuredArrow.proj F d)).hom :=
  commaProjection_isWeakHomotopyEquivalence_of_weakBase F h d hD
end Quillen.TheoremB
