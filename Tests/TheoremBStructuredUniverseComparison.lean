/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.CategoryTheory.TheoremB.StructuredUniverseComparison

/-! Consumers of the original structured comparison with unrelated categorical universes. -/
noncomputable section
open CategoryTheory Quillen Quillen.TheoremB
universe u₁ v₁ u₂ v₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

example (F : C ⥤ D)
    (h : ∀ ⦃d e : D⦄ (f : d ⟶ e), IsWeakHomotopyEquivalence
      (classifyingSpaceMapUniversal (StructuredArrow.map (T := F) f)))
    (d : D) (z : HomotopyFiber (classifyingSpaceMapUniversal F) (classifyingSpacePoint d)) :
    ∃ x, Joined (structuredFiberComparisonUniversal F d x) z :=
  (structuredFiberComparisonUniversal_isWeakHomotopyEquivalence F h d).component_surjective z

example (F : C ⥤ D) (h : StructuredTransitionWeakEquivalencesUniversal F)
    (d : D) (x : ClassifyingSpace (StructuredArrow d F)) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (structuredFiberComparisonUniversal F d) (x := x) rfl) :=
  (structuredFiberComparisonUniversal_isWeakHomotopyEquivalence F h d).homotopy_bijective x n

example (F : C ⥤ D) (h : StructuredTransitionWeakEquivalencesUniversal F)
    (d : D) [IsEmpty (StructuredArrow d F)] :
    IsWeakHomotopyEquivalence (structuredFiberComparisonUniversal F d) :=
  structuredFiberComparisonUniversal_isWeakHomotopyEquivalence F h d

example (F : C ⥤ D) (d : D) (X : StructuredArrow d F) (t : unitInterval) :
    (structuredFiberComparisonUniversal F d (classifyingSpacePoint X)).1.2 t =
      classifyingSpacePath X.hom (unitInterval.symm t) :=
  structuredFiberComparisonUniversal_vertex_path F d X t

example (F : C ⥤ D) (c : C) :
    structuredFiberComparisonUniversal F (F.obj c)
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) =
      HomotopyFiber.basepoint (classifyingSpaceMapUniversal F) (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMapUniversal_point F c) :=
  structuredFiberComparisonUniversal_identity F c
