/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.BoundedComparison
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
-- The public unit-component equation retains a hidden proof in the pinned mathlib version.
-- Import its implementation to use that equation; no private declaration is referenced.
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # The actual bounded-below derived unit on bounded complexes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u v' u'
namespace CategoryTheory.Functor
variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive]

/-- The complex-level and homotopy-level original units have the same invertibility locus. -/
theorem rightDerivedFunctorPlusUnit_isIso_iff (K : CochainComplex.Plus A) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) ↔
      IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj K)) := by
  rw [F.rightDerivedFunctorPlusUnit_app]
  rw [isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]

/-- The original bounded-below right-derived unit is invertible on a bounded complex whose
individual terms, placed in degree zero, are acyclic for the given functor. -/
theorem rightDerivedFunctorPlusUnit_isIso_of_term_bounds (K : CochainComplex.Plus A)
    (a b : ℤ) (hl : ∀ i, i < a → IsZero (K.obj.X i))
    (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hs : ∀ n, IsIso (F.rightDerivedFunctorPlusUnit.app
      (CochainComplex.singlePlus (K.obj.X n) 0))) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  rw [rightDerivedFunctorPlusUnit_isIso_iff]
  apply CochainComplex.isIso_app_of_term_bounds
    F.rightDerivedFunctorPlusUnith K a b hl hu
  intro n
  apply CochainComplex.isIso_app_single_of_zero
  exact (F.rightDerivedFunctorPlusUnit_isIso_iff _).mp (hs n)

end CategoryTheory.Functor
