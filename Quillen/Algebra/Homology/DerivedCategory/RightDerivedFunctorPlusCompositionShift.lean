/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.Algebra.Homology.CochainComplexPlusShift
public import Quillen.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComposition

/-! # Shift compatibility of the original composite derived unit -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
/-- Both original factors make the composite installed unit shift-compatible. -/
instance Functor.rightDerivedFunctorPlusCompUnitCommShift
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive] :
    NatTrans.CommShift (Functor.rightDerivedFunctorPlusCompUnit F G) ℤ := by
  unfold Functor.rightDerivedFunctorPlusCompUnit
  infer_instance
end CategoryTheory
