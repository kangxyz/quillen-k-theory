/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.CategoryTheory.TheoremB.NaturalTransformationFiberCancellation

/-! # Original source-fixed fiber cancellation consumers -/
noncomputable section
open CategoryTheory Quillen Quillen.TheoremB
open scoped Topology unitInterval
universe u
variable {A C D : Type u} [SmallCategory A] [SmallCategory C] [SmallCategory D]
  (P : A ⥤ C) (F : C ⥤ D) (d : D) {K : A ⥤ D}
  (α : K ⟶ P ⋙ F) (β : P ⋙ F ⟶ (Functor.const A).obj d)

example :
    (HomotopyFiber.lift (classifyingSpaceMap F).hom (classifyingSpacePoint d)
      (classifyingSpaceMap P).hom
      (naturalTransformationCancellationNullhomotopy P F d α β)).Homotopic
      (naturalTransformationFiberLift P F d β) :=
  ⟨naturalTransformationFiberCancellationHomotopy P F d α β⟩

example (s t : unitInterval) (x : ClassifyingSpace A) :
    (naturalTransformationFiberCancellationHomotopy P F d α β (s, x)).val.2 t =
      naturalTransformationCancellationHomotopy α β (s, (t, x)) := rfl
