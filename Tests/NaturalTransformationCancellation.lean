/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.CategoryTheory.TheoremB.NaturalTransformationCancellation

/-! # Original source-fixed natural-transformation cancellation consumers -/
noncomputable section
open CategoryTheory Quillen Quillen.TheoremB
open scoped Topology unitInterval
universe u
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)

example :
    ((classifyingSpaceNaturalTransformationHomotopy α).symm.trans
      (classifyingSpaceNaturalTransformationHomotopy (α ≫ β))).toContinuousMap.HomotopyRel
      (classifyingSpaceNaturalTransformationHomotopy β).toContinuousMap
      {z : unitInterval × ClassifyingSpace C | z.1 = 0 ∨ z.1 = 1} :=
  naturalTransformationCancellationHomotopy α β

example (x : ClassifyingSpace C) :
    (((classifyingSpaceNaturalTransformationHomotopy α).evalAt x).symm.trans
      ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).evalAt x)).Homotopic
      ((classifyingSpaceNaturalTransformationHomotopy β).evalAt x) :=
  ⟨naturalTransformationCancellationPathHomotopy α β x⟩

example (r : unitInterval) (x : ClassifyingSpace C) :
    naturalTransformationCancellationHomotopy α β (r, (0, x)) =
      ((classifyingSpaceNaturalTransformationHomotopy α).symm.trans
        (classifyingSpaceNaturalTransformationHomotopy (α ≫ β))) (0, x) :=
  (naturalTransformationCancellationHomotopy α β).eq_fst r (Or.inl rfl)
