/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.TheoremB.CompositionHomotopy

/-! Consumers retain the original composite arrow, both original edge tracks and fixed endpoints. -/
@[expose] public section

noncomputable section

open CategoryTheory Quillen Quillen.TheoremB
open scoped Topology unitInterval

universe u

namespace QuillenTest.CompositionHomotopy

open Quillen

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)

lemma original_composite_face (s : unitInterval) (x : ClassifyingSpace C) :
    naturalTransformationCompositionHomotopy α β (0, (s, x)) =
      classifyingSpaceNaturalTransformationHomotopy (α ≫ β) (s, x) :=
  (naturalTransformationCompositionHomotopy α β).apply_zero (s, x)

lemma original_two_tracks_face (s : unitInterval) (x : ClassifyingSpace C) :
    naturalTransformationCompositionHomotopy α β (1, (s, x)) =
      ((classifyingSpaceNaturalTransformationHomotopy α).trans
        (classifyingSpaceNaturalTransformationHomotopy β)) (s, x) :=
  (naturalTransformationCompositionHomotopy α β).apply_one (s, x)

lemma original_source_fixed (r : unitInterval) (x : ClassifyingSpace C) :
    naturalTransformationCompositionHomotopy α β (r, (0, x)) = classifyingSpaceMap F x :=
  ((naturalTransformationCompositionHomotopy α β).eq_fst r (Or.inl rfl)).trans
    ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).apply_zero x)

lemma original_target_fixed (r : unitInterval) (x : ClassifyingSpace C) :
    naturalTransformationCompositionHomotopy α β (r, (1, x)) = classifyingSpaceMap H x :=
  ((naturalTransformationCompositionHomotopy α β).eq_fst r (Or.inr rfl)).trans
    ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).apply_one x)

lemma original_path_parameters (r s : unitInterval) (x : ClassifyingSpace C) :
    naturalTransformationCompositionPathHomotopy α β x (r, s) =
      naturalTransformationCompositionHomotopy α β (r, (s, x)) := rfl

end QuillenTest.CompositionHomotopy
