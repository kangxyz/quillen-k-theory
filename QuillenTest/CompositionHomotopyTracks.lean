/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.TheoremB.CompositionHomotopy
public import Quillen.CategoryTheory.TheoremB.CompositionHomotopyTracks

/-!
# Consumers for full realized composition coherence and its exact vertex tracks

The tests use the existing whole-source relative homotopy and its literal
pointwise path restriction, then the new restriction to actual component edges.
Both owners are imported together, without extra inhabitedness or coherence
hypotheses on the categories, functors, or natural transformations.
-/

@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.TheoremB
universe u
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)

example :
    (classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).toContinuousMap.HomotopyRel
      ((classifyingSpaceNaturalTransformationHomotopy α).trans
        (classifyingSpaceNaturalTransformationHomotopy β)).toContinuousMap
      {z : unitInterval × ClassifyingSpace C | z.1 = 0 ∨ z.1 = 1} :=
  naturalTransformationCompositionHomotopy α β

example (x : ClassifyingSpace C) :
    ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).evalAt x).Homotopy
      (((classifyingSpaceNaturalTransformationHomotopy α).evalAt x).trans
        ((classifyingSpaceNaturalTransformationHomotopy β).evalAt x)) :=
  naturalTransformationCompositionPathHomotopy α β x

example (c : C) :
    (classifyingSpacePath (α.app c ≫ β.app c)).Homotopy
      ((classifyingSpacePath (α.app c)).trans (classifyingSpacePath (β.app c))) :=
  naturalTransformationCompositionVertexPathHomotopy α β c

example (c : C) (t : unitInterval) :
    ((classifyingSpaceNaturalTransformationHomotopy α).trans
      (classifyingSpaceNaturalTransformationHomotopy β)) (t, classifyingSpacePoint c) =
      ((classifyingSpacePath (α.app c)).trans (classifyingSpacePath (β.app c))) t :=
  classifyingHomotopy_trans_vertex α β c t

example (c : C) (s t : unitInterval) :
    naturalTransformationCompositionVertexPathHomotopy α β c (s, t) =
      naturalTransformationCompositionHomotopy α β (s, (t, classifyingSpacePoint c)) :=
  naturalTransformationCompositionVertexPathHomotopy_apply α β c s t

example (x : ClassifyingSpace C) (s : unitInterval) :
    naturalTransformationCompositionHomotopy α β (s, (0, x)) =
      classifyingSpaceMap F x :=
  ((naturalTransformationCompositionHomotopy α β).prop' s (0, x) (Or.inl rfl)).trans
    ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).apply_zero x)

example (x : ClassifyingSpace C) (s : unitInterval) :
    naturalTransformationCompositionHomotopy α β (s, (1, x)) =
      classifyingSpaceMap H x :=
  ((naturalTransformationCompositionHomotopy α β).prop' s (1, x) (Or.inr rfl)).trans
    ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).apply_one x)
