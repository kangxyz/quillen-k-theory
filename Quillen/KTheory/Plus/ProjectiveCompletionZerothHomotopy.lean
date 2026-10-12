/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus.ProjectiveCompletionKZero
public import Quillen.Topology.ClassifyingSpace.ZerothHomotopy

/-!
# The actual path components of projective completion are the original K₀

The genuine path-component quotient of the original completion classifying
space is identified first with categorical components, then with the existing
Grothendieck group and the unchanged homotopical Quillen K₀. Original object
vertices have exactly numerator-minus-denominator grade. Change of rings uses
the quotient map of the original continuous completion map.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory

namespace Quillen.FiniteProjectiveModule

attribute [local instance] categoryDirectSumMonoidal directSumMonoidal

variable (R : Type u) [Ring R]

/-- The original virtual grading classifies actual topological completion components. -/
def completionZerothHomotopyGrothendieckEquiv :
    ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory R)) ≃
      (exactStructure R).GrothendieckGroup :=
  (classifyingSpaceZerothHomotopyEquiv (GroupCompletionCategory R)).trans
    (completionComponentGrothendieckEquiv R).toEquiv

/-- The actual completion path-component quotient identifies with the original Quillen K₀. -/
def completionZerothHomotopyKZeroEquiv :
    ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory R)) ≃ (exactStructure R).K 0 :=
  (classifyingSpaceZerothHomotopyEquiv (GroupCompletionCategory R)).trans
    (completionComponentKZeroEquiv R)

/-- The original object vertex keeps its exact virtual grade. -/
@[simp] theorem completionZerothHomotopyGrothendieckEquiv_point (X : GroupCompletionCategory R) :
    completionZerothHomotopyGrothendieckEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint X)) = completionGrade R X := by
  change completionComponentGrothendieckEquiv R
    (classifyingSpaceZerothHomotopyEquiv _ (ZerothHomotopy.mk (classifyingSpacePoint X))) = _
  rw [classifyingSpaceZerothHomotopyEquiv_point]
  rfl

/-- The original object vertex keeps its preexisting homotopical virtual K₀ class. -/
@[simp] theorem completionZerothHomotopyKZeroEquiv_point (X : GroupCompletionCategory R) :
    completionZerothHomotopyKZeroEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint X)) = completionKZeroClass R X := by
  change completionComponentKZeroEquiv R
    (classifyingSpaceZerothHomotopyEquiv _ (ZerothHomotopy.mk (classifyingSpacePoint X))) = _
  rw [classifyingSpaceZerothHomotopyEquiv_point]
  rfl

/-- Every original pair has numerator-minus-denominator grade, without any rank assumption. -/
theorem completionZerothHomotopyGrothendieckEquiv_pair (A B : IsoCategory R) :
    completionZerothHomotopyGrothendieckEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint (completionPair R A B))) =
      (exactStructure R).grothendieckClass B.of -
        (exactStructure R).grothendieckClass A.of :=
  completionZerothHomotopyGrothendieckEquiv_point R (completionPair R A B)

/-- The original K₀ equivalence has the unchanged numerator and denominator object classes. -/
theorem completionZerothHomotopyKZeroEquiv_pair (A B : IsoCategory R) :
    completionZerothHomotopyKZeroEquiv R
      (ZerothHomotopy.mk (classifyingSpacePoint (completionPair R A B))) =
      (exactStructure R).kZeroObjectClass B.of / (exactStructure R).kZeroObjectClass A.of := by
  rw [completionZerothHomotopyKZeroEquiv_point]
  exact completionKZeroClass_eq_objectClasses R (completionPair R A B)

variable {R} {S : Type u} [Ring S]

/-- The actual original continuous change-of-rings map induces this map on path components. -/
def completionZerothHomotopyBaseChange (f : R →+* S) :
    ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) →
      ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory Sᵐᵒᵖ)) :=
  ZerothHomotopy.lift (fun x ↦ ZerothHomotopy.mk (completionBaseChangeMap f x))
    (fun _ _ p ↦ ZerothHomotopy.sound (p.map (completionBaseChangeMap f).continuous))

/-- No original point is changed before taking its image component. -/
@[simp] theorem completionZerothHomotopyBaseChange_mk (f : R →+* S)
    (x : ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) :
    completionZerothHomotopyBaseChange f (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (completionBaseChangeMap f x) := rfl

/-- The topological quotient map preserves the exact original image vertex. -/
theorem completionZerothHomotopyBaseChange_point (f : R →+* S)
    (X : GroupCompletionCategory Rᵐᵒᵖ) :
    completionZerothHomotopyBaseChange f (ZerothHomotopy.mk (classifyingSpacePoint X)) =
      ZerothHomotopy.mk (classifyingSpacePoint ((completionBaseChange f).obj X)) := by
  rw [completionZerothHomotopyBaseChange_mk]
  exact congrArg ZerothHomotopy.mk (classifyingSpaceMapUniversal_point (completionBaseChange f) X)

/-- The actual topological and categorical change-of-rings component maps agree. -/
theorem completionZerothHomotopyBaseChange_components (f : R →+* S)
    (a : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ))) :
    classifyingSpaceZerothHomotopyEquiv (GroupCompletionCategory Sᵐᵒᵖ)
      (completionZerothHomotopyBaseChange f a) =
    completionComponentsBaseChange f
      (classifyingSpaceZerothHomotopyEquiv (GroupCompletionCategory Rᵐᵒᵖ) a) := by
  obtain ⟨X, rfl⟩ :=
    classifyingSpaceVertexComponent_surjective (GroupCompletionCategory Rᵐᵒᵖ) a
  rw [completionZerothHomotopyBaseChange_point, classifyingSpaceZerothHomotopyEquiv_point,
    classifyingSpaceZerothHomotopyEquiv_point, completionComponentsBaseChange_mk]
  rfl

/-- The actual topological grading is natural for arbitrary ring homomorphisms. -/
theorem completionZerothHomotopyGrothendieckEquiv_baseChange (f : R →+* S)
    (a : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ))) :
    completionZerothHomotopyGrothendieckEquiv Sᵐᵒᵖ (completionZerothHomotopyBaseChange f a) =
      (rightBaseChangeExact f).grothendieckMap
        (completionZerothHomotopyGrothendieckEquiv Rᵐᵒᵖ a) := by
  obtain ⟨X, rfl⟩ :=
    classifyingSpaceVertexComponent_surjective (GroupCompletionCategory Rᵐᵒᵖ) a
  rw [completionZerothHomotopyBaseChange_point,
    completionZerothHomotopyGrothendieckEquiv_point,
    completionZerothHomotopyGrothendieckEquiv_point]
  exact completionGrade_baseChange f X

/-- Naturality retains the actual continuous completion map and the unchanged original K₀ map. -/
theorem completionZerothHomotopyKZeroEquiv_baseChange (f : R →+* S)
    (a : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ))) :
    (rightBaseChangeExact f).KMap 0 (completionZerothHomotopyKZeroEquiv Rᵐᵒᵖ a) =
      completionZerothHomotopyKZeroEquiv Sᵐᵒᵖ (completionZerothHomotopyBaseChange f a) := by
  obtain ⟨X, rfl⟩ :=
    classifyingSpaceVertexComponent_surjective (GroupCompletionCategory Rᵐᵒᵖ) a
  rw [completionZerothHomotopyBaseChange_point, completionZerothHomotopyKZeroEquiv_point,
    completionZerothHomotopyKZeroEquiv_point]
  exact completionKZeroClass_baseChange f X

end Quillen.FiniteProjectiveModule
