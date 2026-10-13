/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.GroupCompletion.Symmetric
public import Quillen.Topology.ClassifyingSpace.MonoidalFundamentalGroup

/-!
# Original homotopy-group consumers for Grayson's category

These tests retain the original path transport, projection maps, unit vertex,
and inverse-object arrow. The fundamental-group conclusion concerns the actual
realization and its ordinary path-quotient fundamental group.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory MonoidalCategory Quillen Quillen.GroupCompletion
open scoped Topology unitInterval

namespace QuillenTest.GroupCompletionHomotopyGroups

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

example (X : Localization C C) :
    Nonempty (Path (classifyingSpacePoint (𝟙_ (Localization C C)))
      (classifyingSpacePoint (X ⊗ Localization.inverseObject X))) :=
  ⟨classifyingSpacePath (Localization.inverseArrow X)⟩

example (a b : FundamentalGroup (ClassifyingSpace (Localization C C))
    (classifyingSpacePoint (𝟙_ (Localization C C)))) : a * b = b * a :=
  classifyingUnitFundamentalGroup_mul_comm a b

example (n : ℕ) (a : ShiftedHomotopyGroup (Localization C C) (𝟙_ (Localization C C)) n) :
    classifyingUnitPiMultiplication n (1, a) = a :=
  classifyingUnitPiMultiplication_one_left n a

example (n : ℕ) (a : ShiftedHomotopyGroup (Localization C C) (𝟙_ (Localization C C)) n) :
    classifyingUnitPiMultiplication n (a, 1) = a :=
  classifyingUnitPiMultiplication_one_right n a

example {X : Type u} [TopologicalSpace X] {x y : X} (γ : Path x y) (n : ℕ)
    (a b : HomotopyGroup.Pi (n + 1) X x) :
    pathTransport γ (n + 1) (a * b) =
      pathTransport γ (n + 1) a * pathTransport γ (n + 1) b :=
  (pathTransportMulEquiv γ n).map_mul a b

example {D : Type u} [Category.{v} D] {F G : C ⥤ D} (η : F ⟶ G) (c : C) :
    classifyingSpaceNaturalTransformationTrack η c = classifyingSpacePath (η.app c) :=
  classifyingSpaceNaturalTransformationTrack_eq η c

end QuillenTest.GroupCompletionHomotopyGroups
