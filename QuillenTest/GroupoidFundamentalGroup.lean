/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.FundamentalGroup

/-! # Original groupoid loops, inverse comparison and independent universes -/
@[expose] public section

open Quillen.GroupoidClassifying


noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe u v
namespace QuillenTest.GroupoidFundamentalGroup

open Quillen
open GroupoidClassifying

/-- The original comparison realizes precisely the given arrow. -/
theorem original_arrow {C : Type u} [Category.{v} C] [IsGroupoid C] (c : C) (g : End c) :
    fundamentalGroupEquiv c g = Path.Homotopic.Quotient.mk (classifyingSpacePath g) := rfl

/-- Every actual topological loop is represented by the unchanged categorical arrow map. -/
theorem actual_loop_surjective {C : Type u} [Category.{v} C] [IsGroupoid C] (c : C)
    (a : FundamentalGroup (ClassifyingSpace C) (classifyingSpacePoint c)) :
    ∃ g : End c, Path.Homotopic.Quotient.mk (classifyingSpacePath g) = a :=
  (fundamentalGroupMap_bijective_general c).surjective a

/-- No nonidentity original automorphism becomes a nullhomotopic original loop. -/
theorem original_arrow_detection {C : Type u} [Category.{v} C] [IsGroupoid C] (c : C)
    (g : End c) (h : (Path.Homotopic.Quotient.mk (classifyingSpacePath g) :
      FundamentalGroup (ClassifyingSpace C) (classifyingSpacePoint c)) =
        fundamentalGroupEquiv c 1) : g = 1 := by
  apply (fundamentalGroupEquiv c).injective
  exact h

/-- The group-nerve comparison retains the original realized loop in genuine Pi 1. -/
theorem original_group_pi_one (G : Type u) [Group G] (g : G) :
    singleObjPiOneEquiv G g = HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (Path.Homotopic.Quotient.mk (classifyingSpacePath (SingleObj.toEnd G g))) := rfl

/-- The comparison preserves the original possibly noncommutative multiplication. -/
theorem original_group_product (G : Type u) [Group G] (g h : G) :
    singleObjPiOneEquiv G (g * h) = singleObjPiOneEquiv G g * singleObjPiOneEquiv G h :=
  map_mul _ _ _

/-- Every original Pi 1 element has its genuine inverse-image group element. -/
theorem original_group_inverse (G : Type u) [Group G]
    (a : HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj G))
      (classifyingSpacePoint (SingleObj.star G))) :
    singleObjPiOneEquiv G ((singleObjPiOneEquiv G).symm a) = a :=
  (singleObjPiOneEquiv G).apply_symm_apply a

/-- The point-fiber comparison retains the entire original path, before quotienting. -/
theorem original_fiber_path {C : Type u} [SmallCategory C] (c : C) (g : c ⟶ c) :
    pointFiberLoopHomeomorph c (TheoremB.fiberComparison (pointFunctor c) c
      (classifyingSpacePoint (CostructuredArrow.mk (S := pointFunctor c)
        (Y := Discrete.mk PUnit.unit) g))) = classifyingSpacePath g :=
  pointFiberLoopHomeomorph_vertex c g

end QuillenTest.GroupoidFundamentalGroup
