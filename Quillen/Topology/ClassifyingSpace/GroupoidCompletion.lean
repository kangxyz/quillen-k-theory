/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.ClassifyingSpace.ArrowPaths
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The comparison from categorical groupoid completion to continuous paths

The actual realized-arrow functor inverts every arrow, so the categorical
localization universal property extends it to the groupoid completion.
This constructs the canonical comparison without assuming it is full or faithful.
-/
@[expose] public section


noncomputable section
universe u v
open CategoryTheory
namespace Quillen

/-- Extend the realized-arrow functor to the actual groupoid localization. -/
def classifyingGroupoidCompletionFunctor (C : Type u) [Category.{v} C] :
    (⊤ : MorphismProperty C).Localization ⥤ FundamentalGroupoid (ClassifyingSpace C) :=
  Localization.Construction.lift (classifyingFundamentalGroupoidFunctor C)
    (fun _ _ _ _ => inferInstance)

/-- The extension preserves the original object vertices and arrow paths exactly. -/
@[simp] theorem toClassifyingGroupoidCompletionFunctor (C : Type u) [Category.{v} C] :
    (⊤ : MorphismProperty C).Q ⋙ classifyingGroupoidCompletionFunctor C =
      classifyingFundamentalGroupoidFunctor C :=
  Localization.Construction.fac _ _

/-- The canonical comparison on any chosen vertex endomorphism monoid.
The codomain is the actual topological fundamental group. -/
def classifyingGroupoidCompletionMap (C : Type u) [Category.{v} C] (c : C) :
    End ((⊤ : MorphismProperty C).Q.obj c) →*
      FundamentalGroup (ClassifyingSpace C) (classifyingSpacePoint c) :=
  (classifyingGroupoidCompletionFunctor C).mapEnd ((⊤ : MorphismProperty C).Q.obj c)

end Quillen
