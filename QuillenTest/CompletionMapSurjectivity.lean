/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.ClassifyingSpace.CompletionMapSurjectivity
import Quillen.Topology.ClassifyingSpace.GroupHom

/-!
# Regression tests for the original localization-to-topology surjectivity bridge

The tests retain independent category universes, accept the literal localization
construction, verify original arrow classes, and recover categorical surjectivity
from the established single-object group-homomorphism comparison.
-/
noncomputable section
universe u₁ v₁ u₂ v₂
open CategoryTheory Quillen
attribute [local instance] Localization.groupoid

example {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (c : C) (a : c ⟶ c) :
    FundamentalGroup.mapOfEq (classifyingSpaceMapUniversal F)
      (classifyingSpaceMapUniversal_point F c)
      (Path.Homotopic.Quotient.mk (classifyingSpacePath a)) =
        Path.Homotopic.Quotient.mk (classifyingSpacePath (F.map a)) := by
  rw [FundamentalGroup.mapOfEq_apply]
  exact congrArg Path.Homotopic.Quotient.mk (classifyingSpaceMapUniversal_path_cast F a)

example {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (c : C)
    (h : Function.Surjective
      ((Localization.Construction.lift (W := (⊤ : MorphismProperty C))
        (F ⋙ (⊤ : MorphismProperty D).Q) (fun _ _ _ _ ↦ inferInstance)).mapEnd
          ((⊤ : MorphismProperty C).Q.obj c))) :
    Function.Surjective (piMap 0 (classifyingSpaceMapUniversal F)
      (classifyingSpaceMapUniversal_point F c)) :=
  classifyingSpaceMapUniversal_piOne_surjective F c h

example {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (c : C)
    [Subsingleton (End ((⊤ : MorphismProperty D).Q.obj (F.obj c)))] :
    Function.Surjective (piMap 0 (classifyingSpaceMapUniversal F)
      (classifyingSpaceMapUniversal_point F c)) := by
  apply classifyingSpaceMapUniversal_piOne_surjective F c
  intro a
  exact ⟨1, Subsingleton.elim (α := End ((⊤ : MorphismProperty D).Q.obj (F.obj c))) _ _⟩

example {G H : Type u₁} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) :
    Function.Surjective ((groupoidCompletionFunctorMap f.toFunctor).mapEnd
      ((⊤ : MorphismProperty (SingleObj G)).Q.obj (SingleObj.star G))) := by
  apply (classifyingSpaceMapUniversal_piOne_surjective_iff f.toFunctor _).mp
  simpa only [classifyingSpaceMapUniversal_eq, GroupoidClassifying.piOneMap,
    GroupoidClassifying.classifyingMap] using
    GroupoidClassifying.piOneMap_surjective f hf
