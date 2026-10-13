/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.ClassifyingSpace.GroupHom

/-! Regression tests for actual group classifying maps and their first homotopy groups. -/

open CategoryTheory Quillen Quillen.GroupoidClassifying

universe u
variable {G H : Type u} [Group G] [Group H]

example (f : G →* H) (a : G) (h : f a = 1) :
    piOneMap f (singleObjPiOneEquiv G a) = 1 :=
  (piOneMap_equiv_eq_one_iff f a).2 h

example (f : G →* H) (hf : Function.Injective f)
    (x y : HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj G))
      (classifyingSpacePoint (SingleObj.star G))) (h : piOneMap f x = piOneMap f y) : x = y :=
  piOneMap_injective f hf h

example (f : G →* H) (hf : Function.Surjective f)
    (y : HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj H))
      (classifyingSpacePoint (SingleObj.star H))) : ∃ x, piOneMap f x = y :=
  piOneMap_surjective f hf y
