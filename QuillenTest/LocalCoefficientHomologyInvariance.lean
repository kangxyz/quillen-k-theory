/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.ClassifyingSpace.GroupCompletionHomology

/-!
# Consumers of homotopy invariance with actual coefficient transport

These tests retain endpoint maps, coefficient conversions and the original
coordinate translations on the realized categorical completion.
-/

noncomputable section

open CategoryTheory Quillen Quillen.LocalCoefficients
open scoped ContinuousMap

universe u v

section Spaces

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

example {f g : C(X, Y)} (H : f.Homotopy g) (A : System.{u, u} Y) (n : ℕ) :
    pushforwardHomologyMap f A n =
      (homotopyPullbackHomologyIso H A n).hom ≫ pushforwardHomologyMap g A n :=
  pushforwardHomologyMap_homotopy H A n

example (f : C(X, Y)) (g : C(Y, Z)) (A : System.{u, u} Z) (n : ℕ) :
    pushforwardHomologyMap (g.comp f) A n =
      coefficientHomologyMap (pullbackCompositionIso f g A).hom n ≫
        pushforwardHomologyMap f (pullback g A) n ≫ pushforwardHomologyMap g A n :=
  pushforwardHomologyMap_comp f g A n

example (e : X ≃ₕ Y) (A : System.{u, u} Y) (n : ℕ) :
    IsIso (pushforwardHomologyMap e.toFun A n) :=
  isIso_pushforwardHomologyMap_of_homotopyEquiv e A n

example (e : X ≃ₕ Y) (A : System.{u, u} Y) (n : ℕ) :
    (homologyIsoOfHomotopyEquiv e A n).hom = pushforwardHomologyMap e.toFun A n := by simp

end Spaces

section CompletedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

open GroupCompletion.Localization

example (s : C)
    (A : System.{max u v, max u v} (ClassifyingSpace (GroupCompletion.Localization C C)))
    (n : ℕ) :
    IsIso (pushforwardHomologyMap (classifyingSpaceMap (firstTranslation s)).hom A n) :=
  isIso_firstTranslation_localHomology s A n

example (s : C)
    (A : System.{max u v, max u v} (ClassifyingSpace (GroupCompletion.Localization C C)))
    (n : ℕ) :
    IsIso (pushforwardHomologyMap (classifyingSpaceMap (secondTranslation s)).hom A n) :=
  isIso_secondTranslation_localHomology s A n

end CompletedCategory
