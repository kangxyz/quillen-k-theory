/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.Topology.LocalCoefficients.TelescopeShift
/-! # Regression tests for the original precompletion shift maps -/

open CategoryTheory MonoidalCategory
universe u v

example {C : Type u} [Category.{v} C] (T : C ⥤ C) (n : ℕ) :
    Grothendieck.ι (Quillen.EndofunctorTelescope.diagram T) n ⋙
        Quillen.EndofunctorTelescope.shift T =
      Grothendieck.ι (Quillen.EndofunctorTelescope.diagram T) (n + 1) :=
  Quillen.EndofunctorTelescope.inclusion_shift T n

example {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)
    (x y : Quillen.ClassifyingSpace (Quillen.TranslationTelescope.Model e)) :
    Joined (Quillen.classifyingSpaceMap (Quillen.TranslationTelescope.rightStabilization e) x)
      (Quillen.classifyingSpaceMap (Quillen.TranslationTelescope.rightStabilization e) y) ↔
        Joined x y :=
  Quillen.TranslationTelescope.rightStabilization_joined_iff e x y

example {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)
    (A : Quillen.LocalCoefficients.System.{max u v, max u v}
      (Quillen.ClassifyingSpace (Quillen.TranslationTelescope.Model e))) (n : ℕ) :
    IsIso (Quillen.LocalCoefficients.pushforwardHomologyMap
      (Quillen.classifyingSpaceMap (Quillen.TranslationTelescope.rightStabilization e)).hom A n) :=
  Quillen.TranslationTelescope.rightStabilization_localHomology_isIso e A n
