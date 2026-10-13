/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.Topology.LocalCoefficients.TelescopeTranslationKernel
import Quillen.Topology.LocalCoefficients.RelativeHomology

/-! # Actual stage action naturality and finite kernel representatives -/

open CategoryTheory MonoidalCategory Quillen Quillen.LocalCoefficients
open Quillen.TranslationTelescope Quillen.GrothendieckTelescope
universe u v

example {C : Type u} [Category.{v} C] [MonoidalCategory C] (e P : C)
    (A : System.{max u v, max u v} (ClassifyingSpace (TranslationTelescope.Model e))) (d : ℕ)
    {n m : ℕ} (h : n ≤ m) :
    stageTranslationHomology e P A d n ≫
      stageHomologyTransition (TranslationTelescope.diagram e) h A d =
      stageHomologyTransition (TranslationTelescope.diagram e) h
        (pullback (classifyingSpaceMap (leftTranslation e P)).hom A) d ≫
          stageTranslationHomology e P A d m :=
  stageTranslationHomology_transition e P A d h

example {C : Type u} [Category.{v} C] [MonoidalCategory C] (e P : C)
    (A : System.{max u v, max u v} (ClassifyingSpace (TranslationTelescope.Model e))) (d : ℕ)
    (x : homology (pullback (classifyingSpaceMap (leftTranslation e P)).hom A) d)
    (hx : pushforwardHomologyMap (classifyingSpaceMap (leftTranslation e P)).hom A d x = 0) :
    ∃ (n : ℕ) (y : homology
      (pullback (classifyingSpaceMap (Grothendieck.ι (TranslationTelescope.diagram e) n)).hom
        (pullback (classifyingSpaceMap (leftTranslation e P)).hom A)) d),
      pushforwardHomologyMap
        (classifyingSpaceMap (Grothendieck.ι (TranslationTelescope.diagram e) n)).hom
        (pullback (classifyingSpaceMap (leftTranslation e P)).hom A) d y = x ∧
      stageTranslationHomology e P A d n y = 0 :=
  translation_kernel_exists_stage e P A d x hx
