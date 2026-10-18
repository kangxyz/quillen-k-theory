/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.GeometricConeFixedWords

/-!
# Fixed-word and actual-cone regressions

The generic three-letter word is natural without any relation on the supplied local
isomorphism. The actual geometric specialization retains the same two-cone map with
the explicit finite-iterate equality transports retained. No permutation-group law is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor.FixedWords
open Quillen.KTheory.Bass.GeometricConeInterchange
open Quillen.KTheory.Bass.GeometricConeFixedWords
universe u v w

example {D : Type u} [Category.{v} D] (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F)
    {X Y : D} (f : X ⟶ Y) :
    F.map (F.map (F.map f)) ≫
      (F.map (P.hom.app Y) ≫ P.hom.app (F.obj Y) ≫ F.map (P.hom.app Y)) =
    (F.map (P.hom.app X) ≫ P.hom.app (F.obj X) ≫ F.map (P.hom.app X)) ≫
      F.map (F.map (F.map f)) := by
  have h := (fixedWord F P 3).hom.naturality f
  rw [fixedWord_three_hom_app, fixedWord_three_hom_app] at h
  exact h

example (F : Scheme.{u}ᵒᵖ ⥤ Quillen.LoopPrespectrum.{w}) :
    wordAt 2 F =
      (eqToIso (power_obj 2 F)).symm ≪≫ permutationNatIso F ≪≫
        eqToIso (power_obj 2 F) := by
  unfold wordAt
  rw [word_two]
  rfl

#print axioms CategoryTheory.Functor.FixedWords.beta
#print axioms CategoryTheory.Functor.FixedWords.fixedWord_three
#print axioms Quillen.KTheory.Bass.GeometricConeFixedWords.power_obj
#print axioms Quillen.KTheory.Bass.GeometricConeFixedWords.wordAt
#print axioms Quillen.KTheory.Bass.GeometricConeFixedWords.word_three_hom_app
