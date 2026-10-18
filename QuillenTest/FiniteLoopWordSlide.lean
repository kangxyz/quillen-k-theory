/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.FiniteLoopWordSlide
public import Quillen.Topology.Prespectrum.LoopTranspose

/-!
# The arbitrary-map loop-slide time regression

Two pre-existing loop times and the new time produced by an arbitrary diagram map are
retained. The original whole-functor equality transport occurs in the tested expression.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.FiniteLoopWords
open Quillen.LoopPrespectrum.FiniteLoopWordSlide
open scoped Topology unitInterval
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u v w
variable {C : Type u} [Category.{v} C]

example {A B : C ⥤ Quillen.LoopPrespectrum.{w}}
    (f : A ⟶ B ⋙ parameterLoopingFunctor) (X : C) (n : ℕ)
    (z : ((loopDiagram 2 A).obj X).space n) (r s t : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((((loopMap 2 f ≫ eqToHom (loopDiagram_postcomp 2 B)) ≫
        (reversalIso 3 B).hom).app X).map n z) r) s) t =
      Path.toContinuousMap ((f.app X).map n
        (Path.toContinuousMap (Path.toContinuousMap z t) s)) r := by
  rw [← loopInto_eq]
  change evaluate 3 B X n (((reversalIso 3 B).hom.app X).map n
    (((loopInto 2 f).app X).map n z)) ![r, s, t] = _
  rw [reversalIso_evaluate, loopInto_evaluate]
  rfl

#print axioms Quillen.LoopPrespectrum.FiniteLoopWordSlide.loopInto_eq
#print axioms Quillen.LoopPrespectrum.FiniteLoopWordSlide.loopMap_reversal
