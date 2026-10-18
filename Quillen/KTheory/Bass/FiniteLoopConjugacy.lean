/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.FiniteLoopWordSlide

/-! # Fixed loop-word conjugacy from one local square -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace Quillen.KTheory.Bass.FiniteLoopConjugacy
open FiniteLoopWords FiniteLoopWordSlide
variable {C : Type u} [Category.{v} C] {A B : C ⥤ LoopPrespectrum.{w}}

/-- A single actual square survives fixed finite looping with its complete target cast. -/
theorem loopInto_square (j : ℕ) (f : A ⟶ B ⋙ parameterLoopingFunctor)
    (p : A ⟶ A) (q : B ⟶ B)
    (h : f ≫ Functor.whiskerRight q parameterLoopingFunctor = p ≫ f) :
    loopInto j f ≫ loopMap (j + 1) q = loopMap j p ≫ loopInto j f := by
  induction j with
  | zero => exact h
  | succ j ih =>
    change Functor.whiskerRight (loopInto j f) parameterLoopingFunctor ≫
      Functor.whiskerRight (loopMap (j + 1) q) parameterLoopingFunctor = _
    rw [← Functor.whiskerRight_comp, ih, Functor.whiskerRight_comp]
    rfl

/-- Reversal and the prescribed successor word give the adjacent conjugacy from that square. -/
theorem loopInto_conjugacy (j : ℕ) (f : A ⟶ B ⋙ parameterLoopingFunctor)
    (p : A ⟶ A) (q b : B ⟶ B)
    (h : f ≫ Functor.whiskerRight q parameterLoopingFunctor = p ≫ f) :
    loopInto j f ≫ (reversalIso (j + 1) B).hom ≫ loopMap (j + 1) (q ≫ b) =
      ((reversalIso j A).hom ≫ loopMap j p) ≫
        (loopInto j f ≫ (cyclicIso j B).hom ≫ loopMap (j + 1) b) := by
  have hn : loopMap (j + 1) q ≫ (cyclicIso j B).hom =
      (cyclicIso j B).hom ≫ loopMap (j + 1) q := (cyclic j).hom.naturality q
  rw [loopMap_comp, ← Category.assoc (loopInto j f), loopInto_reversal]
  simp only [Category.assoc]
  rw [← Category.assoc (cyclicIso j B).hom, ← hn]
  simp only [Category.assoc]
  rw [← Category.assoc (loopInto j f), loopInto_square j f p q h]
  simp only [Category.assoc]

end Quillen.KTheory.Bass.FiniteLoopConjugacy
