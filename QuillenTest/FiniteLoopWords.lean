/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.FiniteLoopStrengthWords
public import Quillen.Topology.Prespectrum.LoopTranspose

/-!
# Finite loop-word regressions

Three actual loop times verify the direction of the fixed cyclic and reversal words.
The Bass regression retains an additional independent original Bass time for every finite
loop count and every original input. No cone permutation or geometric action is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open Quillen.KTheory.Bass Quillen.KTheory.Bass.FiniteConeStrength
open Quillen.LoopPrespectrum.FiniteLoopWords
open Quillen.KTheory.Bass.IteratedLoopStrength
open Quillen.KTheory.Bass.FiniteLoopStrengthWords
open scoped Topology unitInterval
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u v w
variable {C : Type u} [Category.{v} C]

example (F : C ⥤ Quillen.LoopPrespectrum.{w}) (X : C) (n : ℕ)
    (z : ((loopDiagram 3 F).obj X).space n) (r s t : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      (((cyclicIso 2 F).hom.app X).map n z) r) s) t =
      Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap z s) t) r := by
  change evaluate 3 F X n (((cyclicIso 2 F).hom.app X).map n z) ![r, s, t] = _
  rw [cyclicIso_evaluate]
  rfl

example (F : C ⥤ Quillen.LoopPrespectrum.{w}) (X : C) (n : ℕ)
    (z : ((loopDiagram 3 F).obj X).space n) (r s t : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      (((reversalIso 3 F).hom.app X).map n z) r) s) t =
      Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap z t) s) r := by
  change evaluate 3 F X n (((reversalIso 3 F).hom.app X).map n z) ![r, s, t] = _
  rw [reversalIso_evaluate]
  rfl

example (Q : C ⥤ Arrow (Arrow C)) (j : ℕ) (F : C ⥤ Quillen.LoopPrespectrum.{w})
    (X : C) (n : ℕ)
    (z : (((strictDiagramFunctor Q).obj (loopDiagram j F)).obj X).space n)
    (t : Fin j → unitInterval) (u : unitInterval) :
    Path.toContinuousMap (evaluate j ((strictDiagramFunctor Q).obj F) X n
      (((iteratedStrength Q j F).app X).map n
        ((((strictDiagramFunctor Q).map (reversalIso j F).hom).app X).map n z)) t) u =
      Path.toContinuousMap (evaluate j ((strictDiagramFunctor Q).obj F) X n
        (((iteratedStrength Q j F).app X).map n z) (t ∘ Fin.rev)) u := by
  have h := congrArg (fun a => evaluate j ((strictDiagramFunctor Q).obj F) X n
    ((a.app X).map n z) t) (iteratedStrength_reversal Q j F)
  change evaluate j ((strictDiagramFunctor Q).obj F) X n
      (((iteratedStrength Q j F).app X).map n
        ((((strictDiagramFunctor Q).map (reversalIso j F).hom).app X).map n z)) t =
    evaluate j ((strictDiagramFunctor Q).obj F) X n
      (((reversalIso j ((strictDiagramFunctor Q).obj F)).hom.app X).map n
        (((iteratedStrength Q j F).app X).map n z)) t at h
  rw [reversalIso_evaluate] at h
  exact congrArg (fun γ => Path.toContinuousMap γ u) h

#print axioms Quillen.LoopPrespectrum.FiniteLoopWords.cyclic
#print axioms Quillen.LoopPrespectrum.FiniteLoopWords.reversal
#print axioms Quillen.KTheory.Bass.FiniteLoopStrengthWords.iteratedStrength_evaluation
#print axioms Quillen.KTheory.Bass.FiniteLoopStrengthWords.iteratedStrength_reversal
#print axioms Quillen.KTheory.Bass.FiniteLoopStrengthWords.iteratedStrength_cyclic
