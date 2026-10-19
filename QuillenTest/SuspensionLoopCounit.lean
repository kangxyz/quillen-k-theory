/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.FiniteConeUnit

/-!
# Evaluation counit regression

The original suspension cylinder and the spectrum structure parameter remain independent.
The entire fiber path is retained by the inverse. The finite Model consumer supplies actual
stability at every cone-loop stage with no added topology or connectivity hypotheses.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.FiniteParameterLooping
open Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass.FiniteConeTopology
open scoped Topology unitInterval
universe u v w
namespace QuillenTest.SuspensionLoopCounit

/-- Suspension time and spectrum structure time occur in their original distinct positions. -/
theorem independent_structure_time (E : Quillen.LoopPrespectrum.{u}) (n : ℕ)
    (s t : unitInterval) (γ : Path (E.point n) (E.point n)) :
    E.structureMap n
      ((suspensionLoopCounit E).map n
        (Quillen.ReducedMappingCone.cylinder ((parameterLooping E).point n)
          (pointPrespectrum.point n) ((zeroHom (parameterLooping E) pointPrespectrum).map n)
            (s, γ))) t =
      Path.toContinuousMap ((parameterLooping E).structureMap n γ t) s := rfl

/-- The inverse recovers every time of the original fiber path. -/
theorem whole_fiber_path (E : Quillen.LoopPrespectrum.{u}) (n : ℕ)
    (z : (homotopyFiber (zeroHom pointPrespectrum E)).space n) (s : unitInterval) :
    Path.toContinuousMap ((pointFiberIso E).inv.map n z) s = z.1.2 s := rfl

/-- At the actual finite Model stages, the forward looped counit needs no extra premises. -/
theorem finite_model_forward {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ Model.{w}) (X : C) (i j : ℕ) :
    IsStableEquivalence (parameterLoopingMap
      (suspensionLoopCounit
        (loops j ((Quillen.KTheory.Bass.FiniteConeTopology.iterate Q i
          (F ⋙ prespectrumFunctor)).obj X)))) :=
  modelLoopsIterate_parameterLoopingCounit_isStableEquivalence Q i j F X

/-- The triangle leaves an additional external loop coordinate untouched. -/
theorem triangle_independent_loop (E : Quillen.LoopPrespectrum.{u}) (n : ℕ)
    (γ : Path (Path.refl (E.point n)) (Path.refl (E.point n))) (s t : unitInterval) :
    Path.toContinuousMap ((parameterLoopingMap (suspensionLoopCounit E)).map n
      ((suspensionLoopUnit (parameterLooping E)).map n (γ t))) s = γ t s := rfl

/-- The literal forward unit is stable at every actual parameter-looped finite cone stage. -/
theorem finite_model_unit {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ Model.{w}) (X : C) (i j : ℕ) :
    IsStableEquivalence (suspensionLoopUnit (parameterLooping
      (loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)))) :=
  modelLoopsIterate_suspensionLoopUnit_isStableEquivalence Q i j F X

end QuillenTest.SuspensionLoopCounit
