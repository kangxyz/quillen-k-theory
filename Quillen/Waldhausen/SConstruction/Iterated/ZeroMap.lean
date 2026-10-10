/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.SConstruction.Iterated.ExactCoherence
public import Quillen.Topology.Prespectrum.HomotopyLoop

/-! Literal zero maps and their canonical normalization homotopy for the actual S-prespectrum. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS

/-- The actual constant-zero model functor gives the literal zero prespectrum map. -/
theorem prespectrumMap_zeroHom (V W : Model.{u}) :
    prespectrumMap (zeroHom V W) = LoopPrespectrum.zeroHom (prespectrum V) (prespectrum W) := by
  apply LoopPrespectrum.Hom.ext
  funext n
  cases n with
  | zero =>
    apply ContinuousMap.ext
    intro γ
    change Path (stagePoint 0 V) (stagePoint 0 V) at γ
    apply Path.ext
    funext t
    change SSet.toTop.map ((stages 0).map (zeroHom V W)) (γ t) = stagePoint 0 W
    rw [stages_map_zeroHom]
    exact realization_const_apply _ _
  | succ n =>
    apply ContinuousMap.ext
    intro x
    change SSet.toTop.map ((stages n).map (zeroHom V W)) x = stagePoint n W
    rw [stages_map_zeroHom]
    exact realization_const_apply _ _

section Original
universe v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D)

theorem modelMap_zeroFunctor :
    modelMap W V (zeroFunctor_isExact W V) rfl = zeroHom (modelOf W) (modelOf V) := by
  apply Model.Hom.ext
  rfl

/-- Original zero-preserving constant functors are actual zero spectrum maps. -/
theorem originalPrespectrumMap_zeroFunctor :
    originalPrespectrumMap W V (zeroFunctor_isExact W V) rfl =
      LoopPrespectrum.zeroHom (originalPrespectrum W) (originalPrespectrum V) := by
  change prespectrumMap (modelMap W V (zeroFunctor_isExact W V) rfl) = _
  rw [modelMap_zeroFunctor, prespectrumMap_zeroHom]
  rfl

/-- Canonical normalization of the zero functor has a specified whole based
homotopy to the actual zero prespectrum map. -/
def exactOriginalPrespectrumMapZeroFunctorHomotopy :
    LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W V (zeroFunctor_isExact W V))
      (LoopPrespectrum.zeroHom (originalPrespectrum W) (originalPrespectrum V)) := by
  let h := zeroFunctor_isExact W V
  let e := (Quillen.rebaseFunctorIso (zeroFunctor V) W.zero V.zero
    ((h.zero W.isZero).iso V.isZero)).symm
  have H := originalPrespectrumTransformationHomotopy W V h.rebase h
    (Quillen.rebaseFunctor_obj_base _ _ _ _) rfl e.hom (fun _ ↦ V.weq_iso _ inferInstance)
  simpa only [exactOriginalPrespectrumMap, originalPrespectrumMap_zeroFunctor] using H

end Original
end Quillen.Waldhausen.IteratedS
