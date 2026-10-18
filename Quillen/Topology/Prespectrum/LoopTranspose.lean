/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.ParameterLooping

/-!
# Double-loop transpose and finite parameter-loop diagrams

This independently reconstructed prototype packages the existing parameter transpose as a
prespectrum isomorphism. Structure time remains independent of both loop coordinates.
This adopted source is an independent reconstruction, not byte recovery of the historical prototype.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.LoopTranspose

/-- Swap the two loop coordinates while preserving the independent structure coordinate. -/
def transpose (E : LoopPrespectrum.{u}) :
    parameterLooping (parameterLooping E) ⟶ parameterLooping (parameterLooping E) where
  map n := doubleLoopTranspose (E.point n)
  map_point n := doubleLoopTranspose_refl (E.point n)
  comm n γ := by
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    apply Path.ext
    funext r
    rfl

/-- The actual transpose is involutive as a prespectrum morphism. -/
def iso (E : LoopPrespectrum.{u}) :
    parameterLooping (parameterLooping E) ≅ parameterLooping (parameterLooping E) where
  hom := transpose E
  inv := transpose E
  hom_inv_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro γ
    apply Path.ext
    funext s
    apply Path.ext
    funext t
    rfl
  inv_hom_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro γ
    apply Path.ext
    funext s
    apply Path.ext
    funext t
    rfl

/-- Both original loop values are retained, in the transposed order. -/
theorem transpose_apply (E : LoopPrespectrum.{u}) (n : ℕ)
    (γ : Path (Path.refl (E.point n)) (Path.refl (E.point n))) (s t : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((transpose E).map n γ) s) t = γ t s := rfl

/-- The transpose commutes with the double loop of every original prespectrum map. -/
theorem naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    parameterLoopingMap (parameterLoopingMap f) ≫ transpose F =
      transpose E ≫ parameterLoopingMap (parameterLoopingMap f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext s
  apply Path.ext
  funext t
  rfl

end Quillen.LoopPrespectrum.LoopTranspose

universe v w
namespace Quillen.LoopPrespectrum.FiniteParameterLooping
variable {C : Type u} [Category.{v} C]

/-- Actual parameter looping, with its original structure-coordinate transposes. -/
def loops : ℕ → LoopPrespectrum.{w} → LoopPrespectrum.{w}
  | 0, E => E
  | j + 1, E => parameterLooping (loops j E)

/-- Apply the original parameter-looping functor to a diagram finitely many times. -/
def loopDiagram : ℕ → (C ⥤ LoopPrespectrum.{w}) → (C ⥤ LoopPrespectrum.{w})
  | 0, F => F
  | j + 1, F => loopDiagram j F ⋙ parameterLoopingFunctor

/-- The diagram retains precisely the original finite parameter-loop object. -/
theorem loopDiagram_obj (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    (loopDiagram j F).obj X = loops j (F.obj X) := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg parameterLooping ih

/-- Moving one already applied loop through the finite loop count changes only association. -/
theorem loopDiagram_postcomp (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}) :
    loopDiagram i (F ⋙ parameterLoopingFunctor) = loopDiagram (i + 1) F := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (fun G => G ⋙ parameterLoopingFunctor) ih

end Quillen.LoopPrespectrum.FiniteParameterLooping
