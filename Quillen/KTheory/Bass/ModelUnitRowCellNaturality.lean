/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelUnitRowCell
public import Quillen.Waldhausen.SConstruction.Iterated.RowLoopFunctor

/-! # Whole index naturality of the independent initial Model-unit cell

The actual row map of the original exact Model morphism preserves the complete cell at the
same transformation time. Its row coordinate and degree-zero input-loop coordinate are unchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.FunctorIdentityAutomorphism
open scoped Topology unitInterval
universe u v w
namespace Quillen.KTheory.Bass.ModelDiagramRowInterchange
open NaturalTrack
variable {C : Type u} [Category.{v} C] (L : C ⥤ C) (c : 𝟭 C ⟶ L)
  (F : C ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)) ≅ 𝟭 (F.obj (L.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (F.map (L.map g)).functor (unit X) (unit Y))

include hunit in
/-- Genuine exact row transport preserves every original cell level and transformation time. -/
theorem initialCell_naturality {X Y : C} (g : X ⟶ Y) (n : ℕ) (t : unitInterval)
    (x : (prespectrum (F.obj X)).space n) :
    (rowLoopMap (F.map (L.map g))).map n ((initialCell L c F unit X).level n (t, x)) =
      (initialCell L c F unit Y).level n (t, (prespectrumMap (F.map g)).map n x) := by
  let A := ofModelUnits L c F unit hunit
  change (rowLoopMap (F.map (L.map g))).map n
      ((rowStabilizationMap (F.obj (L.obj X))).map n ((A.homotopy X).level n (t, x))) =
    (rowStabilizationMap (F.obj (L.obj Y))).map n
      ((A.homotopy Y).level n (t, (prespectrumMap (F.map g)).map n x))
  have hr := congrArg (fun f => f.map n ((A.homotopy X).level n (t, x)))
    (rowStabilizationMap_naturality (F.map (L.map g))).symm
  change (rowLoopMap (F.map (L.map g))).map n
      ((rowStabilizationMap (F.obj (L.obj X))).map n ((A.homotopy X).level n (t, x))) =
    (rowStabilizationMap (F.obj (L.obj Y))).map n
      ((prespectrumMap (F.map (L.map g))).map n ((A.homotopy X).level n (t, x))) at hr
  exact hr.trans (congrArg ((rowStabilizationMap (F.obj (L.obj Y))).map n)
    (A.naturality g n t x))

end Quillen.KTheory.Bass.ModelDiagramRowInterchange
