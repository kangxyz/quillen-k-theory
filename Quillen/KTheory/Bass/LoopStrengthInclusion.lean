/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.LoopStable
public import Quillen.Topology.Prespectrum.LoopTransposeStableSign

/-!
# Original Laurent inclusions through the Bass loop strength

The actual cone-loop comparison preserves the complete original target inclusion.
The actual Bass strength therefore preserves its looped inclusion with the final
double-loop transpose still present. On signed stable groups this is a minus sign.
These statements use no excision or connectivity assumption.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen.LoopPrespectrum

universe u v w

namespace Quillen.KTheory.Bass.LoopFactor

/-- The original cone-loop comparison preserves the whole target loop, with its original time. -/
theorem coneStrength_inclusion (S : Arrow (Arrow LoopPrespectrum.{w})) :
    mappingConeInclusion (StrictSquare.comparison (loopSquare S)) ≫ coneStrength S =
      parameterLoopingMap (mappingConeInclusion (StrictSquare.comparison S)) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext t
  rfl

variable {C : Type u} [Category.{v} C]

/-- The actual strength retains the final transpose on the entire original Laurent inclusion. -/
theorem strength_inclusion (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    parameterLoopingMap (mappingConeInclusion (StrictSquare.comparison
        (loopSquare (F.mapArrow.mapArrow.obj (Q.obj X))))) ≫ LoopStrength.strength Q F X =
      parameterLoopingMap (parameterLoopingMap (mappingConeInclusion
        (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))) ≫
      LoopTranspose.transpose
        (mappingCone (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))) := by
  rw [LoopStable.strength_factor, ← Category.assoc]
  have h := congrArg parameterLoopingFunctor.map
    (coneStrength_inclusion (F.mapArrow.mapArrow.obj (Q.obj X)))
  simp only [CategoryTheory.Functor.map_comp] at h
  exact congrArg (fun k => k ≫ LoopTranspose.transpose _) h

private theorem comp_neg_id {D : Type*} [Category D] [Preadditive D]
    {X Y : D} (f : X ⟶ Y) : f ≫ (-𝟙 Y) = -f := by
  rw [Preadditive.comp_neg, Category.comp_id]

/-- Signed stable Laurent representatives see the original transpose sign in the strength. -/
theorem strength_inclusion_stable (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) (d : ℤ) :
    (stableHomotopyFunctor d).map (parameterLoopingMap (mappingConeInclusion
        (StrictSquare.comparison (loopSquare (F.mapArrow.mapArrow.obj (Q.obj X)))))) ≫
      (stableHomotopyFunctor d).map (LoopStrength.strength Q F X) =
    -((stableHomotopyFunctor d).map (parameterLoopingMap (parameterLoopingMap
      (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))))) := by
  rw [← CategoryTheory.Functor.map_comp, strength_inclusion,
    CategoryTheory.Functor.map_comp, LoopTranspose.stableHomotopyFunctor_map_transpose]
  exact comp_neg_id _

end Quillen.KTheory.Bass.LoopFactor
