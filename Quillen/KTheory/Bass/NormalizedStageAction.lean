/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.NaturalTrack
public import Quillen.Topology.Prespectrum.LoopTranspose
public import Quillen.KTheory.Bass.NormalizedStageMap

/-! # The unchanged finite stage map intertwines the actual induced whole actions -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
open scoped unitInterval
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace Quillen.KTheory.Bass.NaturalTrack
open FiniteConeTopology FiniteConeStrength
open IteratedLoopStrength NormalizedStageMap
variable {C : Type u} [Category.{v} C] {L : C ⥤ C} {c : 𝟭 C ⟶ L}
    {F G : C ⥤ LoopPrespectrum.{w}}

/-- Fixed finite pointwise looping of the same natural track. -/
def Track.loops (A : Track L c F) : ∀ j, Track L c (loopDiagram j F)
  | 0 => A
  | j + 1 => (A.loops j).loop

/-- Complete-functor equality transport commutes with one original loop. -/
theorem Track.loop_cast (A : Track L c F) (h : F = G) :
    (A.cast h).loop = A.loop.cast (congrArg (fun D => D ⋙ parameterLoopingFunctor) h) := by
  subst G
  rfl

/-- The original named loop association equality retains the same whole track. -/
theorem Track.loops_postcomp (A : Track L c F) (i : ℕ) :
    (A.loop.loops i).cast (loopDiagram_postcomp i F) = A.loops (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change ((A.loop.loops i).loop).cast
      (congrArg (fun D => D ⋙ parameterLoopingFunctor) (loopDiagram_postcomp i F)) =
        (A.loops (i + 1)).loop
    exact ((A.loop.loops i).loop_cast (loopDiagram_postcomp i F)).symm.trans
      (congrArg (fun B => B.loop) ih)

variable (Q : C ⥤ Arrow (Arrow C))
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- Fixed finite original cone induction of the initial natural track. -/
def Track.cones (A : Track L c F) : ∀ i, Track L c (iterate Q i F)
  | 0 => A
  | i + 1 => (A.cones i).cone Q χ hχ

/-- The action on the original right-associated Bass stages, with the named source transport. -/
def Track.stages (A : Track L c F) :
    ∀ i, Track L c ((strictDiagramIterate Q i).obj F)
  | 0 => A
  | i + 1 => ((A.stages i).bass Q χ hχ).cast (bass_succ_eq Q i F).symm

/-- The normalized action retains exactly i original loops after i original cone actions. -/
def Track.normalized (A : Track L c F) (i : ℕ) : Track L c (normalized Q i F) :=
  (A.cones Q χ hχ i).loops i

/-- The named target equality in stageMap retains the normalized action. -/
theorem Track.normalized_successor_cast (A : Track L c F) (i : ℕ) :
    (((A.cones Q χ hχ i).bass Q χ hχ).loops i).cast (normalized_succ_eq Q i F) =
      A.normalized Q χ hχ (i + 1) :=
  (A.cones Q χ hχ (i + 1)).loops_postcomp i

/-- The original single strength preserves both induced actions at every track time. -/
theorem strength_equivariant (A : Track L c F) :
    Equivariant (A.loop.bass Q χ hχ) (A.bass Q χ hχ).loop (strengthDiagram Q F) := by
  intro X r
  exact LoopStrengthConeAction.strength_action Q L c χ hχ F
    A.homotopy A.naturality X r

/-- The fixed-order iterated strength preserves the corresponding whole original actions. -/
theorem iteratedStrength_equivariant (A : Track L c F) (j : ℕ) :
    Equivariant ((A.loops j).bass Q χ hχ) ((A.bass Q χ hχ).loops j)
      (iteratedStrength Q j F) := by
  induction j with
  | zero => exact Equivariant.id _
  | succ j ih => exact (strength_equivariant Q χ hχ (A.loops j)).comp ih.loop

/-- Every unchanged finite stageMap intertwines the actual whole induced actions. -/
theorem stageMap_equivariant (A : Track L c F) (i : ℕ) :
    Equivariant (A.stages Q χ hχ i) (A.normalized Q χ hχ i) (stageMap Q i F) := by
  induction i with
  | zero => exact Equivariant.id A
  | succ i ih =>
    have h := (Equivariant.cast_source ((A.stages Q χ hχ i).bass Q χ hχ)
      (bass_succ_eq Q i F)).comp
      ((ih.bass Q χ hχ).comp
        ((iteratedStrength_equivariant Q χ hχ (A.cones Q χ hχ i) i).comp
          (Equivariant.cast_target (((A.cones Q χ hχ i).bass Q χ hχ).loops i)
            (normalized_succ_eq Q i F))))
    rw [Track.normalized_successor_cast] at h
    exact h

end Quillen.KTheory.Bass.NaturalTrack
