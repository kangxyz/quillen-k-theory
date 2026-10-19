/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.NormalizedStageMap
public import Quillen.KTheory.Bass.LoopStrengthInclusion

/-!
# The first two actual normalization maps

The first normalization is identity. The second is precisely the original
Bass loop strength on the first unlooped cone, with the original whole-functor
endpoint identifications retained. This identifies the additional transpose
that must be preserved when comparing original second-bottom representatives.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.FiniteParameterLooping

universe u v w

namespace Quillen.KTheory.Bass.NormalizedStageMap

open IteratedLoopStrength FiniteConeTopology

variable {C : Type u} [Category.{v} C]

/-- The entire first normalization map is the original identity map. -/
theorem stageMap_one (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w}) :
    stageMap Q 1 F = 𝟙 ((strictDiagramFunctor Q).obj F) := by
  simp only [stageMap, strictDiagramIterate, Functor.comp_obj, Functor.id_obj, normalized,
    iterate, loopDiagram, iteratedStrength, eqToHom_refl, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- The second normalization keeps the original strength between its two complete casts. -/
theorem stageMap_two (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w}) :
    stageMap Q 2 F = eqToHom (bass_succ_eq Q 1 F) ≫
      strengthDiagram Q (iterate Q 1 F) ≫ eqToHom (normalized_succ_eq Q 1 F) := by
  simp only [stageMap, strictDiagramIterate, Functor.comp_obj, Functor.id_obj, normalized,
    iterate, loopDiagram, iteratedStrength, eqToHom_refl, CategoryTheory.Functor.map_id,
    Functor.whiskerRight_id', Category.id_comp, Category.comp_id]

/-- At each actual parameter object, the second normalization is the original cone strength. -/
theorem stageMap_two_app (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    (stageMap Q 2 F).app X = LoopStrength.strength Q (ConeTrack.diagram Q F) X := by
  have h := congrArg (fun η => η.app X) (stageMap_two Q F)
  simpa only [NatTrans.comp_app, eqToHom_app, eqToHom_refl, Category.id_comp,
    Category.comp_id, strengthDiagram, iterate] using h

end Quillen.KTheory.Bass.NormalizedStageMap
