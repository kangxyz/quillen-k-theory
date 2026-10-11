/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagramIteration

/-!
# Original seed transitions under the actual successor identification

The right-iteration equality transports the same single seed and every actual iterated image.
Its naturality proves compatibility between the original successor tower and the tower obtained
by applying Bass, including the exact equality-induced endpoint transports.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F : C ⥤ LoopPrespectrum.{w}} (η : F ⟶ (strictDiagramFunctor Q).obj F)

/-- The actual original successor transitions respect the genuine right-iteration transports. -/
theorem strictDiagramTransition_succ_right (i : ℕ) :
    strictDiagramTransition Q η (i + 1) ≫
        eqToHom (congrArg (fun H : (C ⥤ LoopPrespectrum.{w}) ⥤ (C ⥤ LoopPrespectrum.{w}) =>
          H.obj F) (strictDiagramIterate_succ_right Q (i + 1))) =
      eqToHom (congrArg (fun H : (C ⥤ LoopPrespectrum.{w}) ⥤ (C ⥤ LoopPrespectrum.{w}) =>
        H.obj F) (strictDiagramIterate_succ_right Q i)) ≫
        (strictDiagramFunctor Q).map (strictDiagramTransition Q η i) := by
  have h := (eqToHom (strictDiagramIterate_succ_right.{u, v, w} Q i)).naturality η
  simp only [eqToHom_app, Functor.comp_map] at h
  exact h

end Quillen.KTheory.Bass
