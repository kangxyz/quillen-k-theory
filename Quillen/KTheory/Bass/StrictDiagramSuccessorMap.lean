/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagramSuccessor

/-!
# Natural successor maps for the original strict Bass iteration

The successor map is precisely the equality-induced map from the original right-iteration
identity. It is natural in every strict diagram arrow and intertwines the original transitions.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- The actual right-successor equality, evaluated on the original diagram. -/
def strictDiagramSuccessorMap (F : C ⥤ LoopPrespectrum.{w}) (i : ℕ) :
    (strictDiagramIterate Q (i + 1)).obj F ⟶
      (strictDiagramFunctor Q).obj ((strictDiagramIterate Q i).obj F) :=
  eqToHom (congrArg (fun H ↦ H.obj F) (strictDiagramIterate_succ_right Q i))

/-- The unchanged equality-induced successor arrow is an isomorphism. -/
instance strictDiagramSuccessorMap_isIso (F : C ⥤ LoopPrespectrum.{w}) (i : ℕ) :
    IsIso (strictDiagramSuccessorMap Q F i) := by
  unfold strictDiagramSuccessorMap
  infer_instance

/-- The specified successor transport is natural in every original diagram arrow. -/
theorem strictDiagramSuccessorMap_naturality
    {F G : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G) (i : ℕ) :
    (strictDiagramIterate Q (i + 1)).map a ≫ strictDiagramSuccessorMap Q G i =
      strictDiagramSuccessorMap Q F i ≫
        (strictDiagramFunctor Q).map ((strictDiagramIterate Q i).map a) := by
  have h := (eqToHom (strictDiagramIterate_succ_right.{u, v, w} Q i)).naturality a
  simpa only [eqToHom_app, Functor.comp_map, strictDiagramSuccessorMap] using h

/-- The original successor transitions retain these exact equality-induced maps. -/
theorem strictDiagramSuccessorMap_transition
    {F : C ⥤ LoopPrespectrum.{w}} (η : F ⟶ (strictDiagramFunctor Q).obj F) (i : ℕ) :
    strictDiagramTransition Q η (i + 1) ≫ strictDiagramSuccessorMap Q F (i + 1) =
      strictDiagramSuccessorMap Q F i ≫
        (strictDiagramFunctor Q).map (strictDiagramTransition Q η i) :=
  strictDiagramTransition_succ_right Q η i

end Quillen.KTheory.Bass
