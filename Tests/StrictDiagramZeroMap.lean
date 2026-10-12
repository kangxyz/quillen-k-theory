/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagramZeroMap

/-!
# Original reduced-zero and Bass null-endpoint consumers

These consumers retain the original pushout cylinder and output loop coordinate, and show
precisely the endpoint casts of a supplied whole Bass image. They do not assume or assert
that such an image has already been constructed, or that it agrees with the original seed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u v w
namespace Quillen.Tests.StrictDiagramZeroMap

/-- Expose the unchanged output loop of the actual strict-square construction. -/
def originalSquareLoop (S : Arrow (Arrow LoopPrespectrum.{w})) (n : ℕ)
    (γ : (strictSquareLoopedConeFunctor.obj S).space n) :
    Path ((mappingCone (StrictSquare.comparison S)).point n)
      ((mappingCone (StrictSquare.comparison S)).point n) := γ

/-- The original span map kills its whole basepoint cylinder without changing cylinder time. -/
theorem original_zero_span_cylinder {S T : Arrow (Arrow LoopPrespectrum.{w})} (a : S ⟶ T)
    (h00 : a.left.left = zeroHom S.left.left T.left.left)
    (h01 : a.left.right = zeroHom S.left.right T.left.right)
    (h10 : a.right.left = zeroHom S.right.left T.right.left)
    (n : ℕ) (s : unitInterval) (x : S.left.left.space n) :
    (StrictSquare.spanMap a).map n (HomotopyPushout.cylinder S.left.hom S.hom.left n (s, x)) =
      (StrictSquare.span T).point n := by
  rw [StrictSquare.spanMap_eq_zero a h00 h01 h10]
  rfl

/-- The unchanged looped cone square map is constant at each independent output loop time. -/
theorem original_zero_loop_coordinate {S T : Arrow (Arrow LoopPrespectrum.{w})} (a : S ⟶ T)
    (h00 : a.left.left = zeroHom S.left.left T.left.left)
    (h01 : a.left.right = zeroHom S.left.right T.left.right)
    (h10 : a.right.left = zeroHom S.right.left T.right.left)
    (h11 : a.right.right = zeroHom S.right.right T.right.right)
    (n : ℕ) (γ : (strictSquareLoopedConeFunctor.obj S).space n) (t : unitInterval) :
    originalSquareLoop T n ((strictSquareLoopedConeFunctor.map a).map n γ) t =
      (mappingCone (StrictSquare.comparison T)).point n := by
  rw [strictSquareLoopedConeFunctor_map_eq_zero a h00 h01 h10 h11]
  rfl

variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F G K : C ⥤ LoopPrespectrum.{w}} (i : F ⟶ G) (c : G ⟶ K) (X : C)

/-- Exactly the two endpoint equalities needed by a whole Bass image of an original null track. -/
def originalBassNullEndpoint
    (H : Homotopy (((strictDiagramFunctor Q).map (i ≫ c)).app X)
      (((strictDiagramFunctor Q).map (diagramZeroMap F K)).app X)) :
    Homotopy ((((strictDiagramFunctor Q).map i).app X) ≫
      (((strictDiagramFunctor Q).map c).app X))
      (zeroHom (((strictDiagramFunctor Q).obj F).obj X)
        (((strictDiagramFunctor Q).obj K).obj X)) :=
  H.cast (congrArg (fun η => η.app X) ((strictDiagramFunctor Q).map_comp i c))
    (strictDiagramFunctor_map_zero_app Q F K X)

/-- The endpoint casts preserve the entire original level track at identical time. -/
theorem original_bass_null_track
    (H : Homotopy (((strictDiagramFunctor Q).map (i ≫ c)).app X)
      (((strictDiagramFunctor Q).map (diagramZeroMap F K)).app X))
    (n : ℕ) (s : unitInterval) (x : (((strictDiagramFunctor Q).obj F).obj X).space n) :
    (originalBassNullEndpoint Q i c X H).level n (s, x) = H.level n (s, x) := rfl

/-- The final face is the actual target basepoint, with no zero-diagram object identification. -/
theorem original_bass_null_final
    (H : Homotopy (((strictDiagramFunctor Q).map (i ≫ c)).app X)
      (((strictDiagramFunctor Q).map (diagramZeroMap F K)).app X))
    (n : ℕ) (x : (((strictDiagramFunctor Q).obj F).obj X).space n) :
    (originalBassNullEndpoint Q i c X H).level n (1, x) =
      (((strictDiagramFunctor Q).obj K).obj X).point n :=
  (originalBassNullEndpoint Q i c X H).at_one n x

/-- Degree zero retains the original homotopy and independent parameter-loop coordinates. -/
theorem original_bass_zero_degree_track
    (H : Homotopy (((strictDiagramFunctor Q).map (i ≫ c)).app X)
      (((strictDiagramFunctor Q).map (diagramZeroMap F K)).app X))
    (s t : unitInterval) (x : (((strictDiagramFunctor Q).obj F).obj X).space 0) :
    originalSquareLoop (K.mapArrow.mapArrow.obj (Q.obj X)) 0
        ((originalBassNullEndpoint Q i c X H).level 0 (s, x)) t =
      originalSquareLoop (K.mapArrow.mapArrow.obj (Q.obj X)) 0 (H.level 0 (s, x)) t := rfl

end Quillen.Tests.StrictDiagramZeroMap
