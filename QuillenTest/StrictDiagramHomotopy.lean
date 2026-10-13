/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.StrictDiagramHomotopy

/-!
# Original whole Bass-action consumers

The consumers retain all four independent homotopy, cone, overlap and output-loop times,
as well as the original structure coordinate. The null family is constructed from an actual
coefficient-natural original null track; its final face uses the proved literal zero equality.
The constant-family consumer checks the unchanged original Bass map without a homotopy premise.
No original seed-relative pasting or geometric endpoint comparison is asserted here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u v w
namespace QuillenTest.StrictDiagramHomotopy

open Quillen

/-- Every original overlap/cone/loop coordinate survives the actual moving square map. -/
theorem original_four_times {S T : Arrow (Arrow LoopPrespectrum.{w})} {a b : S ⟶ T}
    (L : StrictSquare.MapHomotopy a b) (n : ℕ) (r s q t : unitInterval)
    (x : S.left.left.space n)
    (γ : Path ((mappingCone (StrictSquare.comparison S)).point n)
      ((mappingCone (StrictSquare.comparison S)).point n))
    (hγ : γ t = ReducedMappingCone.cylinder ((StrictSquare.span S).point n)
      (S.right.right.point n) ((StrictSquare.comparison S).map n)
        (s, HomotopyPushout.cylinder S.left.hom S.hom.left n (q, x))) :
    Path.toContinuousMap (L.looped.level n (r, γ)) t =
      ReducedMappingCone.cylinder ((StrictSquare.span T).point n) (T.right.right.point n)
        ((StrictSquare.comparison T).map n)
        (s, HomotopyPushout.cylinder T.left.hom T.hom.left n (q, L.source.level n (r, x))) := by
  rw [L.looped_apply, hγ, L.cone_cylinder, L.span_cylinder]

/-- The actual Laurent target face uses the original final-corner whole track. -/
theorem original_laurent_face {S T : Arrow (Arrow LoopPrespectrum.{w})} {a b : S ⟶ T}
    (L : StrictSquare.MapHomotopy a b) (n : ℕ) (r : unitInterval) (y : S.right.right.space n) :
    L.cone.level n (r, (mappingConeInclusion (StrictSquare.comparison S)).map n y) =
      (mappingConeInclusion (StrictSquare.comparison T)).map n (L.target.level n (r, y)) :=
  L.cone_inclusion n r y

variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F G : C ⥤ LoopPrespectrum.{w}} {η θ : F ⟶ G}
    (H : ∀ X, Homotopy (η.app X) (θ.app X))
    (hH : ∀ {X Y} (f : X ⟶ Y) n r x,
      (G.map f).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map f).map n x))

/-- All actual coefficient maps commute with the same full Bass time slice. -/
theorem original_coefficient_time {X Y : C} (f : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F).obj X).space n) :
    (((strictDiagramFunctor Q).obj G).map f).map n
        ((strictDiagramMapHomotopy H hH Q X).level n (r, x)) =
      (strictDiagramMapHomotopy H hH Q Y).level n
        (r, (((strictDiagramFunctor Q).obj F).map f).map n x) :=
  strictDiagramMapHomotopy_naturality H hH Q f n r x

/-- The original structure time is independent of the whole Bass homotopy parameter. -/
theorem original_structure_time (X : C) (n : ℕ) (r t : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F).obj X).space n) :
    (strictDiagramMapHomotopy H hH Q X).level (n + 1)
        (r, (((strictDiagramFunctor Q).obj F).obj X).structureMap n x t) =
      (((strictDiagramFunctor Q).obj G).obj X).structureMap n
        ((strictDiagramMapHomotopy H hH Q X).level n (r, x)) t :=
  (strictDiagramMapHomotopy H hH Q X).comm n r x t

/-- Degree zero retains the independent original input and output-loop parameters. -/
theorem original_zero_degree_loop (X : C) (r t : unitInterval)
    (γ : Path
      ((mappingCone (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))).point 0)
      ((mappingCone (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))).point 0)) :
    Path.toContinuousMap ((strictDiagramMapHomotopy H hH Q X).level 0 (r, γ)) t =
      (diagramSquareMapHomotopy H hH (Q.obj X)).cone.level 0 (r, γ t) := rfl

/-- A literal constant family remains the unchanged original Bass map at every actual time. -/
theorem original_constant_bass_map (α : F ⟶ G) (X : C) (r : unitInterval) :
    (strictDiagramMapHomotopy (fun Y => Homotopy.refl (α.app Y))
      (fun f n _ x => congrArg (fun k => k.map n x) (α.naturality f).symm) Q X).at r =
      ((strictDiagramFunctor Q).map α).app X := by
  rw [strictDiagramMapHomotopy_at]
  have he : diagramHomotopyAt (fun Y => Homotopy.refl (α.app Y))
      (fun f n _ x => congrArg (fun k => k.map n x) (α.naturality f).symm) r = α := by
    apply NatTrans.ext
    funext Y
    apply Hom.ext
    funext n
    ext x
    rfl
  rw [he]

section Null
variable {K : C ⥤ LoopPrespectrum.{w}} (i : F ⟶ G) (c : G ⟶ K)
    (N : ∀ X, Homotopy ((i ≫ c).app X) ((diagramZeroMap F K).app X))
    (hN : ∀ {X Y} (f : X ⟶ Y) n r x,
      (K.map f).map n ((N X).level n (r, x)) =
        (N Y).level n (r, (F.map f).map n x))

/-- The constructed Bass null family starts at the two unchanged map-induced Bass arrows. -/
theorem original_null_initial (X : C) (n : ℕ)
    (x : (((strictDiagramFunctor Q).obj F).obj X).space n) :
    (strictDiagramNullHomotopy i c N hN Q X).level n (0, x) =
      (((strictDiagramFunctor Q).map c).app X).map n
        ((((strictDiagramFunctor Q).map i).app X).map n x) :=
  (strictDiagramNullHomotopy i c N hN Q X).at_zero n x

/-- The final endpoint is the literal original target point after the proved Bass-zero equality. -/
theorem original_null_final (X : C) (n : ℕ)
    (x : (((strictDiagramFunctor Q).obj F).obj X).space n) :
    (strictDiagramNullHomotopy i c N hN Q X).level n (1, x) =
      (((strictDiagramFunctor Q).obj K).obj X).point n :=
  (strictDiagramNullHomotopy i c N hN Q X).at_one n x

/-- Every original basepoint value remains fixed throughout the actual null family. -/
theorem original_null_point (X : C) (n : ℕ) (r : unitInterval) :
    (strictDiagramNullHomotopy i c N hN Q X).level n
        (r, (((strictDiagramFunctor Q).obj F).obj X).point n) =
      (((strictDiagramFunctor Q).obj K).obj X).point n :=
  (strictDiagramNullHomotopy i c N hN Q X).at_point n r

end Null
end QuillenTest.StrictDiagramHomotopy
