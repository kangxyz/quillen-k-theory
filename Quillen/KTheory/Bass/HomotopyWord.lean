/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictDiagramHomotopy
public import Quillen.Topology.Prespectrum.NullLoopNaturality

/-!
# Bass preserves the original whole homotopy words

The literal natural time slices show preservation of reversal and the original
half-clock concatenation. These finite formulas are used for the original
source-null/unit/source-null word, without adding a coherence hypothesis.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open scoped unitInterval
universe u v w
namespace Quillen.KTheory.Bass.HomotopyWord
variable {C : Type u} [Category.{v} C]
  {F G : C ⥤ LoopPrespectrum.{w}} {a b c : F ⟶ G}

/-- Same-time naturality of the supplied actual family. -/
abbrev Natural (H : ∀ X, Homotopy (a.app X) (b.app X)) : Prop :=
  ∀ {X Y} (f : X ⟶ Y) n r x,
    (G.map f).map n ((H X).level n (r, x)) =
      (H Y).level n (r, (F.map f).map n x)

/-- Reversal keeps the original naturality equation at reversed time. -/
theorem natural_symm (H : ∀ X, Homotopy (a.app X) (b.app X)) (hH : Natural H) :
    Natural (fun X => (H X).symm) := fun f n r x => hH f n (unitInterval.symm r) x

/-- The original half-clock concatenation preserves same-time naturality. -/
theorem natural_trans (H : ∀ X, Homotopy (a.app X) (b.app X))
    (K : ∀ X, Homotopy (b.app X) (c.app X)) (hH : Natural H) (hK : Natural K) :
    Natural (fun X => (H X).trans (K X)) := by
  intro X Y f n r x
  change (G.map f).map n (((H X).levelHomotopy n).trans ((K X).levelHomotopy n) (r,x)) =
    ((H Y).levelHomotopy n).trans ((K Y).levelHomotopy n) (r, (F.map f).map n x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hH f n _ x
  · exact hK f n _ x

/-- Original postcomposition preserves the naturality of the whole family. -/
theorem natural_postcomp {D : C ⥤ LoopPrespectrum.{w}}
    (H : ∀ X, Homotopy (a.app X) (b.app X)) (hH : Natural H) (j : G ⟶ D) :
    Natural (a := a ≫ j) (b := b ≫ j) (fun X => (H X).postcomp (j.app X)) := by
  intro X Y f n r x
  change ((j.app X) ≫ D.map f).map n ((H X).level n (r,x)) =
    (j.app Y).map n ((H Y).level n (r, (F.map f).map n x))
  rw [← j.naturality]
  exact congrArg ((j.app Y).map n) (hH f n r x)

/-- Bass preserves reversal of the entire natural homotopy, including all structure values. -/
theorem map_symm (H : ∀ X, Homotopy (a.app X) (b.app X)) (hH : Natural H)
    (Q : C ⥤ Arrow (Arrow C)) (X : C) :
    strictDiagramMapHomotopy (fun Y => (H Y).symm) (natural_symm H hH) Q X =
      (strictDiagramMapHomotopy H hH Q X).symm := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨r,x⟩
  change ((strictDiagramMapHomotopy _ _ Q X).at r).map n x =
    ((strictDiagramMapHomotopy H hH Q X).at (unitInterval.symm r)).map n x
  rw [strictDiagramMapHomotopy_at, strictDiagramMapHomotopy_at]
  rfl

/-- Bass preserves the original half-clock concatenation literally. -/
theorem map_trans (H : ∀ X, Homotopy (a.app X) (b.app X))
    (K : ∀ X, Homotopy (b.app X) (c.app X)) (hH : Natural H) (hK : Natural K)
    (Q : C ⥤ Arrow (Arrow C)) (X : C) :
    strictDiagramMapHomotopy (fun Y => (H Y).trans (K Y))
        (natural_trans H K hH hK) Q X =
      (strictDiagramMapHomotopy H hH Q X).trans (strictDiagramMapHomotopy K hK Q X) := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨r,x⟩
  change ((strictDiagramMapHomotopy _ _ Q X).at r).map n x =
    ((strictDiagramMapHomotopy H hH Q X).levelHomotopy n).trans
      ((strictDiagramMapHomotopy K hK Q X).levelHomotopy n) (r,x)
  rw [strictDiagramMapHomotopy_at, ContinuousMap.HomotopyRel.trans_apply]
  split
  · rename_i hr
    change _ = ((strictDiagramMapHomotopy H hH Q X).at _).map n x
    rw [strictDiagramMapHomotopy_at]
    apply congrArg (fun η => (((strictDiagramFunctor Q).map η).app X).map n x)
    apply NatTrans.ext
    funext Y
    apply Hom.ext
    funext m
    apply ContinuousMap.ext
    intro y
    change ((H Y).levelHomotopy m).trans ((K Y).levelHomotopy m) (r,y) = _
    rw [ContinuousMap.HomotopyRel.trans_apply]
    simp only [hr, dite_true]
    rfl
  · rename_i hr
    change _ = ((strictDiagramMapHomotopy K hK Q X).at _).map n x
    rw [strictDiagramMapHomotopy_at]
    apply congrArg (fun η => (((strictDiagramFunctor Q).map η).app X).map n x)
    apply NatTrans.ext
    funext Y
    apply Hom.ext
    funext m
    apply ContinuousMap.ext
    intro y
    change ((H Y).levelHomotopy m).trans ((K Y).levelHomotopy m) (r,y) = _
    rw [ContinuousMap.HomotopyRel.trans_apply]
    simp only [hr, dite_false]
    rfl

/-- Original postcomposition becomes Bass postcomposition at every identical time. -/
theorem map_postcomp {D : C ⥤ LoopPrespectrum.{w}}
    (H : ∀ X, Homotopy (a.app X) (b.app X)) (hH : Natural H) (j : G ⟶ D)
    (Q : C ⥤ Arrow (Arrow C)) (X : C) (n : ℕ) :
    (strictDiagramMapHomotopy (η := a ≫ j) (θ := b ≫ j)
      (fun Y => (H Y).postcomp (j.app Y))
      (natural_postcomp H hH j) Q X).level n =
    ((strictDiagramMapHomotopy H hH Q X).postcomp
      (((strictDiagramFunctor Q).map j).app X)).level n := by
  apply ContinuousMap.ext
  rintro ⟨r,x⟩
  change ((strictDiagramMapHomotopy _ _ Q X).at r).map n x =
    ((strictDiagramMapHomotopy H hH Q X).at r ≫
      (((strictDiagramFunctor Q).map j).app X)).map n x
  rw [strictDiagramMapHomotopy_at, strictDiagramMapHomotopy_at]
  exact congrArg (fun k => (k.app X).map n x)
    ((strictDiagramFunctor Q).map_comp (diagramHomotopyAt H hH r) j)

end Quillen.KTheory.Bass.HomotopyWord
