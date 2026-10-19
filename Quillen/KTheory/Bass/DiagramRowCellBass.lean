/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.DiagramRowCellConeComparison
public import Quillen.KTheory.Bass.DiagramBassRowStrength

/-! # Independent cone descent of a natural cell into a genuine row refinement

The input is a whole cross-diagram cell, not a Model structure on the later spectrum.
Its four actual corners descend through the original square cone, inverse geometric index,
and forward row strength. The source-null height remains independent of the cell time.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace Quillen.KTheory.Bass.DiagramRowCell
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)


variable
  (H : ∀ X, Homotopy ((input L c F q hp hn hs).app X)
    ((input L c F q hp hn hs).app X))
  (hH : ∀ {X Y} (g : X ⟶ Y) (n : ℕ) (t : unitInterval) (x : (F.obj X).space n),
    ((DiagramRowRefinement.diagram F q hp hn).map (L.map g)).map n
      ((H X).level n (t, x)) = (H Y).level n (t, (F.map g).map n x))

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)

/-- The actual inverse interchanges old looping with the computed distinguished row. -/
def loopRowInverse (X : C) :=
  RowRefinement.parameterLoopingInverse ((ConeTrack.diagram Q F).obj X)
    (DiagramRowInterchange.cone Q F q hp hn X)
    (DiagramRowInterchange.cone_point Q F q hp hn X)

/-- Loop the independent whole cone cell before comparing it with any scalar action. -/
def rawBass (X : C) :=
  ((cone L c F q hp hn hs H hH Q χ X).parameterLooping).postcomp
    (loopRowInverse F q hp hn Q (L.obj X))

/-- The original row comparison on the actual next Bass diagram. -/
def bassComparison :
    (strictDiagramFunctor Q).obj F ⟶
      DiagramRowRefinement.diagram ((strictDiagramFunctor Q).obj F)
        (DiagramRowInterchange.bass Q F q hp hn)
        (DiagramRowInterchange.bass_point Q F q hp hn)
        (DiagramRowInterchange.bass_naturality Q F q hp hn) :=
  DiagramRowRefinement.comparison ((strictDiagramFunctor Q).obj F)
    (DiagramRowInterchange.bass Q F q hp hn)
    (DiagramRowInterchange.bass_point Q F q hp hn)
    (DiagramRowInterchange.bass_naturality Q F q hp hn)
    (DiagramRowInterchange.bass_structure Q F q hp hn hs)

/-- The explicit loop/row map preserves the whole genuine comparison, also in degree zero. -/
theorem loopRow_comparison (X : C) :
    parameterLoopingMap (coneComparison F q hp hn hs Q X) ≫
        loopRowInverse F q hp hn Q X =
      (bassComparison F q hp hn hs Q).app X := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  cases n with
  | zero =>
    apply Path.ext; funext r
    apply Path.ext; funext s
    apply Path.ext; funext t
    rfl
  | succ k =>
    apply Path.ext; funext s
    apply Path.ext; funext t
    rfl

private theorem loopMap_comp {E E' E'' : LoopPrespectrum.{w}}
    (f : E ⟶ E') (g : E' ⟶ E'') :
    parameterLoopingMap (f ≫ g) = parameterLoopingMap f ≫ parameterLoopingMap g :=
  parameterLoopingFunctor.map_comp f g

variable (A : NaturalTrack.Track L c F)
  (hcell : ∀ X t, (H X).at t = (A.homotopy X).at t ≫
    (DiagramRowRefinement.comparison F q hp hn hs).app (L.obj X))
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

include hcell in
/-- The independently constructed next cell preserves the proved whole action comparison. -/
theorem rawBass_at_eq (X : C) (t : unitInterval) :
    (rawBass L c F q hp hn hs H hH Q χ X).at t =
      ((A.bass Q χ hχ).homotopy X).at t ≫
        (bassComparison F q hp hn hs Q).app (L.obj X) := by
  change ((cone L c F q hp hn hs H hH Q χ X).parameterLooping).at t ≫
      loopRowInverse F q hp hn Q (L.obj X) = _
  rw [Homotopy.parameterLooping_at, cone_at_eq L c F q hp hn hs H hH A hcell Q χ hχ,
    loopMap_comp, Category.assoc, loopRow_comparison]
  rfl

end Quillen.KTheory.Bass.DiagramRowCell
