/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.KTheory.Bass.ConeGeneratorRecognition
public import Quillen.KTheory.Bass.DiagramRowCellIteration

/-! A generator-defined successor relation, independent of the iterated comparison target. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace Quillen.KTheory.Bass.TensorGeneratedRecipe
open DiagramRowCell
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



/-- A successor is any four-generator cone extension, followed by the fixed index/row maps
and explicit old-loop conversion. The relation mentions no iterated family or Track equality. -/
def GeneratorStep
    (H' : ∀ X, Homotopy ((nextInput L c F q hp hn hs Q).app X)
      ((nextInput L c F q hp hn hs Q).app X)) : Prop :=
  ∀ X, ∃ K : Homotopy _ _,
    StrictSquare.MapHomotopy.ConeGeneratorLaw (square L c F q hp hn hs H hH (Q.obj X)) K ∧
    ∀ n, (H' X).level n =
      (((K.postcomp
        ((ConeTrack.indexMap Q L χ (DiagramRowRefinement.diagram F q hp hn)).app X ≫
          DiagramConeRowStrength.strength Q F q hp hn (L.obj X))).parameterLooping).postcomp
        (loopRowInverse F q hp hn Q (L.obj X))).level n

variable (A : NaturalTrack.Track L c F)
  (hcell : ∀ X t, (H X).at t = (A.homotopy X).at t ≫
    (DiagramRowRefinement.comparison F q hp hn hs).app (L.obj X))
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- The actual endpoint-cast successor satisfies the independent generator relation. -/
theorem step_generated :
    GeneratorStep L c F q hp hn hs H hH Q χ
      (step L c F q hp hn hs H hH Q χ A hcell hχ) := by
  intro X
  refine ⟨(square L c F q hp hn hs H hH (Q.obj X)).cone,
    StrictSquare.MapHomotopy.cone_generatorLaw _, ?_⟩
  intro n
  rfl

end Quillen.KTheory.Bass.TensorGeneratedRecipe
