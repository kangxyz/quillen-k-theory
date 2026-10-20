/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.CarrierSquareDescent
public import Quillen.Aglib.Topology.Path.AssociatorEvaluationComparison
/-! Naturality of the unchanged square/associator boundary recipe under two evaluations. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
namespace Quillen.CarrierPathSquare
open Path.Evaluation
variable {X Y T : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
variable {a b c d e : X} {a' b' c' d' e' : Y}

/-- The full chosen boundary is natural from the whole moving square and three final pieces. -/
theorem correctedRecipe_evaluations (f : X → T) (g : C(Y, T))
    {old : Path e d} {new : Path a d} {bottom : Path e a}
    {old' : Path e' d'} {new' : Path a' d'} {bottom' : Path e' a'}
    (Q : Square old new bottom (Path.refl d))
    (Q' : Square old' new' bottom' (Path.refl d'))
    (p : Path a b) (q : Path b c) (w : Path c d)
    (p' : Path a' b') (q' : Path b' c') (w' : Path c' d')
    (hn : (p.trans q).trans w = new) (hn' : (p'.trans q').trans w' = new')
    (hQ : ∀ r s, f (Q.parameter (r, s)) = g (Q'.parameter (r, s)))
    (hb : ∀ s, f (bottom s) = g (bottom' s))
    (hp : ∀ s, f (p s) = g (p' s)) (hq : ∀ s, f (q s) = g (q' s))
    (hw : ∀ s, f (w s) = g (w' s)) (r s : I) :
    f ((Q.toBoundary.trans
      (((Path.Homotopy.refl bottom).hcomp
        ((Path.Homotopy.transAssoc p q w).cast hn rfl)).hcomp
          (Path.Homotopy.refl (Path.refl d).symm))) (r, s)) =
    g ((Q'.toBoundary.trans
      (((Path.Homotopy.refl bottom').hcomp
        ((Path.Homotopy.transAssoc p' q' w').cast hn' rfl)).hcomp
          (Path.Homotopy.refl (Path.refl d').symm))) (r, s)) := by
  have hd : f d = g d' := by simpa only [Path.target] using hw 1
  rw [Path.Homotopy.trans_apply, Path.Homotopy.trans_apply]
  split_ifs
  · exact hQ _ _
  · simp only [Path.Homotopy.hcomp_apply]
    split_ifs
    · change f (((Path.Homotopy.refl bottom).hcomp
        ((Path.Homotopy.transAssoc p q w).cast hn rfl)) (_, _)) =
        g (((Path.Homotopy.refl bottom').hcomp
          ((Path.Homotopy.transAssoc p' q' w').cast hn' rfl)) (_, _))
      rw [Path.Homotopy.hcomp_apply, Path.Homotopy.hcomp_apply]
      split_ifs
      · exact hb _
      · exact associator_evaluations f g p q w p' q' w' hp hq hw _ _
    · exact hd

/-- Collapse surjectivity descends the actual corrected recipe at every interior point. -/
theorem correctedSquareRecipe_evaluations (f : X → T) (g : C(Y, T))
    {old : Path e d} {new : Path a d} {bottom : Path e a}
    {old' : Path e' d'} {new' : Path a' d'} {bottom' : Path e' a'}
    (Q : Square old new bottom (Path.refl d))
    (Q' : Square old' new' bottom' (Path.refl d'))
    (p : Path a b) (q : Path b c) (w : Path c d)
    (p' : Path a' b') (q' : Path b' c') (w' : Path c' d')
    (hn : (p.trans q).trans w = new) (hn' : (p'.trans q').trans w' = new')
    (hQ : ∀ r s, f (Q.parameter (r, s)) = g (Q'.parameter (r, s)))
    (hb : ∀ s, f (bottom s) = g (bottom' s))
    (hp : ∀ s, f (p s) = g (p' s)) (hq : ∀ s, f (q s) = g (q' s))
    (hw : ∀ s, f (w s) = g (w' s)) (r s : I) :
    f ((boundarySquare (Q.toBoundary.trans
      (((Path.Homotopy.refl bottom).hcomp
        ((Path.Homotopy.transAssoc p q w).cast hn rfl)).hcomp
          (Path.Homotopy.refl (Path.refl d).symm)))).parameter (r, s)) =
    g ((boundarySquare (Q'.toBoundary.trans
      (((Path.Homotopy.refl bottom').hcomp
        ((Path.Homotopy.transAssoc p' q' w').cast hn' rfl)).hcomp
          (Path.Homotopy.refl (Path.refl d').symm)))).parameter (r, s)) := by
  obtain ⟨z, hz⟩ := Quillen.ThreeSideSquare.collapse_surjective (r, s)
  rw [← hz]
  change f (boundaryParameter _ (Quillen.ThreeSideSquare.collapse z)) =
    g (boundaryParameter _ (Quillen.ThreeSideSquare.collapse z))
  rw [boundaryParameter_collapse, boundaryParameter_collapse]
  exact correctedRecipe_evaluations f g Q Q' p q w p' q' w' hn hn'
    hQ hb hp hq hw z.1 z.2

end Quillen.CarrierPathSquare
