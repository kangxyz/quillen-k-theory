/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagramTelescope
public import Quillen.Topology.Prespectrum.TelescopeDiagramMap

/-!
# Actual Bass–telescope comparison under original tower maps

The original strict diagram maps commute with the comparison on every telescope cylinder and
internal loop parameter. The proof uses the actual cone and span generators, with no topology
or stability hypothesis and no replacement of the original transition squares.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (F G : ℕ → C ⥤ LoopPrespectrum.{w})
    (τ : ∀ i, F i ⟶ F (i + 1)) (σ : ∀ i, G i ⟶ G (i + 1))
    (a : ∀ i, F i ⟶ G i) (h : ∀ i, a i ≫ σ i = τ i ≫ a (i + 1))

include h in
/-- Applying the actual Bass functor preserves the same original transition square. -/
theorem strictDiagramTelescopeMapCompatibility (i : ℕ) :
    (strictDiagramFunctor Q).map (a i) ≫ (strictDiagramFunctor Q).map (σ i) =
      (strictDiagramFunctor Q).map (τ i) ≫ (strictDiagramFunctor Q).map (a (i + 1)) := by
  simpa only [Functor.map_comp] using congrArg (strictDiagramFunctor Q).map (h i)

/-- The actual Bass–telescope comparison commutes with the unchanged original tower maps. -/
theorem strictDiagramTelescopeComparison_naturality :
    Telescope.diagramMap (fun i => (strictDiagramFunctor Q).obj (F i))
        (fun i => (strictDiagramFunctor Q).obj (G i))
        (fun i => (strictDiagramFunctor Q).map (τ i))
        (fun i => (strictDiagramFunctor Q).map (σ i))
        (fun i => (strictDiagramFunctor Q).map (a i))
        (strictDiagramTelescopeMapCompatibility Q F G τ σ a h) ≫
        strictDiagramTelescopeComparison Q G σ =
      strictDiagramTelescopeComparison Q F τ ≫
        (strictDiagramFunctor Q).map (Telescope.diagramMap F G τ σ a h) := by
  apply NatTrans.ext
  funext X
  apply Telescope.hom_ext
  intro k i s x
  change Path _ _ at x
  apply Path.ext
  funext t
  change (Telescope.diagramConeIso G σ (Q.obj X)).inv.map k
      (Telescope.cylinder
        (fun i => mappingCone (StrictSquare.comparison ((G i).mapArrow.mapArrow.obj (Q.obj X))))
        (Telescope.diagramConeTransition G σ (Q.obj X)) k i
        (s, (mappingConeMap (strictSquareComparisonFunctor.map
          (((Functor.mapArrowFunctor (Arrow C) (Arrow LoopPrespectrum.{w})).map
            ((Functor.mapArrowFunctor C LoopPrespectrum.{w}).map (a i))).app (Q.obj X)))).map k
          (x t))) =
    (mappingConeMap (strictSquareComparisonFunctor.map
      (((Functor.mapArrowFunctor (Arrow C) (Arrow LoopPrespectrum.{w})).map
        ((Functor.mapArrowFunctor C LoopPrespectrum.{w}).map
          (Telescope.diagramMap F G τ σ a h))).app (Q.obj X)))).map k
      ((Telescope.diagramConeIso F τ (Q.obj X)).inv.map k
        (Telescope.cylinder
          (fun i => mappingCone (StrictSquare.comparison ((F i).mapArrow.mapArrow.obj (Q.obj X))))
          (Telescope.diagramConeTransition F τ (Q.obj X)) k i (s, x t)))
  induction x t using Quot.inductionOn with
  | h z => cases z with
    | inl y => rfl
    | inr z =>
      obtain ⟨r, q⟩ := z
      induction q using Quot.inductionOn with
      | h z => cases z with
        | inl z => cases z <;> rfl
        | inr z => rfl

/-- Original stage squares give a whole square after the genuine Bass–telescope comparison. -/
theorem strictDiagramTelescopeComparison_square
    (b : ∀ i, F i ⟶ (strictDiagramFunctor Q).obj (F i))
    (c : ∀ i, G i ⟶ (strictDiagramFunctor Q).obj (G i))
    (hb : ∀ i, b i ≫ (strictDiagramFunctor Q).map (τ i) = τ i ≫ b (i + 1))
    (hc : ∀ i, c i ≫ (strictDiagramFunctor Q).map (σ i) = σ i ≫ c (i + 1))
    (hbc : ∀ i, b i ≫ (strictDiagramFunctor Q).map (a i) = a i ≫ c i) :
    (Telescope.diagramMap F (fun i => (strictDiagramFunctor Q).obj (F i)) τ
        (fun i => (strictDiagramFunctor Q).map (τ i)) b hb ≫
        strictDiagramTelescopeComparison Q F τ) ≫
        (strictDiagramFunctor Q).map (Telescope.diagramMap F G τ σ a h) =
      Telescope.diagramMap F G τ σ a h ≫
        (Telescope.diagramMap G (fun i => (strictDiagramFunctor Q).obj (G i)) σ
          (fun i => (strictDiagramFunctor Q).map (σ i)) c hc ≫
          strictDiagramTelescopeComparison Q G σ) := by
  rw [Category.assoc, ← strictDiagramTelescopeComparison_naturality Q F G τ σ a h,
    ← Category.assoc, ← Category.assoc]
  apply congrArg (· ≫ strictDiagramTelescopeComparison Q G σ)
  apply NatTrans.ext
  funext X
  apply Telescope.hom_ext
  intro k i s x
  exact congrArg
    (fun y => Telescope.cylinder (fun i => ((strictDiagramFunctor Q).obj (G i)).obj X)
      (fun i => ((strictDiagramFunctor Q).map (σ i)).app X) k i (s, y))
    (congrArg (fun m => m.map k x) (NatTrans.congr_app (hbc i) X))

end Quillen.KTheory.Bass
