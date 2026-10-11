/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagram
public import Quillen.Topology.Prespectrum.TelescopeStrictSquare
public import Quillen.Topology.Prespectrum.TelescopeParameterLoopingStable
public import Quillen.Topology.Prespectrum.ParameterLoopingStableEquivalence
public import Quillen.Topology.Prespectrum.StrictSquareTopology

/-!
# The actual Bass endofunctor and the original telescope

The literal telescope–loop comparison followed by the inverse original square-cone interchange
gives an actual coefficient-natural map from the telescope of Bass images to the Bass image
of the telescope. It is stable under T1 of the original stage corners and keeps the original
Bass image of every stage inclusion. No connectivity or telescope point HEP is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (F : ℕ → C ⥤ LoopPrespectrum.{w}) (τ : ∀ i, F i ⟶ F (i + 1))

/-- The actual cylinder map and original cone interchange assemble coefficient-naturally. -/
def strictDiagramTelescopeComparison :
    Telescope.diagramFunctor (fun i => (strictDiagramFunctor Q).obj (F i))
        (fun i => (strictDiagramFunctor Q).map (τ i)) ⟶
      (strictDiagramFunctor Q).obj (Telescope.diagramFunctor F τ) where
  app X := Telescope.parameterLoopingComparison
      (fun i => mappingCone (StrictSquare.comparison ((F i).mapArrow.mapArrow.obj (Q.obj X))))
      (Telescope.diagramConeTransition F τ (Q.obj X)) ≫
    parameterLoopingMap (Telescope.diagramConeIso F τ (Q.obj X)).inv
  naturality X Y h := by
    apply Telescope.hom_ext
    intro k i s x
    change Path _ _ at x
    apply Path.ext
    funext t
    change (Telescope.diagramConeIso F τ (Q.obj Y)).inv.map k
        (Telescope.cylinder
          (fun i => mappingCone (StrictSquare.comparison ((F i).mapArrow.mapArrow.obj (Q.obj Y))))
          (Telescope.diagramConeTransition F τ (Q.obj Y)) k i
          (s, (mappingConeMap (strictSquareComparisonFunctor.map
            ((F i).mapArrow.mapArrow.map (Q.map h)))).map k (x t))) =
      (mappingConeMap (strictSquareComparisonFunctor.map
        ((Telescope.diagramFunctor F τ).mapArrow.mapArrow.map (Q.map h)))).map k
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

/-- On each exact original stage face, the comparison is the Bass image of that stage inclusion. -/
theorem strictDiagramTelescopeComparison_inclusion (i : ℕ) (X : C) :
    (Telescope.diagramInclusion (fun i => (strictDiagramFunctor Q).obj (F i))
        (fun i => (strictDiagramFunctor Q).map (τ i)) i).app X ≫
        (strictDiagramTelescopeComparison Q F τ).app X =
      ((strictDiagramFunctor Q).map (Telescope.diagramInclusion F τ i)).app X := by
  apply Hom.ext
  funext k
  ext x
  change Path _ _ at x
  apply Path.ext
  funext t
  change (Telescope.diagramConeIso F τ (Q.obj X)).inv.map k
      (Telescope.cylinder
        (fun i => mappingCone (StrictSquare.comparison ((F i).mapArrow.mapArrow.obj (Q.obj X))))
        (Telescope.diagramConeTransition F τ (Q.obj X)) k i (0, x t)) =
    (mappingConeMap (strictSquareComparisonFunctor.map
      (((Functor.mapArrowFunctor (Arrow C) (Arrow LoopPrespectrum)).map
        ((Functor.mapArrowFunctor C LoopPrespectrum).map
          (Telescope.diagramInclusion F τ i))).app (Q.obj X)))).map k (x t)
  induction x t using Quot.inductionOn with
  | h z => cases z with
    | inl y => rfl
    | inr z =>
      obtain ⟨r, q⟩ := z
      induction q using Quot.inductionOn with
      | h z => cases z with
        | inl z => cases z <;> rfl
        | inr z => rfl

variable [∀ i X k, T1Space (((F i).obj X).space k)]

/-- The actual comparison is stable in every signed degree under original stage T1 alone. -/
theorem strictDiagramTelescopeComparison_isStableEquivalence (X : C) :
    IsStableEquivalence ((strictDiagramTelescopeComparison Q F τ).app X) := by
  let h (i k : ℕ) : T1Space
      ((mappingCone (StrictSquare.comparison ((F i).mapArrow.mapArrow.obj (Q.obj X)))).space k) :=
    @mappingConeSpaceT1Space _ _ _ k
      (@StrictSquare.spanSpaceT1Space ((F i).mapArrow.mapArrow.obj (Q.obj X)) k
        (inferInstanceAs (T1Space (((F i).obj (Q.obj X).left.left).space k)))
        (inferInstanceAs (T1Space (((F i).obj (Q.obj X).left.right).space k)))
        (inferInstanceAs (T1Space (((F i).obj (Q.obj X).right.left).space k))))
      (inferInstanceAs (T1Space (((F i).obj (Q.obj X).right.right).space k)))
  apply IsStableEquivalence.comp
    (Telescope.parameterLoopingComparison_isStableEquivalence _ _)
  apply parameterLoopingMap_isStableEquivalence
  intro d
  change IsIso ((stableHomotopyFunctor d).map (Telescope.diagramConeIso F τ (Q.obj X)).inv)
  infer_instance

end Quillen.KTheory.Bass
