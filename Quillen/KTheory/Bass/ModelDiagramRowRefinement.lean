/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramRowInterchange
public import Quillen.KTheory.Bass.ModelDiagramConeFiniteStructure
public import Quillen.Topology.Prespectrum.RowRefinement
public import Quillen.Topology.Prespectrum.StableFiniteRange
public import Quillen.Topology.Prespectrum.ParameterLoopingStableEquivalence

/-!
# Stable row refinements of the original finite Bass-stage cones

The row interchange is the computed finite cone and parameter-loop construction on the
original model diagram. Its two-structure identity gives the actual whole comparison into
the row-compatible target. The proved finite range of the original stage cone makes that
comparison stable in every signed degree, without treating a later stage as a Model.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u v w
namespace Quillen.KTheory.Bass.ModelDiagramRowRefinement
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ Model.{w})

/-- The unchanged original comparison cone at the specified finite Bass stage. -/
abbrev source (X : C) : LoopPrespectrum.{w} :=
  (ConeTrack.diagram Q ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).obj X

/-- The genuine distinguished-row target uses the computed original finite-stage interchange. -/
def carrier (X : C) : LoopPrespectrum.{w} :=
  RowRefinement.spectrum (source Q i F X) (ModelDiagramRowInterchange.cone Q i F X)
    (ModelDiagramRowInterchange.cone_point Q i F X)

/-- The actual original structure maps give the complete finite-stage comparison. -/
def comparison (X : C) : source Q i F X ⟶ carrier Q i F X :=
  RowRefinement.comparison (source Q i F X) (ModelDiagramRowInterchange.cone Q i F X)
    (ModelDiagramRowInterchange.cone_point Q i F X)
    (ModelDiagramRowInterchange.cone_structure Q i F X)

/-- No positive component of the original structure comparison has been changed. -/
theorem comparison_succ (X : C) (k : ℕ) :
    (comparison Q i F X).map (k + 1) = (source Q i F X).structureMap (k + 1) := rfl

/-- Degree zero retains both original structure maps and their independent parameters. -/
theorem comparison_zero (X : C) (x : (source Q i F X).space 0) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((comparison Q i F X).map 0 x) r) s =
      (source Q i F X).structureMap 1 ((source Q i F X).structureMap 0 x r) s := rfl

/-- The finite-stage comparison is stable using its actual target structure and finite range. -/
theorem comparison_isStableEquivalence (X : C) :
    IsStableEquivalence (comparison Q i F X) := by
  apply isStableEquivalence_of_eventually_linearPi (comparison Q i F X) (i + 2) (2 * i + 2)
  intro n hn k hk
  change Function.Bijective (homotopyGroupMap (N := Fin (k + 2))
    ((source Q i F X).structureMap (n + 1)) ((source Q i F X).map_point (n + 1)))
  have h := modelDiagramIterate_cone_structure_bijective Q i F X (n - (i + 2)) k (by omega)
  rw [show n - (i + 2) + i + 3 = n + 1 by omega] at h
  exact h

/-- Actual parameter looping preserves this stable roof at every finite stage. -/
theorem parameterComparison_isStableEquivalence (X : C) :
    IsStableEquivalence (parameterLoopingMap (comparison Q i F X)) :=
  parameterLoopingMap_isStableEquivalence _ (comparison_isStableEquivalence Q i F X)

end Quillen.KTheory.Bass.ModelDiagramRowRefinement
