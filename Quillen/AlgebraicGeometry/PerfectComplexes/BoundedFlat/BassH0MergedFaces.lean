/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0MergedNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassReindexedSupport

/-! The thirteen whole native support diagrams are actual faces of the new common simplex. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH0Merged

/-- Relabel an actually supported old face in its proved monotone order. -/
def oldFace {k : ℕ} (α : ⦋k⦌ ⟶ ⦋44⦌)
    (h : Monotone (BassSupportOrder.oldIndex ∘ α.toOrderHom)) : ⦋k⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨BassSupportOrder.oldIndex ∘ α.toOrderHom, h⟩

/-- Relabel an actually supported H0 face in its proved monotone order. -/
def h0Face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋30⦌)
    (h : Monotone (BassSupportOrder.h0Index ∘ α.toOrderHom)) : ⦋k⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨BassSupportOrder.h0Index ∘ α.toOrderHom, h⟩

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Any supported old face is retained with every original full reference node. -/
theorem old_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋44⦌)
    (h : Monotone (BassSupportOrder.oldIndex ∘ α.toOrderHom)) :
    (simplex P u v).face (oldFace α h) = (BassReferenceMerge.simplex P u v).face α := by
  unfold simplex BassReferenceMerge.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  apply ModelSimplex.ofIsos_nodes_congr
    (fun i ↦ nodes P u v ((oldFace α h).toOrderHom i))
    (fun i ↦ BassReferenceMerge.nodes P u v (α.toOrderHom i))
  intro i
  exact old_nodes P u v (α.toOrderHom i)

/-- Any supported H0 face is retained with its actual canonically transported references. -/
theorem h0_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋30⦌)
    (h : Monotone (BassSupportOrder.h0Index ∘ α.toOrderHom)) :
    (simplex P u v).face (h0Face α h) = (BassH0Merge.simplex P u v).face α := by
  unfold simplex BassH0Merge.simplex ModelSimplex.reanchorSimplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  apply ModelSimplex.ofIsos_nodes_congr
    (fun i ↦ nodes P u v ((h0Face α h).toOrderHom i))
    (fun i ↦ BassH0Merge.nodes P u v (α.toOrderHom i))
  intro i
  exact h0_nodes P u v (α.toOrderHom i)

theorem oldPlus_face (i : Fin 3) :
    (simplex P u v).face (BassSupportOrder.oldPlusFace i) =
      (BassReferenceMerge.simplex P u v).face
        (BassPrimitiveSupport.rectangleFace i ≫
          (BassOverlap.plusFace ≫ BassReferenceMerge.chartFace)) :=
  old_face P u v _ (BassSupportOrder.oldPlus_monotone i)

theorem oldMinus_face (i : Fin 3) :
    (simplex P u v).face (BassSupportOrder.oldMinusFace i) =
      (BassReferenceMerge.simplex P u v).face
        (BassPrimitiveSupport.rectangleFace i ≫
          (BassOverlap.minusFace ≫ BassReferenceMerge.chartFace)) :=
  old_face P u v _ (BassSupportOrder.oldMinus_monotone i)

theorem h0Plus_face (i : Fin 3) :
    (simplex P u v).face (BassSupportOrder.h0PlusFace i) =
      (BassH0Merge.simplex P u v).face
        (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace) :=
  h0_face P u v _ (BassSupportOrder.h0Plus_monotone i)

theorem h0Minus_face (i : Fin 3) :
    (simplex P u v).face (BassSupportOrder.h0MinusFace i) =
      (BassH0Merge.simplex P u v).face
        (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace) :=
  h0_face P u v _ (BassSupportOrder.h0Minus_monotone i)

/-- The entire original bottom product simplex is retained as an actual full fourteen-face. -/
theorem bottom_face : (simplex P u v).face BassSupportOrder.bottomFace =
    BassLaurentBottomFace.simplex P u v :=
  (old_face P u v BassReferenceMerge.bottomFace BassSupportOrder.bottom_monotone).trans
    (BassReferenceMerge.bottom_face P u v)

/-- Native evaluation is unchanged on every supported old face, at every original level. -/
theorem old_family_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋44⦌)
    (h : Monotone (BassSupportOrder.oldIndex ∘ α.toOrderHom)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map BassSupportOrder.oldIndex (StdSimplex.map α.toOrderHom z), x) =
    prespectrumSimplexFamily (BassReferenceMerge.simplex P u v) n
      (StdSimplex.map α.toOrderHom z, x) := by
  rw [← StdSimplex.map_comp]
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map (oldFace α h).toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, old_face, prespectrumSimplexFamily_face]

/-- The same value preservation holds on every supported original H0 face. -/
theorem h0_family_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋30⦌)
    (h : Monotone (BassSupportOrder.h0Index ∘ α.toOrderHom)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map BassSupportOrder.h0Index (StdSimplex.map α.toOrderHom z), x) =
    prespectrumSimplexFamily (BassH0Merge.simplex P u v) n
      (StdSimplex.map α.toOrderHom z, x) := by
  rw [← StdSimplex.map_comp]
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map (h0Face α h).toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, h0_face, prespectrumSimplexFamily_face]

end Quillen.PerfectComplexes.BassH0Merged
