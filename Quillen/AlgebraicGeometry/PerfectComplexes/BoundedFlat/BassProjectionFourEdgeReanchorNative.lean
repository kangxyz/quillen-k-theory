/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeReanchorRealization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeConeEvaluation
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! Changing the actual input reference preserves the complete original native cone family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Reanchor
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier FourEdgeTree
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E E' : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (δ : E'.functor ≅ E.functor)
local notation "J" => normalizedMap (polynomialProjection P a)

/-- Every input and degree, including zero, retains its whole four-edge native value. -/
theorem tree_native (n : ℕ) (y : FourEdgeTree.space E J) (x : (prespectrum V).space n) :
    FourEdgeTree.nativeEval E' J n (tree P a E E' δ y) x =
      FourEdgeTree.nativeEval E J n y x := by
  have h := funext_cells E J
    (fun z ↦ FourEdgeTree.nativeEval E' J n (tree P a E E' δ z) x)
    (fun z ↦ FourEdgeTree.nativeEval E J n z x)
  apply congrFun (h ?_ ?_ ?_ ?_ ?_ ?_) y
  · intro z
    rw [tree_plus, nativeEval_plus, nativeEval_plus]
    dsimp only [nativePlus]
    rw [pointwise_reanchor]
  · intro z
    rw [tree_minus, nativeEval_minus, nativeEval_minus]
    dsimp only [nativeMinus]
    rw [pointwise_reanchor]
  · intro z t
    rw [tree_edge12, nativeEval_edge12, nativeEval_edge12]
    dsimp only [nativeCylinder]
    rw [pointwise_reanchor]
  · intro z t
    rw [tree_edge01, nativeEval_edge01, nativeEval_edge01]
    dsimp only [nativeCylinder]
    rw [pointwise_reanchor]
  · intro z t
    rw [tree_edge03, nativeEval_edge03, nativeEval_edge03]
    dsimp only [nativeCylinder]
    rw [pointwise_reanchor]
  · intro z t
    rw [tree_edge34, nativeEval_edge34, nativeEval_edge34]
    dsimp only [nativeCylinder]
    rw [pointwise_reanchor]

/-- The complete unreduced cone value is invariant under the specified full reference iso. -/
theorem cone_native (n : ℕ) (y : scalarCone P a E) (x : (prespectrum V).space n) :
    coneEval P a E' n (cone P a E E' δ y) x = coneEval P a E n y x := by
  have h := SetDescent.funext (beta P a E) (SSet.stdSimplex.isTerminalObj₀.from _)
    (fun z ↦ coneEval P a E' n (cone P a E E' δ z) x)
    (fun z ↦ coneEval P a E n z x)
  apply congrFun (h ?_ ?_ ?_) y
  · rintro ⟨z, ⟨t⟩⟩
    change coneEval P a E' n
      (cone P a E E' δ (cylinder E J (reference P a E) (beta P a E) (z, t))) x =
      coneEval P a E n (cylinder E J (reference P a E) (beta P a E) (z, t)) x
    rw [cone_cylinder, coneEval_cylinder, coneEval_cylinder, tree_native]
  · intro z
    change coneEval P a E' n
      (cone P a E E' δ (laurentInclusion E J (reference P a E) (beta P a E) z)) x =
      coneEval P a E n (laurentInclusion E J (reference P a E) (beta P a E) z) x
    rw [cone_laurent, coneEval_laurent, coneEval_laurent]
    dsimp only [laurentValue]
    rw [pointwise_reanchor]
  · intro z
    have hz : z = (default : |tipSSet|) := Subsingleton.elim _ _
    subst z
    change coneEval P a E' n
      (cone P a E E' δ (tip E J (reference P a E) (beta P a E))) x =
      coneEval P a E n (tip E J (reference P a E) (beta P a E)) x
    rw [cone_tip, coneEval_tip, coneEval_tip]

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Reanchor
