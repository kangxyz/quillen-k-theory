/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgePrecompRealization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeConeEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompNative

/-! Exact all-degree native recovery for the complete tree and its unreduced cone. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Precomp
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier FourEdgeTree
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {U V : Model.{u + 1}} (A : U ⟶ V)
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => normalizedMap (polynomialProjection P a)

/-- Full source precomposition is evaluated on the original native input in every degree. -/
theorem tree_native (n : ℕ) (y : FourEdgeTree.space E J) (x : (prespectrum U).space n) :
    FourEdgeTree.nativeEval (A ≫ E) J n (tree P a A E y) x =
      FourEdgeTree.nativeEval E J n y ((prespectrumMap A).map n x) := by
  have h := funext_cells E J
    (fun z ↦ FourEdgeTree.nativeEval (A ≫ E) J n (tree P a A E z) x)
    (fun z ↦ FourEdgeTree.nativeEval E J n z ((prespectrumMap A).map n x))
  apply congrFun (h ?_ ?_ ?_ ?_ ?_ ?_) y
  · intro z
    rw [tree_plus, nativeEval_plus, nativeEval_plus]
    dsimp only [nativePlus]
    rw [show pointwisePrespectrumFamily ((A ≫ E) ≫ J) n
        (mapParameter (precompNode A) z) x =
      pointwisePrespectrumFamily (E ≫ J) n z ((prespectrumMap A).map n x) from
        CutOpenPrecomp.pointwise_precomp A (E ≫ J) n z x]
  · intro z
    rw [tree_minus, nativeEval_minus, nativeEval_minus]
    dsimp only [nativeMinus]
    rw [show pointwisePrespectrumFamily ((A ≫ E) ≫ J) n
        (mapParameter (precompNode A) z) x =
      pointwisePrespectrumFamily (E ≫ J) n z ((prespectrumMap A).map n x) from
        CutOpenPrecomp.pointwise_precomp A (E ≫ J) n z x]
  · intro z t
    rw [tree_edge12, nativeEval_edge12, nativeEval_edge12]
    dsimp only [nativeCylinder]
    rw [show pointwisePrespectrumFamily (A ≫ E) n (mapParameter (precompNode A) z) x =
      pointwisePrespectrumFamily E n z ((prespectrumMap A).map n x) from
        CutOpenPrecomp.pointwise_precomp A E n z x]
  · intro z t
    rw [tree_edge01, nativeEval_edge01, nativeEval_edge01]
    dsimp only [nativeCylinder]
    rw [show pointwisePrespectrumFamily (A ≫ E) n (mapParameter (precompNode A) z) x =
      pointwisePrespectrumFamily E n z ((prespectrumMap A).map n x) from
        CutOpenPrecomp.pointwise_precomp A E n z x]
  · intro z t
    rw [tree_edge03, nativeEval_edge03, nativeEval_edge03]
    dsimp only [nativeCylinder]
    rw [show pointwisePrespectrumFamily (A ≫ E) n (mapParameter (precompNode A) z) x =
      pointwisePrespectrumFamily E n z ((prespectrumMap A).map n x) from
        CutOpenPrecomp.pointwise_precomp A E n z x]
  · intro z t
    rw [tree_edge34, nativeEval_edge34, nativeEval_edge34]
    dsimp only [nativeCylinder]
    rw [show pointwisePrespectrumFamily (A ≫ E) n (mapParameter (precompNode A) z) x =
      pointwisePrespectrumFamily E n z ((prespectrumMap A).map n x) from
        CutOpenPrecomp.pointwise_precomp A E n z x]

/-- The Laurent, cylinder and terminal-tip values descend without restricting native inputs. -/
theorem cone_native (n : ℕ) (y : scalarCone P a E) (x : (prespectrum U).space n) :
    coneEval P a (A ≫ E) n (cone P a A E y) x =
      coneEval P a E n y ((prespectrumMap A).map n x) := by
  have h := SetDescent.funext (beta P a E) (SSet.stdSimplex.isTerminalObj₀.from _)
    (fun z ↦ coneEval P a (A ≫ E) n (cone P a A E z) x)
    (fun z ↦ coneEval P a E n z ((prespectrumMap A).map n x))
  apply congrFun (h ?_ ?_ ?_) y
  · rintro ⟨z, ⟨t⟩⟩
    change coneEval P a (A ≫ E) n
      (cone P a A E (cylinder E J (reference P a E) (beta P a E) (z, t))) x =
      coneEval P a E n (cylinder E J (reference P a E) (beta P a E) (z, t))
        ((prespectrumMap A).map n x)
    rw [cone_cylinder, coneEval_cylinder, coneEval_cylinder, tree_native]
  · intro z
    change coneEval P a (A ≫ E) n
      (cone P a A E (laurentInclusion E J (reference P a E) (beta P a E) z)) x =
      coneEval P a E n (laurentInclusion E J (reference P a E) (beta P a E) z)
        ((prespectrumMap A).map n x)
    rw [cone_laurent, coneEval_laurent, coneEval_laurent]
    dsimp only [laurentValue]
    rw [show pointwisePrespectrumFamily (reference P a (A ≫ E)) n
        (mapParameter (precompNode A) z) x =
      pointwisePrespectrumFamily (reference P a E) n z ((prespectrumMap A).map n x) from
        CutOpenPrecomp.pointwise_precomp A (reference P a E) n z x]
  · intro z
    have hz : z = (default : |tipSSet|) := Subsingleton.elim _ _
    subst z
    change coneEval P a (A ≫ E) n
      (cone P a A E (tip E J (reference P a E) (beta P a E))) x =
      coneEval P a E n (tip E J (reference P a E) (beta P a E))
        ((prespectrumMap A).map n x)
    rw [cone_tip, coneEval_tip, coneEval_tip]

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Precomp
