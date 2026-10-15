/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.DoubleSquareCommonSimplex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleNativeEvaluation
public import Quillen.Topology.Prespectrum.RelativeLevelEvaluation

/-! Whole native triple constituents of the actual double-square in one common diagram.
Repeated scalar slots are still separate;
this does not yet assemble the native three-routes square. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.DoubleSquareCommonSimplex
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The split-triple comparison parameter embedded in the first face of the common 23-simplex. -/
def firstParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 24)) :=
  ⟨fun z ↦ StdSimplex.map firstFace.toOrderHom (SplitTripleSimplex.comparisonParameter z),
    by fun_prop⟩

/-- The split-triple comparison parameter embedded in the middle face of the common 23-simplex. -/
def middleParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 24)) :=
  ⟨fun z ↦ StdSimplex.map middleFace.toOrderHom (SplitTripleSimplex.comparisonParameter z),
    by fun_prop⟩

/-- The split-triple comparison parameter embedded in the last face of the common 23-simplex. -/
def lastParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 24)) :=
  ⟨fun z ↦ StdSimplex.map lastFace.toOrderHom (SplitTripleSimplex.comparisonParameter z),
    by fun_prop⟩

/-- Every point of the literal firstTriple is evaluated in the common family. -/
theorem first_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen A)).space n) :
    prespectrumSimplexFamily (simplex p q p' q' a b c hp hq) n
      (firstParameter (r, s), x) =
      (DoubleSquareTrack.firstTriple (p := p) (q := q) (c := c)).level n (r, (s, x)) := by
  change prespectrumSimplexFamily _ n
    (StdSimplex.map firstFace.toOrderHom (SplitTripleSimplex.comparisonParameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, first_face]
  refine (SplitTripleSimplex.comparison_native_evaluation c q p n r s x).trans ?_
  exact (Homotopy.RelHomotopy.ofLevels_apply _ _ _ _ _ n r s x).symm

/-- Every point of middleTriple retains its original hq endpoint transport. -/
theorem middle_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen A)).space n) :
    prespectrumSimplexFamily (simplex p q p' q' a b c hp hq) n
      (middleParameter (r, s), x) =
      (DoubleSquareTrack.middleTriple p q q' b c hq).level n (r, (s, x)) := by
  change prespectrumSimplexFamily _ n
    (StdSimplex.map middleFace.toOrderHom (SplitTripleSimplex.comparisonParameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, middle_face]
  refine (SplitTripleSimplex.comparison_native_evaluation q' b p n r s x).trans ?_
  exact (Homotopy.RelHomotopy.ofLevels_apply _ _ _ _ _ n r s x).symm

/-- Every point of lastTriple retains both original square transports. -/
theorem last_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen A)).space n) :
    prespectrumSimplexFamily (simplex p q p' q' a b c hp hq) n
      (lastParameter (r, s), x) =
      (DoubleSquareTrack.lastTriple p q p' q' a b c hp hq).level n (r, (s, x)) := by
  change prespectrumSimplexFamily _ n
    (StdSimplex.map lastFace.toOrderHom (SplitTripleSimplex.comparisonParameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, last_face]
  refine (SplitTripleSimplex.comparison_native_evaluation q' p' a n r s x).trans ?_
  exact (Homotopy.RelHomotopy.ofLevels_apply _ _ _ _ _ n r s x).symm

end Quillen.PerfectComplexes.DoubleSquareCommonSimplex
