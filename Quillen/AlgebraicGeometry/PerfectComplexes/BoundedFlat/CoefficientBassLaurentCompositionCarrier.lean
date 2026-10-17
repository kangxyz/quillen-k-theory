/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleLeftColumnNodes
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactFamily

/-! Full three-node Laurent composition paths for the prescribed projection boundary. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassLaurentCompositionCarrier
open BassH0Merge
private theorem binary_nodes_simplex {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ModelSimplex.ofIsos (BinaryNormalizationSimplex.sourceMap f g)
      (fun i ↦ (binaryNodes f g i).1) (fun i ↦ (binaryNodes f g i).2) =
      BinaryNormalizationSimplex.simplex f g := by
  let Fs : Fin 3 → (modelOf (boundedFlatPerfectWaldhausen Z) ⟶
      modelOf (boundedFlatPerfectWaldhausen X)) :=
    ![BinaryNormalizationSimplex.sourceMap f g, BinaryNormalizationSimplex.intermediateMap f g,
      BinaryNormalizationSimplex.targetMap f g]
  let refs : ∀ i, (BinaryNormalizationSimplex.sourceMap f g).functor ≅ (Fs i).functor :=
    Fin.cases (Iso.refl _) (Fin.cases (BinaryNormalizationSimplex.first f g)
      (Fin.cases (BinaryNormalizationSimplex.total f g) (fun j ↦ Fin.elim0 j)))
  exact ModelSimplex.ofIsos_nodes_congr (binaryNodes f g) (fun i ↦ ⟨Fs i, refs i⟩)
    (by intro i; fin_cases i <;> rfl)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original coefficient map of the Laurent extension of `q`. -/
abbrev first := coefficientMap P ((laurentUnderFunctor R).map q)
/-- The original coefficient map of the Laurent extension of `p`. -/
abbrev second := coefficientMap P ((laurentUnderFunctor R).map p)
/-- The binary normalization source reference for the two original Laurent coefficient maps. -/
abbrev reference := BinaryNormalizationSimplex.sourceMap (first P q) (second P p)
/-- The three full binary-normalization nodes of those Laurent coefficient maps. -/
abbrev nodes := binaryNodes (first P q) (second P p)

/-- The original three-node binary path in the full Laurent composition reference nerve. -/
def family : C(I, |nerve (Codiscrete (CommonReferenceNerve.Node (reference P p q)))|) :=
  (CommonReferenceNerve.parameter (reference P p q) (nodes P p q)).comp
    (binaryPath (k := 2) 0 1 2).toContinuousMap

theorem family_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P p q)
      (family P p q) n (t, x) =
    (boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n (t, x) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (reference P p q) (family P p q) (nodes P p q) t
    (binaryPath (k := 2) 0 1 2 t) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  change prespectrumSimplexFamily
    (ModelSimplex.ofIsos (BinaryNormalizationSimplex.sourceMap (first P q) (second P p))
      (fun i ↦ (binaryNodes (first P q) (second P p) i).1)
      (fun i ↦ (binaryNodes (first P q) (second P p) i).2)) n _ = _
  rw [binary_nodes_simplex]
  exact BinaryNormalizationSimplex.native_path (first P q) (second P p) n t x

theorem family_zero : family P p q 0 = CommonReferenceNerve.parameter (reference P p q)
    (nodes P p q) (Convexity.StdSimplex.single 0) :=
  congrArg (CommonReferenceNerve.parameter (reference P p q) (nodes P p q))
    (binaryPath (k := 2) 0 1 2).source

theorem family_one : family P p q 1 = CommonReferenceNerve.parameter (reference P p q)
    (nodes P p q) (Convexity.StdSimplex.single 2) :=
  congrArg (CommonReferenceNerve.parameter (reference P p q) (nodes P p q))
    (binaryPath (k := 2) 0 1 2).target

end Quillen.PerfectComplexes.CoefficientBassLaurentCompositionCarrier
