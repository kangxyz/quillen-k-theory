/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentProjectionRoutes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareFiveSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactFamily

/-! The prescribed Laurent naturality track with all five full reference nodes. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassLaurentNaturalityCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)
  {M N : Under R ⥤ Under R} (α : M ⟶ N)

/-- The coefficient map induced by the Laurent image of `N.map u`. -/
abbrev first := coefficientMap P ((laurentUnderFunctor R).map (N.map u))
/-- The coefficient map induced by the Laurent image of the component `α.app a`. -/
abbrev second := coefficientMap P ((laurentUnderFunctor R).map (α.app a))
/-- The coefficient map induced by the Laurent image of the component `α.app b`. -/
abbrev third := coefficientMap P ((laurentUnderFunctor R).map (α.app b))
/-- The coefficient map induced by the Laurent image of `M.map u`. -/
abbrev fourth := coefficientMap P ((laurentUnderFunctor R).map (M.map u))

theorem square : first P u (N := N) ≫ second P α = third P α ≫ fourth P u (M := M) :=
  coefficientMap_naturality P (whiskerRight α (laurentUnderFunctor R)) u

/-- The common reference for the first composite in the Laurent naturality square. -/
abbrev reference := NativeSquareFiveSimplex.source (first P u (N := N)) (second P α)
/-- The five full reference nodes of the Laurent naturality square. -/
abbrev nodes := NativeSquareFiveSimplex.nodes (first P u (N := N)) (second P α)
  (third P α) (fourth P u (M := M)) (square P u α)

/-- The interval family in the five-node reference simplex with the prescribed naturality clock. -/
def family : C(I, |nerve (Codiscrete (CommonReferenceNerve.Node (reference P u α)))|) :=
  (CommonReferenceNerve.parameter (reference P u α) (nodes P u α)).comp
    NativeSquareFiveSimplex.parameter.toContinuousMap

private theorem trans_eval {E F E' F' : LoopPrespectrum.{u}}
    {f g h : E ⟶ F} {f' g' h' : E' ⟶ F'}
    (H : Homotopy f g) (K : Homotopy g h)
    (H' : Homotopy f' g') (K' : Homotopy g' h') (n : ℕ)
    {T : Type v} (φ : F.space n → T) (ψ : F'.space n → T)
    (x : E.space n) (x' : E'.space n)
    (hH : ∀ r, φ (H.level n (r, x)) = ψ (H'.level n (r, x')))
    (hK : ∀ r, φ (K.level n (r, x)) = ψ (K'.level n (r, x'))) (r : I) :
    φ ((H.trans K).level n (r, x)) = ψ ((H'.trans K').level n (r, x')) := by
  change φ (((H.levelHomotopy n).trans (K.levelHomotopy n)) (r, x)) =
    ψ (((H'.levelHomotopy n).trans (K'.levelHomotopy n)) (r, x'))
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact hH _
  · exact hK _

theorem original_level (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj (M.obj a))))).space n) :
    (boundedFlatPerfectPrespectrumSquareHomotopy
      (first P u (N := N)) (second P α) (third P α) (fourth P u (M := M))
      (square P u α)).level n (t, x) =
    (CoefficientBassLaurentProjectionRoutes.naturalitySquare P u α).level n (t, x) := by
  rw [boundedFlatPerfectPrespectrumSquareHomotopy_eq]
  unfold CoefficientBassLaurentProjectionRoutes.naturalitySquare
  apply trans_eval _ _ _ _ n id id x x
  · intro r
    rfl
  · intro r
    rfl

theorem family_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj (M.obj a))))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P u α)
      (family P u α) n (t, x) =
    (CoefficientBassLaurentProjectionRoutes.naturalitySquare P u α).level n (t, x) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (reference P u α) (family P u α) (nodes P u α) t
    (NativeSquareFiveSimplex.parameter t) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  exact (NativeSquareFiveSimplex.native _ _ _ _ _ n t x).trans
    (original_level P u α n t x)

theorem family_zero : family P u α 0 = CommonReferenceNerve.parameter (reference P u α)
    (nodes P u α) (Convexity.StdSimplex.single 2) :=
  congrArg (CommonReferenceNerve.parameter (reference P u α) (nodes P u α))
    NativeSquareFiveSimplex.parameter.source

theorem family_one : family P u α 1 = CommonReferenceNerve.parameter (reference P u α)
    (nodes P u α) (Convexity.StdSimplex.single 4) :=
  congrArg (CommonReferenceNerve.parameter (reference P u α) (nodes P u α))
    NativeSquareFiveSimplex.parameter.target

end Quillen.PerfectComplexes.CoefficientBassLaurentNaturalityCarrier
