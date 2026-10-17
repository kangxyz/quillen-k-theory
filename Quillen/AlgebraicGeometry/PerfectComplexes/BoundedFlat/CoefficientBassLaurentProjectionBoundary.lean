/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSecondConeProjectionRoutes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentProjectionRoutes

/-! Exact restrictions of the prescribed projection boundary to its full Laurent summand. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassLaurentProjectionBoundary
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

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

theorem naturalitySquare_inclusion {M N : Under R ⥤ Under R} (α : M ⟶ N)
    (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj (M.obj a))))).space n) :
    (CoefficientBassSecondConeProjectionRoutes.naturalitySquare P u α).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P (M.obj a))).map n x) =
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P (N.obj b))).map n
      ((CoefficientBassLaurentProjectionRoutes.naturalitySquare P u α).level n (r, x)) := by
  unfold CoefficientBassSecondConeProjectionRoutes.naturalitySquare
    CoefficientBassLaurentProjectionRoutes.naturalitySquare
  apply trans_eval _ _ _ _ n id
    ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P (N.obj b))).map n)
    _ x
  · intro t
    exact CoefficientBassLaurentProjectionRoutes.composition_inclusion P
      (α.app a) (N.map u) n (unitInterval.symm t) x
  · intro t
    exact CoefficientBassLaurentProjectionRoutes.composition_inclusion P
      (M.map u) (α.app b) n t x

theorem plusLeft_inclusion (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (CoefficientBassSecondConeProjectionRoutes.plusLeft P u).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P
      ((laurentUnderFunctor R).obj b))).map n
      ((CoefficientBassLaurentProjectionRoutes.plusLeft P u).level n (r, x)) := by
  unfold CoefficientBassSecondConeProjectionRoutes.plusLeft
    CoefficientBassLaurentProjectionRoutes.plusLeft
  apply trans_eval _ _ _ _ n id
    ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P
      ((laurentUnderFunctor R).obj b))).map n) _ x
  · intro t
    exact (congrArg
      (fun y ↦ (CoefficientBassSecondConeProjectionRoutes.plusSquare P u).level n (t, y))
      (CoefficientBassLaurentProjectionRoutes.map_inclusion P
        ((polynomialUnderCoefficient R).app a) n x)).trans
      (naturalitySquare_inclusion P u (underToLaurent R) n t
        ((CoefficientBassLaurentProjectionRoutes.laurentMap P
          ((polynomialUnderCoefficient R).app a)).map n x))
  · intro t
    exact (congrArg
      ((boundedFlatCoefficientBassConeMap P ((underToLaurent R).app b)).map n)
      (naturalitySquare_inclusion P u (polynomialUnderCoefficient R) n t x)).trans
      (CoefficientBassLaurentProjectionRoutes.map_inclusion P
        ((underToLaurent R).app b) n
        ((CoefficientBassLaurentProjectionRoutes.polynomialSquare P u).level n (t, x)))

theorem plusRight_inclusion (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (CoefficientBassSecondConeProjectionRoutes.plusRight P u).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P
      ((laurentUnderFunctor R).obj b))).map n
      ((CoefficientBassLaurentProjectionRoutes.plusRight P u).level n (r, x)) := by
  unfold CoefficientBassSecondConeProjectionRoutes.plusRight
    CoefficientBassLaurentProjectionRoutes.plusRight
  apply trans_eval _ _ _ _ n id
    ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P
      ((laurentUnderFunctor R).obj b))).map n) _ x
  · intro t
    exact (congrArg
      ((boundedFlatCoefficientBassConeMap P ((laurentUnderFunctor R).map u)).map n)
      (CoefficientBassLaurentProjectionRoutes.composition_inclusion P
        ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a)
        n (unitInterval.symm t) x)).trans
      (CoefficientBassLaurentProjectionRoutes.map_inclusion P
        ((laurentUnderFunctor R).map u) n
        ((CoefficientBassLaurentProjectionRoutes.plusComposition P a).level n
          (unitInterval.symm t, x)))
  · intro t
    apply trans_eval _ _ _ _ n id
      ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P
        ((laurentUnderFunctor R).obj b))).map n) _ x
    · intro v
      exact naturalitySquare_inclusion P u (laurentUnderCoefficient R) n v x
    · intro v
      exact (congrArg
        (fun y ↦ (CoefficientBassSecondConeProjectionRoutes.plusComposition P b).level n (v, y))
        (CoefficientBassLaurentProjectionRoutes.map_inclusion P u n x)).trans
        (CoefficientBassLaurentProjectionRoutes.composition_inclusion P
          ((polynomialUnderCoefficient R).app b) ((underToLaurent R).app b) n v
          ((CoefficientBassLaurentProjectionRoutes.laurentMap P u).map n x))

theorem minusLeft_inclusion (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (CoefficientBassSecondConeProjectionRoutes.minusLeft P u).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P
      ((laurentUnderFunctor R).obj b))).map n
      ((CoefficientBassLaurentProjectionRoutes.minusLeft P u).level n (r, x)) := by
  unfold CoefficientBassSecondConeProjectionRoutes.minusLeft
    CoefficientBassLaurentProjectionRoutes.minusLeft
  apply trans_eval _ _ _ _ n id
    ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P
      ((laurentUnderFunctor R).obj b))).map n) _ x
  · intro t
    exact (congrArg
      (fun y ↦ (CoefficientBassSecondConeProjectionRoutes.minusSquare P u).level n (t, y))
      (CoefficientBassLaurentProjectionRoutes.map_inclusion P
        ((polynomialUnderCoefficient R).app a) n x)).trans
      (naturalitySquare_inclusion P u (underToLaurentInvert R) n t
        ((CoefficientBassLaurentProjectionRoutes.laurentMap P
          ((polynomialUnderCoefficient R).app a)).map n x))
  · intro t
    exact (congrArg
      ((boundedFlatCoefficientBassConeMap P ((underToLaurentInvert R).app b)).map n)
      (naturalitySquare_inclusion P u (polynomialUnderCoefficient R) n t x)).trans
      (CoefficientBassLaurentProjectionRoutes.map_inclusion P
        ((underToLaurentInvert R).app b) n
        ((CoefficientBassLaurentProjectionRoutes.polynomialSquare P u).level n (t, x)))

theorem minusRight_inclusion (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (CoefficientBassSecondConeProjectionRoutes.minusRight P u).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P
      ((laurentUnderFunctor R).obj b))).map n
      ((CoefficientBassLaurentProjectionRoutes.minusRight P u).level n (r, x)) := by
  unfold CoefficientBassSecondConeProjectionRoutes.minusRight
    CoefficientBassLaurentProjectionRoutes.minusRight
  apply trans_eval _ _ _ _ n id
    ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P
      ((laurentUnderFunctor R).obj b))).map n) _ x
  · intro t
    exact (congrArg
      ((boundedFlatCoefficientBassConeMap P ((laurentUnderFunctor R).map u)).map n)
      (CoefficientBassLaurentProjectionRoutes.composition_inclusion P
        ((polynomialUnderCoefficient R).app a) ((underToLaurentInvert R).app a)
        n (unitInterval.symm t) x)).trans
      (CoefficientBassLaurentProjectionRoutes.map_inclusion P
        ((laurentUnderFunctor R).map u) n
        ((CoefficientBassLaurentProjectionRoutes.minusComposition P a).level n
          (unitInterval.symm t, x)))
  · intro t
    apply trans_eval _ _ _ _ n id
      ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P
        ((laurentUnderFunctor R).obj b))).map n) _ x
    · intro v
      exact naturalitySquare_inclusion P u (laurentUnderCoefficient R) n v x
    · intro v
      exact (congrArg
        (fun y ↦ (CoefficientBassSecondConeProjectionRoutes.minusComposition P b).level n (v, y))
        (CoefficientBassLaurentProjectionRoutes.map_inclusion P u n x)).trans
        (CoefficientBassLaurentProjectionRoutes.composition_inclusion P
          ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b) n v
          ((CoefficientBassLaurentProjectionRoutes.laurentMap P u).map n x))

end Quillen.PerfectComplexes.CoefficientBassLaurentProjectionBoundary
