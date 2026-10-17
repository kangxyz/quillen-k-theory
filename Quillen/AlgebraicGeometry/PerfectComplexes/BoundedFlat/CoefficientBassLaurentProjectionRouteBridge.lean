/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentProjectionScalarNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentNaturalityCarrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionReferences

/-! Exact prescribed Laurent route boundaries, with the original casts and clocks. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassLaurentProjectionScalar
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

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The plus initial edge recovers the complete old Laurent route on every Laurent input. -/
theorem plus_zero_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily
      (reference P (underToLaurent R) u) (family P (underToLaurent R) u) n ((0, t), x) =
    (CoefficientBassLaurentProjectionRoutes.plusLeft P u).level n (t, x) := by
  refine (family_zero_original P (underToLaurent R) u n t x).trans ?_
  unfold DoubleSquareTrack.originalLeft CoefficientBassLaurentProjectionRoutes.plusLeft
  apply trans_eval _ _ _ _ n id id x x
  · intro r
    exact CoefficientBassLaurentNaturalityCarrier.original_level P u (underToLaurent R) n r
      ((CoefficientBassLaurentProjectionRoutes.laurentMap P
        ((polynomialUnderCoefficient R).app a)).map n x)
  · intro r
    exact congrArg ((CoefficientBassLaurentProjectionRoutes.laurentMap P
      ((underToLaurent R).app b)).map n)
      (CoefficientBassLaurentNaturalityCarrier.original_level P u
        (polynomialUnderCoefficient R) n r x)

/-- The minus initial edge recovers the complete old Laurent route on every Laurent input. -/
theorem minus_zero_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily
      (reference P (underToLaurentInvert R) u) (family P (underToLaurentInvert R) u) n ((0, t), x) =
    (CoefficientBassLaurentProjectionRoutes.minusLeft P u).level n (t, x) := by
  refine (family_zero_original P (underToLaurentInvert R) u n t x).trans ?_
  unfold DoubleSquareTrack.originalLeft CoefficientBassLaurentProjectionRoutes.minusLeft
  apply trans_eval _ _ _ _ n id id x x
  · intro r
    exact CoefficientBassLaurentNaturalityCarrier.original_level P u (underToLaurentInvert R) n r
      ((CoefficientBassLaurentProjectionRoutes.laurentMap P
        ((polynomialUnderCoefficient R).app a)).map n x)
  · intro r
    exact congrArg ((CoefficientBassLaurentProjectionRoutes.laurentMap P
      ((underToLaurentInvert R).app b)).map n)
      (CoefficientBassLaurentNaturalityCarrier.original_level P u
        (polynomialUnderCoefficient R) n r x)

/-- The outer geometric square is the prescribed Laurent projection square on full inputs. -/
theorem outer_square_native
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : (polynomialUnderCoefficient R).app a ≫ α.app a =
      (laurentUnderCoefficient R).app a)
    (hb : (polynomialUnderCoefficient R).app b ≫ α.app b =
      (laurentUnderCoefficient R).app b)
    (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (boundedFlatPerfectPrespectrumSquareHomotopy
      (cMap P u) (q P α (a := a) ≫ p P (a := a))
      (q' P α (b := b) ≫ p' P (b := b)) (aMap P u)
      (DoubleSquareTrack.total_eq (p P (a := a)) (q P α (a := a))
        (p' P (b := b)) (q' P α (b := b)) (aMap P u) (bMap P u) (cMap P u)
        (polynomial_square P u) (chart_square P α u)).symm).level n (t, x) =
    (CoefficientBassLaurentProjectionRoutes.laurentSquare P u).level n (t, x) := by
  have ea : q P α (a := a) ≫ p P (a := a) =
      coefficientMap P ((laurentUnderFunctor R).map ((laurentUnderCoefficient R).app a)) :=
    (BassMWholeNerve.laurentComposition_total P
      ((polynomialUnderCoefficient R).app a) (α.app a)).symm.trans
      (congrArg (fun k ↦ coefficientMap P ((laurentUnderFunctor R).map k)) ha)
  have eb : q' P α (b := b) ≫ p' P (b := b) =
      coefficientMap P ((laurentUnderFunctor R).map ((laurentUnderCoefficient R).app b)) :=
    (BassMWholeNerve.laurentComposition_total P
      ((polynomialUnderCoefficient R).app b) (α.app b)).symm.trans
      (congrArg (fun k ↦ coefficientMap P ((laurentUnderFunctor R).map k)) hb)
  have h := boundedFlatGeometricSquare_level_congr
    (DoubleSquareTrack.total_eq (p P (a := a)) (q P α (a := a))
      (p' P (b := b)) (q' P α (b := b)) (aMap P u) (bMap P u) (cMap P u)
      (polynomial_square P u) (chart_square P α u)).symm
    (CoefficientBassLaurentNaturalityCarrier.square P u (laurentUnderCoefficient R))
    rfl ea eb rfl n
  exact (DFunLike.congr_fun h (t, x)).trans
    (CoefficientBassLaurentNaturalityCarrier.original_level P u (laurentUnderCoefficient R) n t x)

/-- The plus final edge recovers the full original Laurent route, including all nested clocks. -/
theorem plus_one_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily
      (reference P (underToLaurent R) u) (family P (underToLaurent R) u) n ((1, t), x) =
    (CoefficientBassLaurentProjectionRoutes.plusRight P u).level n (t, x) := by
  refine (family_one_original P (underToLaurent R) u n t x).trans ?_
  unfold DoubleSquareTrack.originalRight CoefficientBassLaurentProjectionRoutes.plusRight
  apply trans_eval _ _ _ _ n id id x x
  · intro r
    rfl
  · intro r
    apply trans_eval _ _ _ _ n id id x x
    · intro s
      exact outer_square_native P u (underToLaurent R)
        (polynomialUnderCoefficient_toLaurent R a) (polynomialUnderCoefficient_toLaurent R b) n s x
    · intro s
      rfl

/-- The minus final edge recovers the full original Laurent route, including all nested clocks. -/
theorem minus_one_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily
      (reference P (underToLaurentInvert R) u) (family P (underToLaurentInvert R) u) n ((1, t), x) =
    (CoefficientBassLaurentProjectionRoutes.minusRight P u).level n (t, x) := by
  refine (family_one_original P (underToLaurentInvert R) u n t x).trans ?_
  unfold DoubleSquareTrack.originalRight CoefficientBassLaurentProjectionRoutes.minusRight
  apply trans_eval _ _ _ _ n id id x x
  · intro r
    rfl
  · intro r
    apply trans_eval _ _ _ _ n id id x x
    · intro s
      exact outer_square_native P u (underToLaurentInvert R)
        (polynomialUnderCoefficient_toLaurentInvert R a)
        (polynomialUnderCoefficient_toLaurentInvert R b) n s x
    · intro s
      rfl

end Quillen.PerfectComplexes.CoefficientBassLaurentProjectionScalar
