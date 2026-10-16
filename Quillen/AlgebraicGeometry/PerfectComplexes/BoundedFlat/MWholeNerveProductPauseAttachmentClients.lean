/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPauseAttachments

/-! Actual seam consumers at every level and independent structure and input-loop times. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve

/-- Compact evaluation depends on the actual nerve point, with no new reference choice. -/
private theorem compact_family_of_point_eq {V W : Model.{u}} (F : V ⟶ W)
    {T U : Type*} [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace U] [CompactSpace U]
    (f : C(T, |nerve (Codiscrete (CommonReferenceNerve.Node F))|))
    (g : C(U, |nerve (Codiscrete (CommonReferenceNerve.Node F))|))
    (z : T) (y : U) (h : f z = g y) (n : ℕ) (x : (prespectrum V).space n) :
    CommonReferenceNerve.compactPrespectrumFamily F f n (z, x) =
      CommonReferenceNerve.compactPrespectrumFamily F g n (y, x) := by
  obtain ⟨k, N, b, hb⟩ := CommonReferenceNerve.exists_parameter F (g y)
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex F f N z b
    (h.trans hb.symm) n x).trans
      (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex F g N y b hb.symm n x).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The actual whole seam equality acts on every original prespectrum level. -/
theorem chart_pause_plus_laurent_native
    (r q t : unitInterval) (n : ℕ) (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space
      (op P, a))))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartPause P u v w (underToLaurent R) (laurentPlus_projection P d) false) n (![r, q, 0, t],
        x) =
    CommonReferenceNerve.compactPrespectrumFamily _
      (laurentPrism P u v w) n (![q, 1, lower t], x) :=
  compact_family_of_point_eq _ _ _ _ _ (chart_pause_plus_laurent_seam P u v w r q t) n x

/-- The seam's structure time stays independent of pause, coefficient and polynomial time. -/
theorem chart_pause_plus_laurent_structure
    (r q t : unitInterval) (n : ℕ) (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space
      (op P, a))))).space n)
    (h : unitInterval) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartPause P u v w (underToLaurent R) (laurentPlus_projection P d) false) (n + 1)
        (![r, q, 0, t], (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P,
          a))))).structureMap n x h) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).structureMap n
      (CommonReferenceNerve.compactPrespectrumFamily _
        (laurentPrism P u v w) n (![q, 1, lower t], x)) h := by
  rw [chart_pause_plus_laurent_native P u v w r q t (n + 1),
    CommonReferenceNerve.compactPrespectrumFamily_structure]

/-- Level zero retains the original input loop at its own independent coordinate. -/
theorem chart_pause_plus_laurent_loop
    (r q t : unitInterval)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))) (ℓ :
      unitInterval) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) (stagePoint 0 (modelOf
        (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) from
      CommonReferenceNerve.compactPrespectrumFamily _
        (chartPause P u v w (underToLaurent R) (laurentPlus_projection P d) false) 0 (![r, q, 0,
          t], γ)) ℓ =
    CommonReferenceNerve.compactStageFamily _ 0
      (laurentPrism P u v w) (![q, 1, lower t], γ ℓ) := by
  have h := chart_pause_plus_laurent_native P u v w r q t 0 γ
  exact (congrArg (fun p : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) (stagePoint 0 (modelOf
        (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) ↦ p ℓ) h).trans
    (CommonReferenceNerve.compactPrespectrumFamily_zero_apply _ _ _ γ ℓ)

/-- The actual whole seam equality acts on every original prespectrum level. -/
theorem chart_pause_minus_laurent_native
    (r q t : unitInterval) (n : ℕ) (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space
      (op P, a))))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartPause P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true) n (![r, q,
        0, t], x) =
    CommonReferenceNerve.compactPrespectrumFamily _
      (laurentPrism P u v w) n (![q, 1, upper (upper t)], x) :=
  compact_family_of_point_eq _ _ _ _ _ (chart_pause_minus_laurent_seam P u v w r q t) n x

/-- The seam's structure time stays independent of pause, coefficient and polynomial time. -/
theorem chart_pause_minus_laurent_structure
    (r q t : unitInterval) (n : ℕ) (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space
      (op P, a))))).space n)
    (h : unitInterval) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartPause P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true) (n + 1)
        (![r, q, 0, t], (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P,
          a))))).structureMap n x h) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).structureMap n
      (CommonReferenceNerve.compactPrespectrumFamily _
        (laurentPrism P u v w) n (![q, 1, upper (upper t)], x)) h := by
  rw [chart_pause_minus_laurent_native P u v w r q t (n + 1),
    CommonReferenceNerve.compactPrespectrumFamily_structure]

/-- Level zero retains the original input loop at its own independent coordinate. -/
theorem chart_pause_minus_laurent_loop
    (r q t : unitInterval)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))) (ℓ :
      unitInterval) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) (stagePoint 0 (modelOf
        (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) from
      CommonReferenceNerve.compactPrespectrumFamily _
        (chartPause P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true) 0 (![r,
          q, 0, t], γ)) ℓ =
    CommonReferenceNerve.compactStageFamily _ 0
      (laurentPrism P u v w) (![q, 1, upper (upper t)], γ ℓ) := by
  have h := chart_pause_minus_laurent_native P u v w r q t 0 γ
  exact (congrArg (fun p : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) (stagePoint 0 (modelOf
        (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) ↦ p ℓ) h).trans
    (CommonReferenceNerve.compactPrespectrumFamily_zero_apply _ _ _ γ ℓ)

/-- The actual whole seam equality acts on every original prespectrum level. -/
theorem chart_pause_raw_source_native
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool)
    (r q t : unitInterval) (n : ℕ) (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space
      (op P, a))))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartPause P u v w α hd inverse) n (![r, q, 1, t], x) =
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartProductPrism P u v w α hd inverse) n (![ChangedBoundaryPause.time (r, q), 1, t], x) :=
  compact_family_of_point_eq _ _ _ _ _ (chart_pause_source_side P u v w α hd inverse r q t) n x

/-- The seam's structure time stays independent of pause, coefficient and polynomial time. -/
theorem chart_pause_raw_source_structure
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool)
    (r q t : unitInterval) (n : ℕ) (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space
      (op P, a))))).space n)
    (h : unitInterval) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartPause P u v w α hd inverse) (n + 1)
        (![r, q, 1, t], (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P,
          a))))).structureMap n x h) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).structureMap n
      (CommonReferenceNerve.compactPrespectrumFamily _
        (chartProductPrism P u v w α hd inverse) n (![ChangedBoundaryPause.time (r, q), 1, t], x))
          h := by
  rw [chart_pause_raw_source_native P u v w α hd inverse r q t (n + 1),
    CommonReferenceNerve.compactPrespectrumFamily_structure]

/-- Level zero retains the original input loop at its own independent coordinate. -/
theorem chart_pause_raw_source_loop
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool)
    (r q t : unitInterval)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))) (ℓ :
      unitInterval) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) (stagePoint 0 (modelOf
        (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) from
      CommonReferenceNerve.compactPrespectrumFamily _
        (chartPause P u v w α hd inverse) 0 (![r, q, 1, t], γ)) ℓ =
    CommonReferenceNerve.compactStageFamily _ 0
      (chartProductPrism P u v w α hd inverse) (![ChangedBoundaryPause.time (r, q), 1, t], γ ℓ) :=
        by
  have h := chart_pause_raw_source_native P u v w α hd inverse r q t 0 γ
  exact (congrArg (fun p : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) (stagePoint 0 (modelOf
        (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))) ↦ p ℓ) h).trans
    (CommonReferenceNerve.compactPrespectrumFamily_zero_apply _ _ _ γ ℓ)

end Quillen.PerfectComplexes.BassMWholeNerve
