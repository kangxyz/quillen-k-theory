/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPause

/-! Actual terminal pause, all-level compact evaluation,
basepoints and independent structure time. -/
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
open BassReferenceMerge BassH0Merge BassH1Join
attribute [local irreducible] boundedFlatNormalizedPullback

private theorem pause_product_simplex {V W T : Model.{u}} {p q : ℕ}
    (F : V ⟶ T) (F₀ : V ⟶ W) (Fs : Fin (p + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (Fs i).functor)
    (G₀ : W ⟶ T) (Gs : Fin (q + 1) → (W ⟶ T))
    (refs : ∀ i, G₀.functor ≅ (Gs i).functor) (η : F.functor ≅ (F₀ ≫ G₀).functor) :
    ModelSimplex.ofIsos F (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).1)
      (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).2) =
      CommonReferenceProduct.simplex F₀ Fs ρ G₀ Gs refs := by
  exact ModelSimplex.reanchorSimplex_eq η
    (fun i ↦ ⟨CommonReferenceProduct.vertices Fs Gs i,
      CommonReferenceProduct.references F₀ Fs ρ G₀ Gs refs i⟩)

private theorem pause_product_comp {V W T : Model.{u}} {p q : ℕ}
    (F : V ⟶ T) (F₀ : V ⟶ W) (Fs : Fin (p + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (Fs i).functor)
    (G₀ : W ⟶ T) (Gs : Fin (q + 1) → (W ⟶ T))
    (refs : ∀ i, G₀.functor ≅ (Gs i).functor) (η : F.functor ≅ (F₀ ≫ G₀).functor)
    (n : ℕ) (x : (prespectrum V).space n)
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    prespectrumSimplexFamily
      (ModelSimplex.ofIsos F (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).1)
        (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).2)) n
      (Quillen.SimplexGrid.parameter.{u} p q (z, w), x) =
      prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ Gs refs) n
        (w, prespectrumSimplexFamily (ModelSimplex.ofIsos F₀ Fs ρ) n (z, x)) :=
  (congrArg (fun S ↦ prespectrumSimplexFamily S n
    (Quillen.SimplexGrid.parameter.{u} p q (z, w), x))
    (pause_product_simplex F F₀ Fs ρ G₀ Gs refs η)).trans
      (CommonReferenceProduct.prespectrum_comp F₀ Fs ρ G₀ Gs refs n x z w)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- Every level retains the entire original moving polynomial square before the chart square. -/
theorem polynomial_pause_one_native
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.prespectrumFamily _ (polynomialProductNodes P u v w α hc) n
      (polynomialPauseParameter.{u} inverse ![1, q, s, t], x) =
      (CoefficientTransformationComposition.square P α w).level n
        (s, (CoefficientTransformationComposition.movingSquare P (polynomialUnderCoefficient R)
          u v).pauseRight.level n (q, (productPolynomialTime inverse t, x))) := by
  have hcube (r s : unitInterval) : coefficientPauseCube ![1, r, s] =
      DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s) :=
    ChangedBoundaryPause.cube_one _ r s
  change CommonReferenceNerve.prespectrumFamily _ (polynomialProductNodes P u v w α hc) n
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (coefficientPauseCube ![1, q, productPolynomialTime inverse t],
        NativeSquareFiveSimplex.parameter s), x) = _
  rw [hcube]
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  refine (pause_product_comp _ _ _ _ _ _ _ (polynomialProductAnchor P u v w α hc)
    n x (DoubleSquareScalarPaths.coefficientPausedSquareParameter
      (q, productPolynomialTime inverse t)) (NativeSquareFiveSimplex.parameter s)).trans ?_
  change prespectrumSimplexFamily (CoefficientSquareFamilies.chartSimplex P w α) n
    (NativeSquareFiveSimplex.parameter s,
      prespectrumSimplexFamily (CoefficientTransformationComposition.Scalar.simplex
        P (polynomialUnderCoefficient R) u v) n
          (DoubleSquareScalarPaths.coefficientPausedSquareParameter
            (q, productPolynomialTime inverse t), x)) = _
  rw [CoefficientTransformationComposition.Scalar.pausedSquare_native]
  exact NativeSquareFiveSimplex.native _ _ _ _ _ n s _

/-- Every level retains the entire original chart moving square after the polynomial square. -/
theorem chart_pause_one_native
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.prespectrumFamily _ (chartProductNodes P u v w α hd) n
      (chartPauseParameter.{u} inverse ![1, q, s, t], x) =
      (CoefficientTransformationComposition.movingSquare P α v w).pauseRight.level n
        (q, (s, (boundedFlatCoefficientPolynomialSquareHomotopy P u).level n
          (productPolynomialTime inverse t, x))) := by
  have hcube (r s : unitInterval) : coefficientPauseCube ![1, r, s] =
      DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s) :=
    ChangedBoundaryPause.cube_one _ r s
  change CommonReferenceNerve.prespectrumFamily _ (chartProductNodes P u v w α hd) n
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t),
        coefficientPauseCube ![1, q, s]), x) = _
  rw [hcube]
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  refine (pause_product_comp _ _ _ _ _ _ _ (chartProductAnchor P u v w α hd)
    n x (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t))
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s))).trans ?_
  change prespectrumSimplexFamily (CoefficientTransformationComposition.Scalar.simplex P α v w) n
    (DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s),
      prespectrumSimplexFamily (CoefficientSquareFamilies.polynomialSimplex P u) n
        (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t), x)) = _
  rw [CoefficientSquareFamilies.polynomial_native,
    CoefficientTransformationComposition.Scalar.pausedSquare_native]

/-- Every interior point is evaluated in the original full-reference ninety-node family. -/
theorem polynomial_pause_compact_family
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (z : PauseCube) (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (polynomialPause P u v w α hc inverse) n
      (z, x) = CommonReferenceNerve.prespectrumFamily _ (polynomialProductNodes P u v w α hc) n
        (polynomialPauseParameter.{u} inverse z, x) :=
  CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _
    (polynomialPause P u v w α hc inverse) (polynomialProductNodes P u v w α hc)
    z (polynomialPauseParameter.{u} inverse z) rfl n x

/-- The four comparison coordinates leave the original native basepoint fixed at every level. -/
theorem polynomial_pause_point
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (z : PauseCube) (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily _ (polynomialPause P u v w α hc inverse) n
      (z, (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).point n) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).point n :=
  CommonReferenceNerve.compactPrespectrumFamily_point _ _ n z

/-- Structure time is independent of every comparison, coefficient and product coordinate. -/
theorem polynomial_pause_structure
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (z : PauseCube) (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n)
    (h : unitInterval) :
    CommonReferenceNerve.compactPrespectrumFamily _ (polynomialPause P u v w α hc inverse) (n + 1)
      (z, (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).structureMap
        n x h) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).structureMap n
        (CommonReferenceNerve.compactPrespectrumFamily _ (polynomialPause P u v w α hc inverse) n
          (z, x)) h :=
  CommonReferenceNerve.compactPrespectrumFamily_structure _ _ n z x h

/-- Every interior point is evaluated in the original full-reference ninety-node family. -/
theorem chart_pause_compact_family
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (z : PauseCube) (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (chartPause P u v w α hd inverse) n
      (z, x) = CommonReferenceNerve.prespectrumFamily _ (chartProductNodes P u v w α hd) n
        (chartPauseParameter.{u} inverse z, x) :=
  CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _
    (chartPause P u v w α hd inverse) (chartProductNodes P u v w α hd)
    z (chartPauseParameter.{u} inverse z) rfl n x

/-- The four comparison coordinates leave the original native basepoint fixed at every level. -/
theorem chart_pause_point
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (z : PauseCube) (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily _ (chartPause P u v w α hd inverse) n
      (z, (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).point n) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).point n :=
  CommonReferenceNerve.compactPrespectrumFamily_point _ _ n z

/-- Structure time is independent of every comparison, coefficient and product coordinate. -/
theorem chart_pause_structure
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (z : PauseCube) (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n)
    (h : unitInterval) :
    CommonReferenceNerve.compactPrespectrumFamily _ (chartPause P u v w α hd inverse) (n + 1)
      (z, (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).structureMap
        n x h) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).structureMap n
        (CommonReferenceNerve.compactPrespectrumFamily _ (chartPause P u v w α hd inverse) n
          (z, x)) h :=
  CommonReferenceNerve.compactPrespectrumFamily_structure _ _ n z x h

/-- Level zero retains a loop coordinate independent of all four pause coordinates. -/
theorem polynomial_pause_loop
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (z : PauseCube)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))))
    (ℓ : unitInterval) :
    (show Path
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d))))) from
      CommonReferenceNerve.compactPrespectrumFamily _ (polynomialPause P u v w α hc inverse)
        0 (z, γ)) ℓ =
    CommonReferenceNerve.compactStageFamily _ 0 (polynomialPause P u v w α hc inverse)
      (z, γ ℓ) :=
  CommonReferenceNerve.compactPrespectrumFamily_zero_apply _ _ z γ ℓ

/-- Level zero retains a loop coordinate independent of all four pause coordinates. -/
theorem chart_pause_loop
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (z : PauseCube)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))))
    (ℓ : unitInterval) :
    (show Path
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d))))) from
      CommonReferenceNerve.compactPrespectrumFamily _ (chartPause P u v w α hd inverse)
        0 (z, γ)) ℓ =
    CommonReferenceNerve.compactStageFamily _ 0 (chartPause P u v w α hd inverse)
      (z, γ ℓ) :=
  CommonReferenceNerve.compactPrespectrumFamily_zero_apply _ _ z γ ℓ

end Quillen.PerfectComplexes.BassMWholeNerve
