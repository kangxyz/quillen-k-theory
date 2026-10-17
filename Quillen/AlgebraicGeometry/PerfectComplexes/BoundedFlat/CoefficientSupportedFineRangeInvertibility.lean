/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedConnectiveInvertibility
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBottomChartExactness
public import Quillen.KTheory.Bass.ModelDiagramTransitionSequence
public import Quillen.KTheory.Bass.TwoChartStableMapInvertibility

/-!
# The original fine supported Bass transitions are invertible in their full finite-stage range

For a qcqs ambient scheme and compact removed open, the actual stage-i transition is an
isomorphism on every stable group in degree at least minus i. The proof uses the actual
inter-stage short-exact row map,
the original connective seed, and the proved original bottom chart exactness. At the new
bottom degree its right terms vanish; above it, the previous-stage isomorphisms act at all
four original coefficient vertices. No all-stage comparison with the raw tower is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.KTheory.Bass Quillen.Bass.TwoChartStable
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- Every actual supported transition is invertible throughout its genuine finite-stage range. -/
theorem boundedFlatCoefficientSupportedBassTransition_isIso_of_le (i : ℕ)
    (a : Under R) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientSupportedBassTransition f i).app a)) := by
  induction i generalizing a d with
  | zero =>
    have hn : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (by simpa using hd)
    rw [← hn]
    exact boundedFlatCoefficientSupportedBassTransition_zero_connective_isIso f a d.toNat
  | succ i ih =>
    let F := boundedFlatCoefficientSupportedModelFunctor f
    let η := boundedFlatCoefficientSupportedBassSeed f
    let φ := modelDiagramTransitionSequenceMap F η i a d
    let : IsIso (φ.τ₁) := by
      let : IsIso ((stableHomotopyFunctor (d + 1)).map
          (modelDiagramTransitionSquareMap F η i a).left.right) := by
        change IsIso ((stableHomotopyFunctor (d + 1)).map
          ((boundedFlatCoefficientSupportedBassTransition f i).app
            ((polynomialUnderFunctor R).obj a)))
        exact ih _ _ (by omega)
      let : IsIso ((stableHomotopyFunctor (d + 1)).map
          (modelDiagramTransitionSquareMap F η i a).right.left) := by
        change IsIso ((stableHomotopyFunctor (d + 1)).map
          ((boundedFlatCoefficientSupportedBassTransition f i).app
            ((polynomialUnderFunctor R).obj a)))
        exact ih _ _ (by omega)
      let : IsIso ((stableHomotopyFunctor (d + 1)).map
          (modelDiagramTransitionSquareMap F η i a).right.right) := by
        change IsIso ((stableHomotopyFunctor (d + 1)).map
          ((boundedFlatCoefficientSupportedBassTransition f i).app
            ((laurentUnderFunctor R).obj a)))
        exact ih _ _ (by omega)
      exact chartCokernelMap_isIso (modelDiagramTransitionSquareMap F η i a) (d + 1)
    let : IsIso (φ.τ₃) := by
      by_cases hdi : -(i : ℤ) ≤ d
      · let : IsIso ((stableHomotopyFunctor d).map
            (modelDiagramTransitionSquareMap F η i a).left.left) := by
          change IsIso ((stableHomotopyFunctor d).map
            ((boundedFlatCoefficientSupportedBassTransition f i).app a))
          exact ih _ _ hdi
        let : IsIso ((stableHomotopyFunctor d).map
            (modelDiagramTransitionSquareMap F η i a).left.right) := by
          change IsIso ((stableHomotopyFunctor d).map
            ((boundedFlatCoefficientSupportedBassTransition f i).app
              ((polynomialUnderFunctor R).obj a)))
          exact ih _ _ hdi
        let : IsIso ((stableHomotopyFunctor d).map
            (modelDiagramTransitionSquareMap F η i a).right.left) := by
          change IsIso ((stableHomotopyFunctor d).map
            ((boundedFlatCoefficientSupportedBassTransition f i).app
              ((polynomialUnderFunctor R).obj a)))
          exact ih _ _ hdi
        let : IsIso ((stableHomotopyFunctor d).map
            (modelDiagramTransitionSquareMap F η i a).right.right) := by
          change IsIso ((stableHomotopyFunctor d).map
            ((boundedFlatCoefficientSupportedBassTransition f i).app
              ((laurentUnderFunctor R).obj a)))
          exact ih _ _ hdi
        exact bassRightMap_isIso (modelDiagramTransitionSquareMap F η i a) d
      · have hlt : d < -(i : ℤ) := by omega
        have he : d = -((i + 1 : ℕ) : ℤ) := by omega
        have hS := modelDiagramTwoChartRight_isZero_of_lt F i a d hlt
        have hT : IsZero (bassRightGroup (modelDiagramTwoChartSquare F (i + 1) a) d) := by
          rw [he]
          exact boundedFlatCoefficientSupportedBottomBassRight_isZero f a (i + 1)
        exact isIso_of_source_target_iso_zero φ.τ₃ hS.isoZero hT.isoZero
    let : IsIso (φ.τ₂) := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
      (modelDiagramTwoChartSequence_shortExact F i a d)
      (modelDiagramTwoChartSequence_shortExact F (i + 1) a d)
    change IsIso ((stableHomotopyFunctor d).map
      ((strictDiagramTransition (laurentUnderSquareFunctor R) η (i + 1)).app a))
    have h := modelDiagramTransitionSequenceMap_middle_successor F η i a d
    let e := (eqToIso (congrArg
      (fun H : (Under R ⥤ LoopPrespectrum) ⥤ (Under R ⥤ LoopPrespectrum) =>
        H.obj (F ⋙ Quillen.Waldhausen.IteratedS.prespectrumFunctor))
      (strictDiagramIterate_succ_right (laurentUnderSquareFunctor R) (i + 1)))).app a
    let : IsIso ((stableHomotopyFunctor d).map
        ((strictDiagramTransition (laurentUnderSquareFunctor R) η (i + 1)).app a) ≫
          (stableHomotopyFunctor d).map e.hom) := by
      change IsIso (_ ≫ (stableHomotopyFunctor d).map
        ((eqToHom (congrArg
          (fun H : (Under R ⥤ LoopPrespectrum) ⥤ (Under R ⥤ LoopPrespectrum) =>
            H.obj (F ⋙ Quillen.Waldhausen.IteratedS.prespectrumFunctor))
          (strictDiagramIterate_succ_right (laurentUnderSquareFunctor R) (i + 1)))).app a))
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((stableHomotopyFunctor d).map e.hom)

end Quillen.PerfectComplexes
