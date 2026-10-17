/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePairProjectedReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPauseTerminalChart

/-! The genuine polynomial chart square is the entire original ordinary M side face. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.PairLowerReference
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier

private theorem projected_node {U V W : Model.{u}}
    (A : U ⟶ V) (F H : V ⟶ W) (G G' : U ⟶ W)
    (ρ₀ : G'.functor ≅ G.functor) (ρ : G.functor ≅ (A ≫ H).functor)
    (η : H.functor ≅ F.functor) (M : Node H) :
    CommonReferenceProduct.reanchor (ρ₀ ≪≫ (ρ ≪≫ isoWhiskerLeft A.functor η))
        (precompNode A (CommonReferenceProduct.reanchor η.symm M)) =
      CommonReferenceProduct.reanchor ρ₀ (preReferenceNode G A ρ M) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change (ρ₀ ≪≫ (ρ ≪≫ isoWhiskerLeft A.functor η)) ≪≫
    isoWhiskerLeft A.functor (η.symm ≪≫ M.2) = ρ₀ ≪≫ (ρ ≪≫ isoWhiskerLeft A.functor M.2)
  rw [isoWhiskerLeft_trans, ← isoWhiskerLeft_symm]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (β.app c) ≫ polynomialProjection P c = laurentProjection P c)

/-- The full old-side anchor, typed at the actual precomposed sheet reference. -/
def projectedAnchor :
    (BassProjectionPath.WholeReference.reference P c (inputReference P p q)).functor ≅
      (normalizedMap (polynomialProjection P a) ≫
        CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q).functor :=
  referenceIso P p q ≪≫ BassMOuterJoin.oldSideIso P p q β hc

/-- Source projection keeps the whole original polynomial chart nerve. -/
def projectedChart : C(|parameterSSet
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)|,
      |parameterSSet (BassProjectionPath.WholeReference.reference P c (inputReference P p q))|) :=
  mapParameter (fun M ↦ CommonReferenceProduct.reanchor (projectedAnchor P p q β hc)
    (precompNode (normalizedMap (polynomialProjection P a)) M))

/-- Every full chart node retains the original source projection and old reference. -/
theorem projected_chart_node
    (M : Node (CoefficientBassRaw1PolynomialPausedChart.reference P β p q)) :
    CommonReferenceProduct.reanchor (projectedAnchor P p q β hc)
        (precompNode (normalizedMap (polynomialProjection P a))
          (CommonReferenceProduct.reanchor
            (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q) M)) =
      CommonReferenceProduct.reanchor (referenceIso P p q)
        (preReferenceNode (BassOverlap.commonReference P p q)
          (normalizedMap (polynomialProjection P a))
          (BassOverlap.commonToChartReference P p q β hc) M) := by
  exact projected_node (normalizedMap (polynomialProjection P a))
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
    (CoefficientBassRaw1PolynomialPausedChart.reference P β p q)
    (BassOverlap.commonReference P p q)
    (BassProjectionPath.WholeReference.reference P c (inputReference P p q))
    (referenceIso P p q) (BassOverlap.commonToChartReference P p q β hc)
    (BinaryNormalizationSimplex.total (coefficientMap P (β.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map q) ≫
        coefficientMap P ((polynomialUnderFunctor R).map p))) M

private theorem original_plus_nodes (i : Fin 18) :
    BassMWhole.nodes P p q (BassMWholeNerve.terminalOldChartIndex false i) =
      BassOverlap.chartOverlapNodes P p q (underToLaurent R) (laurentPlus_projection P c) i := by
  unfold BassMWholeNerve.terminalOldChartIndex
  simp only [Bool.false_eq_true, ite_false, Function.comp_apply]
  rw [BassMWhole.old_nodes, BassH1Merged.old_nodes, BassH0Merged.old_nodes,
    BassReferenceMerge.chart_nodes]
  change BassBottomCommonFamily.nodes P p q (Fin.castAdd 15 (Fin.castAdd 18 i)) = _
  unfold BassBottomCommonFamily.nodes
  rw [Fin.addCases_left]
  unfold BassOverlap.nodes
  rw [Fin.addCases_left]

private theorem original_minus_nodes (i : Fin 18) :
    BassMWhole.nodes P p q (BassMWholeNerve.terminalOldChartIndex true i) =
      BassOverlap.chartOverlapNodes P p q (underToLaurentInvert R)
        (laurentMinus_projection P c) i := by
  unfold BassMWholeNerve.terminalOldChartIndex
  simp only [ite_true, Function.comp_apply]
  rw [BassMWhole.old_nodes, BassH1Merged.old_nodes, BassH0Merged.old_nodes,
    BassReferenceMerge.chart_nodes]
  change BassBottomCommonFamily.nodes P p q (Fin.castAdd 15 (Fin.natAdd 18 i)) = _
  unfold BassBottomCommonFamily.nodes
  rw [Fin.addCases_left]
  unfold BassOverlap.nodes
  rw [Fin.addCases_right]

/-- The entire positive Laurent face keeps the original paused square and its full anchor. -/
theorem plus_chart_face (r s : I) :
    projectedChart P p q (underToLaurent R) (laurentPlus_projection P c)
        (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P (underToLaurent R) p q (r, s)) =
      laurentCube P p q (r, (s, 0)) := by
  dsimp only [projectedChart, CoefficientBassRaw1PolynomialPausedChart.sheetFamily,
    CoefficientBassRaw1PolynomialPausedChart.family, ContinuousMap.comp_apply]
  rw [mapParameter_parameter, mapParameter_parameter]
  change _ = mapParameter (CommonReferenceProduct.reanchor (referenceIso P p q))
    (CommonReferenceNerve.parameter _ _ (BassMWhole.scalarCube.{u} ![r, s, 0]))
  rw [BassMWholeNerve.terminal_old_plus_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter
    (BassProjectionPath.WholeReference.reference P c (inputReference P p q)) ns
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s)))
  funext i
  rw [original_plus_nodes]
  exact projected_chart_node P p q (underToLaurent R) (laurentPlus_projection P c) _

/-- The entire inverse face retains its independent original chart and unchanged pause. -/
theorem minus_chart_face (r s : I) :
    projectedChart P p q (underToLaurentInvert R) (laurentMinus_projection P c)
        (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P
          (underToLaurentInvert R) p q (r, s)) =
      laurentCube P p q (r, (s, 1)) := by
  dsimp only [projectedChart, CoefficientBassRaw1PolynomialPausedChart.sheetFamily,
    CoefficientBassRaw1PolynomialPausedChart.family, ContinuousMap.comp_apply]
  rw [mapParameter_parameter, mapParameter_parameter]
  change _ = mapParameter (CommonReferenceProduct.reanchor (referenceIso P p q))
    (CommonReferenceNerve.parameter _ _ (BassMWhole.scalarCube.{u} ![r, s, 1]))
  rw [BassMWholeNerve.terminal_old_minus_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter
    (BassProjectionPath.WholeReference.reference P c (inputReference P p q)) ns
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s)))
  funext i
  rw [original_minus_nodes]
  exact projected_chart_node P p q (underToLaurentInvert R) (laurentMinus_projection P c) _

end Quillen.PerfectComplexes.BassMWholeConeCarrier.PairLowerReference
