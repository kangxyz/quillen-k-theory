/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePairPaths
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeCorrectedSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCorrected
public import Quillen.Aglib.Topology.Path.EvaluationOperations

/-! The complete original polynomial cap maps to the frozen M side with every correction clock. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.PairProjection
open BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (t : I)
  (f : C(CoefficientBassRaw1PolynomialPairCone.carrier P β p q,
    FourEdge.scalarCone P c (inputReference P p q)))
  (hchart : ∀ r s, f (CoefficientBassRaw1PolynomialPairCone.chartSquare P β p q (r, s)) =
    cube P p q (r, (s, t)))
  (hlast : ∀ r s, f (CoefficientBassRaw1PolynomialPairCone.last P β p q (r, s)) =
    last P p q (r, (s, t)))
  (hinitial : ∀ r s, f (CoefficientBassRaw1PolynomialPairCone.initial P β p q (r, s)) =
    initial P p q (r, (s, t)))

include hchart hlast in
private theorem correction_map (r s : I) :
    f (CoefficientBassRaw1PolynomialPairCone.correction P β p q (r, s)) =
      correction P p q (r, s) t := by
  let ev : C(C(I, FourEdge.scalarCone P c (inputReference P p q)),
      FourEdge.scalarCone P c (inputReference P p q)) := ⟨fun g ↦ g t, by fun_prop⟩
  have h₁ := Path.Evaluation.transAssoc f
    (CoefficientBassRaw1PolynomialPairCone.firstPath P β p q)
    (CoefficientBassRaw1PolynomialPairCone.secondPath P β p q)
    (CoefficientBassRaw1PolynomialPairCone.thirdPath P β p q)
    ((firstPath P p q).map ev.continuous) ((secondPath P p q).map ev.continuous)
    ((thirdPath P p q).map ev.continuous)
    (fun s ↦ hchart 1 (Path.CarrierHalfPaths.lower s))
    (fun s ↦ hchart 1 (Path.CarrierHalfPaths.upper s)) (fun s ↦ hlast 1 s) r s
  have h₂ := Path.Evaluation.transAssoc ev
    (firstPath P p q) (secondPath P p q) (thirdPath P p q)
    ((firstPath P p q).map ev.continuous) ((secondPath P p q).map ev.continuous)
    ((thirdPath P p q).map ev.continuous)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) r s
  exact h₁.trans h₂.symm

include hchart hlast hinitial in
private theorem boundary_map (r s : I) :
    f (CoefficientBassRaw1PolynomialPairCone.correctedBoundary P β p q (r, s)) =
      correctedBoundary P p q (r, s) t := by
  have htip : f (CoefficientBassRaw1PolynomialPairCone.tip P β p q) =
      CommonReferenceNerve.FourEdgeTree.tip (inputReference P p q)
        (BassH0Merge.normalizedMap (polynomialProjection P c))
        (reference P c (inputReference P p q)) (FourEdge.beta P c (inputReference P p q)) := by
    have hh := hlast 1 1
    rw [CoefficientBassRaw1PolynomialPairCone.last_one, last_one] at hh
    exact hh
  have hB (r s : I) :
      f ((CoefficientBassRaw1PolynomialPairCone.initialSquare P β p q).toBoundary (r, s)) =
        (initialSquare P p q).toBoundary (r, s) t := hinitial _ _
  have hC (r s : I) :
      f (((Path.Homotopy.refl (CoefficientBassRaw1PolynomialPairCone.leftPath P β p q)).hcomp
        (CoefficientBassRaw1PolynomialPairCone.correction P β p q)) (r, s)) =
      ((Path.Homotopy.refl (leftPath P p q)).hcomp (correction P p q)) (r, s) t := by
    rw [Path.Homotopy.hcomp_apply, Path.Homotopy.hcomp_apply]
    split_ifs
    · exact hchart _ 0
    · exact correction_map P p q β t f hchart hlast _ _
  have hD (r s : I) :
      f ((((Path.Homotopy.refl (CoefficientBassRaw1PolynomialPairCone.leftPath P β p q)).hcomp
        (CoefficientBassRaw1PolynomialPairCone.correction P β p q)).hcomp
        ((Path.Homotopy.refl (Path.refl
          (CoefficientBassRaw1PolynomialPairCone.tip P β p q))).symm)) (r, s)) =
      (((Path.Homotopy.refl (leftPath P p q)).hcomp (correction P p q)).hcomp
        ((Path.Homotopy.refl (Path.refl (endTip P p q))).symm)) (r, s) t := by
    rw [Path.Homotopy.hcomp_apply, Path.Homotopy.hcomp_apply]
    split_ifs
    · exact hC _ _
    · exact htip
  unfold CoefficientBassRaw1PolynomialPairCone.correctedBoundary correctedBoundary
  rw [Path.Homotopy.trans_apply, Path.Homotopy.trans_apply]
  split_ifs
  · exact hB _ _
  · exact hD _ _

include hchart hlast hinitial in
private theorem corrected_map (r s : I) :
    f (CoefficientBassRaw1PolynomialPairCone.corrected P β p q (r, s)) =
      corrected P p q (r, (s, t)) := by
  obtain ⟨z, hz⟩ := ThreeSideSquare.collapse_surjective (r, s)
  have hh := (congrArg f
    (CoefficientBassRaw1PolynomialPairCone.corrected_collapse P β p q z)).trans
      ((boundary_map P p q β t f hchart hlast hinitial z.1 z.2).trans
        (corrected_collapse P p q z t).symm)
  simpa only [hz] using hh

/-- The full positive corrected cap is the original frozen M side, before native evaluation. -/
theorem plus_corrected (r s : I) :
    plus P p q (CoefficientBassRaw1PolynomialPairCone.corrected P
      (underToLaurent R) p q (r, s)) = corrected P p q (r, (s, 0)) :=
  corrected_map P p q (underToLaurent R) 0 (plus P p q)
    (plus_chartSquare P p q) (plus_last P p q) (plus_initial P p q) r s

/-- The inverse corrected cap keeps its independent full chart and all original clocks. -/
theorem minus_corrected (r s : I) :
    minus P p q (CoefficientBassRaw1PolynomialPairCone.corrected P
      (underToLaurentInvert R) p q (r, s)) = corrected P p q (r, (s, 1)) :=
  corrected_map P p q (underToLaurentInvert R) 1 (minus P p q)
    (minus_chartSquare P p q) (minus_last P p q) (minus_initial P p q) r s

end Quillen.PerfectComplexes.BassMWholeConeCarrier.PairProjection
