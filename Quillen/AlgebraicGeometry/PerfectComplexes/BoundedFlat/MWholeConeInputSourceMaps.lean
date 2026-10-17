/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputSourceParameters
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputPolynomialNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePairCorrected

/-! The whole source endpoint action equals the original central map on both genuine sheets. -/
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
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
namespace InputCentral
local notation "A" => normalizedMap (coefficientMap P p)
local notation "E" => inputReference P q w
local notation "F" => TripleLaurent.input P p q w
local notation "Jd" => normalizedMap (polynomialProjection P d)

/-- The exact source precomposition and right-first transport on the entire ordinary tree. -/
def treeMap : C(FourEdgeTree.space E Jd, FourEdgeTree.space F Jd) :=
  (FourEdge.Reanchor.tree P d (A ≫ E) F (TripleLaurent.inputIso P p q w)).comp
    (FourEdge.Precomp.tree P d A E)

theorem carrierMap_cylinder (y : FourEdgeTree.space E Jd) (h : I) :
    carrierMap P p q w (FourEdgeTree.cylinder E Jd (reference P d E)
      (FourEdge.beta P d E) (y, h)) =
    FourEdgeTree.cylinder F Jd (reference P d F) (FourEdge.beta P d F)
      (treeMap P p q w y, h) := by
  dsimp only [carrierMap, ContinuousMap.comp_apply]
  rw [FourEdge.Precomp.cone_cylinder, FourEdge.Reanchor.cone_cylinder]
  rfl

theorem treeMap_plus (y : |parameterSSet (E ≫ Jd)|) :
    treeMap P p q w (SSet.toTop.map (FourEdgeTree.plusVertex E Jd) y) =
    SSet.toTop.map (FourEdgeTree.plusVertex F Jd)
      (mapParameter (CommonReferenceProduct.reanchor
        (isoWhiskerRight (TripleLaurent.inputIso P p q w) (Jd).functor))
        (mapParameter (precompNode A) y)) := by
  dsimp only [treeMap, ContinuousMap.comp_apply]
  rw [FourEdge.Precomp.tree_plus, FourEdge.Reanchor.tree_plus]; rfl

theorem treeMap_minus (y : |parameterSSet (E ≫ Jd)|) :
    treeMap P p q w (SSet.toTop.map (FourEdgeTree.minusVertex E Jd) y) =
    SSet.toTop.map (FourEdgeTree.minusVertex F Jd)
      (mapParameter (CommonReferenceProduct.reanchor
        (isoWhiskerRight (TripleLaurent.inputIso P p q w) (Jd).functor))
        (mapParameter (precompNode A) y)) := by
  dsimp only [treeMap, ContinuousMap.comp_apply]
  rw [FourEdge.Precomp.tree_minus, FourEdge.Reanchor.tree_minus]; rfl

end InputCentral
namespace InputPolynomial
local notation "D" => sourceReference P p
local notation "F" => pairReference P q w

/-- The entire plus sheet at the original source endpoint agrees before native evaluation. -/
theorem plus_source_one
    (z : CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurent R) q w) :
    plusPlace P p q w (FiniteSourceSheet.action D F
      (BassMWholeNerve.coefficientModel P ((underToLaurent R).app d))
      (CoefficientSquareFamilies.polynomialNodes P p)
      (z, NativeSquareFiveSimplex.parameter 1)) =
    InputCentral.carrierMap P p q w (PairProjection.plus P q w z) := by
  let J := BassMWholeNerve.coefficientModel P ((underToLaurent R).app d)
  have h : (fun z ↦ plusPlace P p q w (FiniteSourceSheet.action D F J
      (CoefficientSquareFamilies.polynomialNodes P p)
      (z, NativeSquareFiveSimplex.parameter 1))) =
      (fun z ↦ InputCentral.carrierMap P p q w (PairProjection.plus P q w z)) := by
    apply FourEdgeTree.SetDescent.funext (attaching F J (F ≫ J) (Iso.refl _)) (erase F)
    · rintro ⟨y, ⟨t⟩⟩
      rw [FiniteSourceSheet.action_cylinder]
      have hp := place_cylinder P p q w (underToLaurent R) (laurentPlus_projection P d)
        (FourEdgeTree.plusVertex (input P p q w) (targetProjection P (d := d)))
        (FourEdge.beta_plus P d (input P p q w))
        (FiniteSourceSheet.polynomial D F (CoefficientSquareFamilies.polynomialNodes P p)
          (y, NativeSquareFiveSimplex.parameter 1)) t
      have hq := PairProjection.map_cylinder P q w (underToLaurent R) (laurentPlus_projection P d)
        (FourEdgeTree.plusVertex (inputReference P q w)
          (normalizedMap (polynomialProjection P d)))
        (FourEdge.beta_plus P d (inputReference P q w)) y t
      dsimp only [plusPlace, FiniteSourceSheet.targetCylinder,
        PairProjection.plus, ContinuousMap.coe_mk]
      rw [hp, hq, InputCentral.carrierMap_cylinder P p q w]
      dsimp only [placementVertex, PairProjection.vertex, ContinuousMap.comp_apply]
      change FourEdgeTree.cylinder _ _ _ _
        (SSet.toTop.map (FourEdgeTree.plusVertex (input P p q w)
          (targetProjection P (d := d)))
          (polynomialPlacement P p q w
            (FiniteSourceSheet.polynomial D F (CoefficientSquareFamilies.polynomialNodes P p)
              (y, NativeSquareFiveSimplex.parameter 1))), t) =
        FourEdgeTree.cylinder _ _ _ _
          (InputCentral.treeMap P p q w
            (SSet.toTop.map (FourEdgeTree.plusVertex (inputReference P q w)
              (normalizedMap (polynomialProjection P d))) (PairProjection.polynomial P q w y)), t)
      rw [InputCentral.treeMap_plus, polynomial_parameter4]
    · intro y
      change plusPlace P p q w (FiniteSourceSheet.action D F J
        (CoefficientSquareFamilies.polynomialNodes P p)
        (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y,
          NativeSquareFiveSimplex.parameter 1)) = _
      rw [FiniteSourceSheet.action_laurent]
      have hp := place_laurent P p q w (underToLaurent R) (laurentPlus_projection P d)
        (FourEdgeTree.plusVertex (input P p q w) (targetProjection P (d := d)))
        (FourEdge.beta_plus P d (input P p q w))
        (FiniteSourceSheet.laurent D F J (CoefficientSquareFamilies.polynomialNodes P p)
          (y, NativeSquareFiveSimplex.parameter 1))
      have hq := PairProjection.map_laurent P q w (underToLaurent R) (laurentPlus_projection P d)
        (FourEdgeTree.plusVertex (inputReference P q w)
          (normalizedMap (polynomialProjection P d)))
        (FourEdge.beta_plus P d (inputReference P q w)) y
      dsimp only [plusPlace, FiniteSourceSheet.targetLaurent, PairProjection.plus]
      erw [hp, hq, InputCentral.carrierMap_laurent P p q w,
        laurent_parameter4 P p q w (underToLaurent R) (laurentPlus_projection P d)]
    · intro y
      have hy : y = (default : |tipSSet.{u+1}|) := Subsingleton.elim _ _
      subst y
      change plusPlace P p q w (FiniteSourceSheet.action D F J
        (CoefficientSquareFamilies.polynomialNodes P p)
        (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) default,
          NativeSquareFiveSimplex.parameter 1)) = _
      rw [FiniteSourceSheet.action_tip]
      have hp := place_tip P p q w (underToLaurent R) (laurentPlus_projection P d)
        (FourEdgeTree.plusVertex (input P p q w) (targetProjection P (d := d)))
        (FourEdge.beta_plus P d (input P p q w))
      have hq := PairProjection.map_tip P q w (underToLaurent R) (laurentPlus_projection P d)
        (FourEdgeTree.plusVertex (inputReference P q w)
          (normalizedMap (polynomialProjection P d)))
        (FourEdge.beta_plus P d (inputReference P q w))
      dsimp only [plusPlace, FiniteSourceSheet.targetTip, PairProjection.plus]
      erw [hp, hq, InputCentral.carrierMap_tip P p q w]
  exact congrFun h z

/-- The chosen plus corrected cap meets the same central cap with every old height unchanged. -/
theorem plusFamily_one (r h : I) :
    plusFamily P p q w ((r, h), 1) = InputCentral.family P p q w (r, (h, 0)) := by
  change plusPlace P p q w (FiniteSourceSheet.action D F
    (BassMWholeNerve.coefficientModel P ((underToLaurent R).app d))
    (CoefficientSquareFamilies.polynomialNodes P p)
    (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) q w (r, h),
      NativeSquareFiveSimplex.parameter 1)) = _
  rw [plus_source_one, PairProjection.plus_corrected]
  rfl

/-- The entire minus sheet at the original source endpoint agrees before native evaluation. -/
theorem minus_source_one
    (z : CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurentInvert R) q w) :
    minusPlace P p q w (FiniteSourceSheet.action D F
      (BassMWholeNerve.coefficientModel P ((underToLaurentInvert R).app d))
      (CoefficientSquareFamilies.polynomialNodes P p)
      (z, NativeSquareFiveSimplex.parameter 1)) =
    InputCentral.carrierMap P p q w (PairProjection.minus P q w z) := by
  let J := BassMWholeNerve.coefficientModel P ((underToLaurentInvert R).app d)
  have h : (fun z ↦ minusPlace P p q w (FiniteSourceSheet.action D F J
      (CoefficientSquareFamilies.polynomialNodes P p)
      (z, NativeSquareFiveSimplex.parameter 1))) =
      (fun z ↦ InputCentral.carrierMap P p q w (PairProjection.minus P q w z)) := by
    apply FourEdgeTree.SetDescent.funext (attaching F J (F ≫ J) (Iso.refl _)) (erase F)
    · rintro ⟨y, ⟨t⟩⟩
      rw [FiniteSourceSheet.action_cylinder]
      have hp := place_cylinder P p q w (underToLaurentInvert R) (laurentMinus_projection P d)
        (FourEdgeTree.minusVertex (input P p q w) (targetProjection P (d := d)))
        (FourEdge.beta_minus P d (input P p q w))
        (FiniteSourceSheet.polynomial D F (CoefficientSquareFamilies.polynomialNodes P p)
          (y, NativeSquareFiveSimplex.parameter 1)) t
      have hq := PairProjection.map_cylinder P q w (underToLaurentInvert R)
        (laurentMinus_projection P d)
        (FourEdgeTree.minusVertex (inputReference P q w)
          (normalizedMap (polynomialProjection P d)))
        (FourEdge.beta_minus P d (inputReference P q w)) y t
      dsimp only [minusPlace, FiniteSourceSheet.targetCylinder,
        PairProjection.minus, ContinuousMap.coe_mk]
      rw [hp, hq, InputCentral.carrierMap_cylinder P p q w]
      dsimp only [placementVertex, PairProjection.vertex, ContinuousMap.comp_apply]
      change FourEdgeTree.cylinder _ _ _ _
        (SSet.toTop.map (FourEdgeTree.minusVertex (input P p q w)
          (targetProjection P (d := d)))
          (polynomialPlacement P p q w
            (FiniteSourceSheet.polynomial D F (CoefficientSquareFamilies.polynomialNodes P p)
              (y, NativeSquareFiveSimplex.parameter 1))), t) =
        FourEdgeTree.cylinder _ _ _ _
          (InputCentral.treeMap P p q w
            (SSet.toTop.map (FourEdgeTree.minusVertex (inputReference P q w)
              (normalizedMap (polynomialProjection P d))) (PairProjection.polynomial P q w y)), t)
      rw [InputCentral.treeMap_minus, polynomial_parameter4]
    · intro y
      change minusPlace P p q w (FiniteSourceSheet.action D F J
        (CoefficientSquareFamilies.polynomialNodes P p)
        (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y,
          NativeSquareFiveSimplex.parameter 1)) = _
      rw [FiniteSourceSheet.action_laurent]
      have hp := place_laurent P p q w (underToLaurentInvert R) (laurentMinus_projection P d)
        (FourEdgeTree.minusVertex (input P p q w) (targetProjection P (d := d)))
        (FourEdge.beta_minus P d (input P p q w))
        (FiniteSourceSheet.laurent D F J (CoefficientSquareFamilies.polynomialNodes P p)
          (y, NativeSquareFiveSimplex.parameter 1))
      have hq := PairProjection.map_laurent P q w (underToLaurentInvert R)
        (laurentMinus_projection P d)
        (FourEdgeTree.minusVertex (inputReference P q w)
          (normalizedMap (polynomialProjection P d)))
        (FourEdge.beta_minus P d (inputReference P q w)) y
      dsimp only [minusPlace, FiniteSourceSheet.targetLaurent, PairProjection.minus]
      erw [hp, hq, InputCentral.carrierMap_laurent P p q w,
        laurent_parameter4 P p q w (underToLaurentInvert R) (laurentMinus_projection P d)]
    · intro y
      have hy : y = (default : |tipSSet.{u+1}|) := Subsingleton.elim _ _
      subst y
      change minusPlace P p q w (FiniteSourceSheet.action D F J
        (CoefficientSquareFamilies.polynomialNodes P p)
        (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) default,
          NativeSquareFiveSimplex.parameter 1)) = _
      rw [FiniteSourceSheet.action_tip]
      have hp := place_tip P p q w (underToLaurentInvert R) (laurentMinus_projection P d)
        (FourEdgeTree.minusVertex (input P p q w) (targetProjection P (d := d)))
        (FourEdge.beta_minus P d (input P p q w))
      have hq := PairProjection.map_tip P q w (underToLaurentInvert R)
        (laurentMinus_projection P d)
        (FourEdgeTree.minusVertex (inputReference P q w)
          (normalizedMap (polynomialProjection P d)))
        (FourEdge.beta_minus P d (inputReference P q w))
      dsimp only [minusPlace, FiniteSourceSheet.targetTip, PairProjection.minus]
      erw [hp, hq, InputCentral.carrierMap_tip P p q w]
  exact congrFun h z

/-- The chosen minus corrected cap meets the same central cap with every old height unchanged. -/
theorem minusFamily_one (r h : I) :
    minusFamily P p q w ((r, h), 1) = InputCentral.family P p q w (r, (h, 1)) := by
  change minusPlace P p q w (FiniteSourceSheet.action D F
    (BassMWholeNerve.coefficientModel P ((underToLaurentInvert R).app d))
    (CoefficientSquareFamilies.polynomialNodes P p)
    (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) q w (r, h),
      NativeSquareFiveSimplex.parameter 1)) = _
  rw [minus_source_one, PairProjection.minus_corrected]
  rfl

end InputPolynomial
end Quillen.PerfectComplexes.BassMWholeConeCarrier
