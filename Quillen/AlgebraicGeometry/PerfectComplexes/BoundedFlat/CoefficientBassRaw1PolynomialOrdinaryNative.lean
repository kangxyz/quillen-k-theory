/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialOrdinaryNativeCells
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeExt

/-! Both genuine polynomial sheets enter the original ordinary cone
on the actual projected input. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialOrdinaryMap
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference CoefficientBassRaw1PolynomialSourceProjection
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "E" => input P p q w
local notation "F" => CoefficientBassRaw1PolynomialSourceProjection.polynomial P p q w
local notation "A" => sourceProjection P (a := a)
local notation "Jd" => targetProjection P (d := d)

/-- The entire plus sheet has its original native value on the genuine projected input. -/
theorem plus_native (n : ℕ)
    (z : CoefficientBassRaw1PolynomialPostcomp.carrier P p q w (underToLaurent R))
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    FourEdge.coneEval P d E n (plus P p q w z) x =
      (boundedFlatCoefficientBassPositiveConeInclusion P d).map n
        (CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w (underToLaurent R) n z
          ((prespectrumMap A).map n x)) := by
  let J := BassMWholeNerve.coefficientModel P ((underToLaurent R).app d)
  have h : (fun z ↦ FourEdge.coneEval P d E n (plus P p q w z) x) =
      (fun z ↦ (boundedFlatCoefficientBassPositiveConeInclusion P d).map n
        (CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w (underToLaurent R) n z
          ((prespectrumMap A).map n x))) := by
    apply FourEdgeTree.SetDescent.funext (attaching F J (F ≫ J) (Iso.refl _)) (erase F)
    · rintro ⟨y, ⟨t⟩⟩
      dsimp only [plus]
      rw [map_cylinder, FourEdge.coneEval_cylinder, evaluate_cylinder]
      change ReducedMappingCone.cylinder _ _
        ((boundedFlatCoefficientBassSquareComparison P d).map n)
          (t, FourEdgeTree.nativeEval E Jd n
            (SSet.toTop.map (FourEdgeTree.plusVertex E Jd) (polynomial P p q w y)) x) = _
      rw [FourEdgeTree.nativeEval_plus]
      dsimp only [FourEdgeTree.nativePlus]
      rw [polynomial_native]
      rfl
    · intro y
      change FourEdge.coneEval P d E n
        (plus P p q w (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y)) x =
          (boundedFlatCoefficientBassPositiveConeInclusion P d).map n
            (CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w (underToLaurent R) n
              (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y)
              ((prespectrumMap A).map n x))
      dsimp only [plus]
      rw [map_laurent P p q w (underToLaurent R) (laurentPlus_projection P d)
        (FourEdgeTree.plusVertex E Jd) (FourEdge.beta_plus P d E),
        FourEdge.coneEval_laurent, evaluate_laurent]
      change (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P d)).map n
        (pointwisePrespectrumFamily _ n (laurent P p q w (underToLaurent R) _ y) x) = _
      rw [laurent_native]
      rfl
    · intro y
      have hy : y = (default : |tipSSet.{u+1}|) := Subsingleton.elim _ _
      subst y
      change FourEdge.coneEval P d E n
        (plus P p q w (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) default)) x =
          (boundedFlatCoefficientBassPositiveConeInclusion P d).map n
            (CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w (underToLaurent R) n
              (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) default)
              ((prespectrumMap A).map n x))
      dsimp only [plus]
      rw [map_tip P p q w (underToLaurent R) (laurentPlus_projection P d)
        (FourEdgeTree.plusVertex E Jd) (FourEdge.beta_plus P d E),
        FourEdge.coneEval_tip, evaluate_tip]
      exact ((boundedFlatCoefficientBassPositiveConeInclusion P d).map_point n).symm
  exact congrFun h z

/-- The entire minus sheet has its original native value on the genuine projected input. -/
theorem minus_native (n : ℕ)
    (z : CoefficientBassRaw1PolynomialPostcomp.carrier P p q w (underToLaurentInvert R))
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    FourEdge.coneEval P d E n (minus P p q w z) x =
      (boundedFlatCoefficientBassNegativeConeInclusion P d).map n
        (CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w (underToLaurentInvert R) n z
          ((prespectrumMap A).map n x)) := by
  let J := BassMWholeNerve.coefficientModel P ((underToLaurentInvert R).app d)
  have h : (fun z ↦ FourEdge.coneEval P d E n (minus P p q w z) x) =
      (fun z ↦ (boundedFlatCoefficientBassNegativeConeInclusion P d).map n
        (CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w (underToLaurentInvert R) n z
          ((prespectrumMap A).map n x))) := by
    apply FourEdgeTree.SetDescent.funext (attaching F J (F ≫ J) (Iso.refl _)) (erase F)
    · rintro ⟨y, ⟨t⟩⟩
      dsimp only [minus]
      rw [map_cylinder, FourEdge.coneEval_cylinder, evaluate_cylinder]
      change ReducedMappingCone.cylinder _ _
        ((boundedFlatCoefficientBassSquareComparison P d).map n)
          (t, FourEdgeTree.nativeEval E Jd n
            (SSet.toTop.map (FourEdgeTree.minusVertex E Jd) (polynomial P p q w y)) x) = _
      rw [FourEdgeTree.nativeEval_minus]
      dsimp only [FourEdgeTree.nativeMinus]
      rw [polynomial_native]
      rfl
    · intro y
      change FourEdge.coneEval P d E n
        (minus P p q w (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y)) x =
          (boundedFlatCoefficientBassNegativeConeInclusion P d).map n
            (CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w (underToLaurentInvert R) n
              (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y)
              ((prespectrumMap A).map n x))
      dsimp only [minus]
      rw [map_laurent P p q w (underToLaurentInvert R) (laurentMinus_projection P d)
        (FourEdgeTree.minusVertex E Jd) (FourEdge.beta_minus P d E),
        FourEdge.coneEval_laurent, evaluate_laurent]
      change (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P d)).map n
        (pointwisePrespectrumFamily _ n (laurent P p q w (underToLaurentInvert R) _ y) x) = _
      rw [laurent_native]
      rfl
    · intro y
      have hy : y = (default : |tipSSet.{u+1}|) := Subsingleton.elim _ _
      subst y
      change FourEdge.coneEval P d E n
        (minus P p q w (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) default)) x =
          (boundedFlatCoefficientBassNegativeConeInclusion P d).map n
            (CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w (underToLaurentInvert R) n
              (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) default)
              ((prespectrumMap A).map n x))
      dsimp only [minus]
      rw [map_tip P p q w (underToLaurentInvert R) (laurentMinus_projection P d)
        (FourEdgeTree.minusVertex E Jd) (FourEdge.beta_minus P d E),
        FourEdge.coneEval_tip, evaluate_tip]
      exact ((boundedFlatCoefficientBassNegativeConeInclusion P d).map_point n).symm
  exact congrFun h z

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialOrdinaryMap
