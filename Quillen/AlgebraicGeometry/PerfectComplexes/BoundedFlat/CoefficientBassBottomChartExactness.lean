/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeMiddleExactness
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassOriginalNegativeComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientTwoChartStableSequence

/-!
# Exactness of the original finite-stage bottom chart rows

The original negative-group comparison carries the proved whole natural middle row to the
actual fine spectral chart complex in degree minus the stage. Consequently its original right
Bass term vanishes and the original left quotient arrow is invertible at every bottom degree.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart Quillen.Bass.TwoChartStable
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable (a : Under R)

/-- The original negative-group comparison retains both actual spectral middle arrows. -/
def boundedFlatCoefficientBottomChartIso (i : ℕ) :
    (middleComplex (polynomialUnderCoefficient R) (underToLaurent R)
      (underToLaurentInvert R) (boundedFlatCoefficientCommonCorner (R := R))
      (boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i)).map
        ((evaluation (Under R) AddCommGrpCat).obj a) ≅
      chartComplex ((boundedFlatCoefficientAmbientBassDiagram P i).mapArrow.mapArrow.obj
        (laurentUnderSquare R a)) (-(i : ℤ)) := by
  let e := boundedFlatCoefficientAmbientNegativeKComparison P i
  let K := boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i
  let F := boundedFlatCoefficientAmbientBassDiagram P i ⋙
    stableHomotopyFunctor (-(i : ℤ))
  refine ShortComplex.isoMk (e.app a)
    (biprod.mapIso (e.app ((polynomialUnderFunctor R).obj a))
      (e.app ((polynomialUnderFunctor R).obj a)))
    (e.app ((laurentUnderFunctor R).obj a)) ?_ ?_
  · change e.hom.app a ≫ biprod.lift
      (F.map ((polynomialUnderCoefficient R).app a))
      (F.map ((polynomialUnderCoefficient R).app a)) =
        biprod.lift (K.map ((polynomialUnderCoefficient R).app a))
          (K.map ((polynomialUnderCoefficient R).app a)) ≫
            biprod.map (e.hom.app _) (e.hom.app _)
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, Category.assoc,
        biprod.map_fst (e.hom.app ((polynomialUnderFunctor R).obj a))
          (e.hom.app ((polynomialUnderFunctor R).obj a)), biprod.lift_fst_assoc]
      exact (e.hom.naturality ((polynomialUnderCoefficient R).app a)).symm
    · rw [Category.assoc, biprod.lift_snd, Category.assoc,
        biprod.map_snd (e.hom.app ((polynomialUnderFunctor R).obj a))
          (e.hom.app ((polynomialUnderFunctor R).obj a)), biprod.lift_snd_assoc]
      exact (e.hom.naturality ((polynomialUnderCoefficient R).app a)).symm
  · change biprod.map (e.hom.app _) (e.hom.app _) ≫
      biprod.desc (F.map ((underToLaurent R).app a))
        (-F.map ((underToLaurentInvert R).app a)) =
      biprod.desc (K.map ((underToLaurent R).app a))
        (-K.map ((underToLaurentInvert R).app a)) ≫ e.hom.app _
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
      exact (e.hom.naturality ((underToLaurent R).app a)).symm
    · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc,
        Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg (e.hom.naturality ((underToLaurentInvert R).app a)).symm

variable [QuasiSeparatedSpace P.left]

/-- The unchanged finite-stage chart complex is exact in its actual bottom degree. -/
theorem boundedFlatCoefficientBottomChart_exact (i : ℕ) :
    (chartComplex ((boundedFlatCoefficientAmbientBassDiagram P i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) (-(i : ℤ))).Exact :=
  ShortComplex.exact_of_iso (boundedFlatCoefficientBottomChartIso P a i)
    ((boundedFlatCoefficientNegativeMiddle_exact P i).map
      ((evaluation (Under R) AddCommGrpCat).obj a))

/-- The original right Bass term vanishes at every genuine finite-stage bottom degree. -/
theorem boundedFlatCoefficientBottomBassRight_isZero (i : ℕ) :
    IsZero (bassRightGroup
      ((boundedFlatCoefficientAmbientBassDiagram P i).mapArrow.mapArrow.obj
        (laurentUnderSquare R a)) (-(i : ℤ))) :=
  bassRightGroup_isZero_of_chart_exact _ _
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (boundedFlatCoefficientBottomChart_exact P a i))

/-- The actual left quotient arrow is invertible at every finite-stage bottom degree. -/
instance boundedFlatCoefficientBottomBassLeft_isIso (i : ℕ) :
    IsIso (boundedFlatCoefficientAmbientTwoChartSequence P i a (-(i : ℤ))).f :=
  (boundedFlatCoefficientAmbientTwoChartSequence_shortExact P i a (-(i : ℤ))).isIso_f_iff.mpr
    (boundedFlatCoefficientBottomBassRight_isZero P a i)

end Quillen.PerfectComplexes
