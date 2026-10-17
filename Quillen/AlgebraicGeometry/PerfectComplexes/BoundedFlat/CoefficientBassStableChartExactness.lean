/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSplitExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientKStableComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientTwoChartStableSequence

/-!
# Original connective chart exactness in the actual fine Bass spectrum

The actual natural K/stable comparison carries the unchanged common corner and signed chart
difference to the original fine coefficient spectral row. Its right term therefore vanishes in
every connective degree, and its original left arrow is an isomorphism. This retains the
original Laurent quotient, cone inclusion and signed parameter shift; seed identification is a
separate comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CommRingCat.PolynomialLaurent Quillen.LoopPrespectrum
open Quillen.Bass.TwoChartStable AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable [QuasiSeparatedSpace P.left] (a : Under R)

/-- The original K-row and the actual stage-zero spectral chart row are isomorphic via the
unchanged natural K/stable comparison on each corner. -/
def boundedFlatCoefficientConnectiveChartIso (n : ℕ) :
    (boundedFlatCoefficientMiddleSequence P n).map
        ((evaluation (Under R) AddCommGrpCat).obj a) ≅
      chartComplex ((boundedFlatCoefficientAmbientBassDiagram P 0).mapArrow.mapArrow.obj
        (laurentUnderSquare R a)) (n : ℤ) := by
  let e := boundedFlatCoefficientSectionKStableNatIso P n
  let K := boundedFlatCoefficientKAddFunctor P n
  let F := row P ⋙ boundedFlatCoefficientSectionPrespectrumFunctor R ⋙
    stableHomotopyFunctor (n : ℤ)
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

/-- The unchanged fine spectral chart complex is exact in every connective degree. -/
theorem boundedFlatCoefficientConnectiveChart_exact (n : ℕ) :
    (chartComplex ((boundedFlatCoefficientAmbientBassDiagram P 0).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) (n : ℤ)).Exact :=
  ShortComplex.exact_of_iso (boundedFlatCoefficientConnectiveChartIso P a n)
    (boundedFlatCoefficientMiddleSequence_evaluation_exact P n a)

/-- The actual right term vanishes, including degree zero, for every compact quasi-separated row.
-/
theorem boundedFlatCoefficientConnectiveBassRight_isZero (n : ℕ) :
    IsZero (bassRightGroup
      ((boundedFlatCoefficientAmbientBassDiagram P 0).mapArrow.mapArrow.obj
        (laurentUnderSquare R a)) (n : ℤ)) :=
  bassRightGroup_isZero_of_chart_exact _ _
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (boundedFlatCoefficientConnectiveChart_exact P a n))

/-- The original spectral left map, with its unchanged quotient and shift, is an isomorphism. -/
instance boundedFlatCoefficientConnectiveBassLeft_isIso (n : ℕ) :
    IsIso (boundedFlatCoefficientAmbientTwoChartSequence P 0 a (n : ℤ)).f :=
  (boundedFlatCoefficientAmbientTwoChartSequence_shortExact P 0 a (n : ℤ)).isIso_f_iff.mpr
    (boundedFlatCoefficientConnectiveBassRight_isZero P a n)

end Quillen.PerfectComplexes
