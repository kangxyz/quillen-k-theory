/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassStableChartExactness
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassForwardQuotient
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassTransitionKOperation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationSeedComparison

/-!
# Connective invertibility of the original raw coefficient Bass transition

The original forward-unit quotient is an isomorphism with its genuine minus sign. The actual
fine spectral left map is an isomorphism by global chart exactness. Their composite agrees
with the original raw transition through the unchanged Laurent inclusion, actual cone
evaluation and signed parameter-loop shift. Thus the actual raw map is invertible in all
nonnegative degrees on compact quasi-separated coefficient schemes, including degree zero.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Bass.TwoChart
open Quillen.Bass.TwoChartStable
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Waldhausen.Additivity.KCommGroup
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
local notation "S" =>
  Functor.obj (Functor.mapArrow (Functor.mapArrow
    (boundedFlatCoefficientAmbientBassDiagram P 0))) (laurentUnderSquare R a)
local notation "hS" => boundedFlatCoefficientAmbientTwoChartSpectralConditions P 0 a

/-- The original K/stable natural comparison identifies the unchanged two-chart quotients. -/
def boundedFlatCoefficientConnectiveQuotientIso (n : ℕ) :
    (contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientKAddFunctor P (n + 1))).obj a ≅
        (contraction (underToLaurent R) (underToLaurentInvert R)
          (row P ⋙ boundedFlatCoefficientSectionPrespectrumFunctor R ⋙
            stableHomotopyFunctor ((n + 1 : ℕ) : ℤ))).obj a :=
  ((contractionFunctor (underToLaurent R) (underToLaurentInvert R)).mapIso
    (boundedFlatCoefficientSectionKStableNatIso P (n + 1))).app a

attribute [local irreducible] boundedFlatCoefficientConnectiveQuotientIso
  boundedFlatCoefficientSectionKStableNatIso

/-- Original Laurent representatives pass through the actual fine left arrow, signed shift,
and cone evaluation by the same original geometric inclusion. -/
theorem boundedFlatCoefficientForwardQuotient_to_raw (n : ℕ) :
    (boundedFlatCoefficientForwardUnitQuotient P n).app a ≫
      (boundedFlatCoefficientConnectiveQuotientIso P a n).hom ≫
      bassLeft S hS (n : ℤ) ≫ (bassShift S (n : ℤ)).hom ≫
      (stableHomotopyFunctor ((n : ℤ) + 1)).map
        (boundedFlatCoefficientFullOpenBassConeEvaluation (𝟙 P) a) =
    (boundedFlatCoefficientForwardUnitSection P n).app a ≫
      (boundedFlatCoefficientSectionKStableNatIso P (n + 1)).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
        (boundedFlatCoefficientSectionEvaluationPrespectrumMap
          (op P, (laurentUnderFunctor R).obj a)) ≫
      (stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) := by
  simp only [boundedFlatCoefficientForwardUnitQuotient, NatTrans.comp_app, Category.assoc,
    boundedFlatCoefficientConnectiveQuotientIso, Iso.app_hom, Functor.mapIso_hom]
  dsimp only [contractionFunctor]
  rw [contractionMap_π_assoc]
  dsimp only [contractionπ]
  have hb := bassLeft_π_shift S hS (n : ℤ)
  change cokernel.π (polynomialDifference (underToLaurent R) (underToLaurentInvert R)
      (row P ⋙ boundedFlatCoefficientSectionPrespectrumFunctor R ⋙
        stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)) a) ≫
      bassLeft S hS (n : ℤ) ≫ (bassShift S (n : ℤ)).hom = _ at hb
  have hbr := congrArg (fun f => f ≫ (stableHomotopyFunctor ((n : ℤ) + 1)).map
    (boundedFlatCoefficientFullOpenBassConeEvaluation (𝟙 P) a)) hb
  simp only [Category.assoc] at hbr
  have he := boundedFlatCoefficientFullOpenBassConeEvaluation_inclusion (𝟙 P) a
  change mappingConeInclusion (StrictSquare.comparison S) ≫
    boundedFlatCoefficientFullOpenBassConeEvaluation (𝟙 P) a = _ at he
  rw [hbr, ← Functor.map_comp, he, Functor.map_comp]
  exact Eq.refl _

/-- The named original comparison has exactly the original K/stable value. -/
theorem boundedFlatPerfectKLocalizedStableIso_hom_apply (n : ℕ) (X : Scheme.{u})
    (x : BoundedFlatPerfectK X n) :
    (boundedFlatPerfectKLocalizedStableIso n (op X)).hom (Additive.ofMul x) =
      originalKStableEquiv (boundedFlatPerfectWaldhausen X) n (Additive.ofMul x) := rfl

/-- Original fine evaluation of the actual forward unit has the original K-operation value. -/
theorem boundedFlatCoefficientSectionKStable_forward_evaluation (n : ℕ)
    (x : BoundedFlatPerfectK (space (op P, a)) n) :
    (stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap
        (op P, (laurentUnderFunctor R).obj a))
      ((boundedFlatCoefficientSectionKStableNatIso P (n + 1)).hom.app
        ((laurentUnderFunctor R).obj a)
        ((boundedFlatCoefficientForwardUnitSection P n).app a (Additive.ofMul x))) =
    originalKStableEquiv (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a))) (n + 1)
      (Additive.ofMul (boundedFlatCoefficientLaurentKOperation P a n x)) :=
  ConcreteCategory.congr_hom
    (boundedFlatCoefficientSectionKStableNatIso_evaluation P (n + 1)
      ((laurentUnderFunctor R).obj a))
    ((boundedFlatCoefficientForwardUnitSection P n).app a (Additive.ofMul x))

/-- The original raw transition equals the actual forward quotient and original fine left map,
after the same original signed shift and actual cone evaluation. -/
theorem boundedFlatCoefficientBassTransition_connective_comparison (n : ℕ) :
    (boundedFlatPerfectKLocalizedStableIso n (op (space (op P, a)))).hom ≫
      (stableHomotopyFunctor (n : ℤ)).map (boundedFlatCoefficientBassTransition P a) ≫
      (parameterStableHomotopyIso
        (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) (n : ℤ)).hom =
    (boundedFlatCoefficientForwardUnitQuotient P n).app a ≫
      (boundedFlatCoefficientConnectiveQuotientIso P a n).hom ≫
      bassLeft S hS (n : ℤ) ≫ (bassShift S (n : ℤ)).hom ≫
      (stableHomotopyFunctor ((n : ℤ) + 1)).map
        (boundedFlatCoefficientFullOpenBassConeEvaluation (𝟙 P) a) := by
  apply AddCommGrpCat.ext
  intro x
  have hs := boundedFlatPerfectKLocalizedStableIso_hom_apply n (space (op P, a)) x.toMul
  have hsr := congrArg (fun z =>
    (parameterStableHomotopyIso
      (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) (n : ℤ)).hom
      ((stableHomotopyFunctor (n : ℤ)).map
        (boundedFlatCoefficientBassTransition P a) z)) hs
  have hp := congrArg ((stableHomotopyFunctor ((n : ℤ) + 1)).map
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)))
      (boundedFlatCoefficientSectionKStable_forward_evaluation P a n x.toMul)
  have hr := ConcreteCategory.congr_hom
    (boundedFlatCoefficientForwardQuotient_to_raw P a n) x
  exact hsr.trans ((boundedFlatCoefficientBassTransition_originalK_shift P a n x.toMul).trans
    (hp.symm.trans hr.symm))

private theorem isIso_of_conjugate {C : Type*} [Category C] {A B E F : C}
    (u : A ≅ B) (v : E ≅ F) (f : B ⟶ E) {g : A ⟶ F} [IsIso g]
    (h : u.hom ≫ f ≫ v.hom = g) : IsIso f := by
  let : IsIso (u.hom ≫ f ≫ v.hom) := by rw [h]; infer_instance
  let : IsIso (f ≫ v.hom) := IsIso.of_isIso_comp_left u.hom _
  exact IsIso.of_isIso_comp_right _ v.hom

variable [CompactSpace P.left] [QuasiSeparatedSpace P.left]

/-- The actual raw coefficient Bass transition is invertible in every connective degree. -/
instance boundedFlatCoefficientBassTransition_connective_isIso (n : ℕ) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      (boundedFlatCoefficientBassTransition P a)) := by
  let u := boundedFlatPerfectKLocalizedStableIso n (op (space (op P, a)))
  let r := parameterStableHomotopyIso
    (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) (n : ℤ)
  let : IsIso ((stableHomotopyFunctor ((n : ℤ) + 1)).map
      (boundedFlatCoefficientFullOpenBassConeEvaluation (𝟙 P) a)) :=
    boundedFlatCoefficientFullOpenBassConeEvaluation_isStableEquivalence (𝟙 P) a _
  let : IsIso (bassLeft S hS (n : ℤ)) :=
    boundedFlatCoefficientConnectiveBassLeft_isIso P a n
  let : IsIso ((boundedFlatCoefficientForwardUnitQuotient P n).app a) :=
    boundedFlatCoefficientForwardUnitQuotient_app_isIso P a n
  let g := asIso ((boundedFlatCoefficientForwardUnitQuotient P n).app a) ≪≫
    boundedFlatCoefficientConnectiveQuotientIso P a n ≪≫
    asIso (bassLeft S hS (n : ℤ)) ≪≫ bassShift S (n : ℤ) ≪≫
    asIso ((stableHomotopyFunctor ((n : ℤ) + 1)).map
      (boundedFlatCoefficientFullOpenBassConeEvaluation (𝟙 P) a))
  exact isIso_of_conjugate u r _ (g := g.hom)
    (boundedFlatCoefficientBassTransition_connective_comparison P a n)

end Quillen.PerfectComplexes
