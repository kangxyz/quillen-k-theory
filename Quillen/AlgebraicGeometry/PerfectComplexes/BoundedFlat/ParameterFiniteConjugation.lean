/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFiniteNegativeComparison
public import Quillen.KTheory.Bass.SchemeConjugationStableSign
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientDoubleNegativeRepresentatives

/-!
# The second conjugation on the original finite-bottom classes

The class comparison is the one fixed by the original negative-group recursion,
actual Spec-row isomorphism, restriction, and finite stage map. The actual second
conjugation acts as minus the transported geometric two-cone permutation.
The latter action is retained rather than identified with either sign.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CommRingCat.PolynomialLaurent
open Quillen.LoopPrespectrum Quillen.LoopPrespectrum.FiniteLoopWords
open Quillen.KTheory.Bass Quillen.KTheory.Bass.SchemeNaturalSeed
open Quillen.KTheory.Bass.GeometricConeFixedWords

universe u

namespace Quillen.PerfectComplexes.GlobalParameterCoefficient

open GlobalSectionChangeIndex CoefficientNegativeRepresentatives
open NormalizedStageMap

/-- The actual normalized class map retains both original quotients and both signed shifts. -/
@[reassoc]
theorem doubleLaurentQuotient_normalizedComparison
    (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [CompactSpace P.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    doubleLaurentQuotient P a ≫ (normalizedNegativeKComparison P 2 a).hom =
      (boundedFlatCoefficientAmbientNegativeKComparison P 0).hom.app
          ((laurentUnderFunctor _).obj ((laurentUnderFunctor _).obj a)) ≫
        bottomStep P 0 ((laurentUnderFunctor _).obj a) ≫ bottomStep P 1 a ≫
        inv (I := finiteRestriction_isStableEquivalence P 2 a (-((2 : ℕ) : ℤ)))
          ((stableHomotopyFunctor (-((2 : ℕ) : ℤ))).map ((finiteRestriction P 2).app a)) ≫
        (stableHomotopyFunctor (-((2 : ℕ) : ℤ))).map ((finiteIso P 2).inv.app a) ≫
        (stableHomotopyFunctor (-((2 : ℕ) : ℤ))).map
          ((stageMap squareFunctor 2 (parameterDiagram P)).app (specUnder.obj a)) := by
  rw [normalizedNegativeKComparison_hom]
  exact doubleLaurentQuotient_comparison_assoc P a _

/-- The original degree-minus-two classes retain the actual signed geometric correction. -/
@[reassoc]
theorem normalizedNegativeKComparison_two_conjugating
    (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [CompactSpace P.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (normalizedNegativeKComparison P 2 a).hom ≫
      (stableHomotopyFunctor (-((2 : ℕ) : ℤ))).map
        ((conjugatingIso 2 (parameterDiagram P)).hom.app (specUnder.obj a)) =
      -((normalizedNegativeKComparison P 2 a).hom ≫
        (stableHomotopyFunctor (-((2 : ℕ) : ℤ))).map ((loopMap 2
          (eqToHom (power_obj 2 (parameterDiagram P)).symm ≫
            (GeometricConeInterchange.permutationNatIso (parameterDiagram P)).hom ≫
              eqToHom (power_obj 2 (parameterDiagram P)))).app (specUnder.obj a))) := by
  rw [conjugatingIso_two_stable]
  exact Preadditive.comp_neg _ _

end Quillen.PerfectComplexes.GlobalParameterCoefficient
