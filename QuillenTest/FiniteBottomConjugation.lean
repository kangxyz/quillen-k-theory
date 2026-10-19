/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFiniteConjugation
public import Quillen.KTheory.Bass.GeometricConeDoubleLaurent

/-! # Original finite-bottom classes and the retained second conjugation correction -/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum Quillen.LoopPrespectrum.FiniteLoopWords
open Quillen.KTheory.Bass Quillen.KTheory.Bass.SchemeNaturalSeed
open Quillen.KTheory.Bass.GeometricConeFixedWords
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalParameterCoefficient
open Quillen.PerfectComplexes.CoefficientNegativeRepresentatives

universe u

variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [CompactSpace P.left]
variable (a : Under (CommRingCat.of (ULift.{u} ℤ)))

example (x : (boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor 1).obj a) :
    (stableHomotopyFunctor (-((1 : ℕ) : ℤ))).map
        ((conjugatingIso 1 (parameterDiagram P)).hom.app (specUnder.obj a))
      ((normalizedNegativeKComparison P 1 a).hom x) =
        (normalizedNegativeKComparison P 1 a).hom x :=
  congrArg (fun k => k x) (normalizedNegativeKComparison_one_conjugating P a)

example (x : (boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor 2).obj a) :
    (stableHomotopyFunctor (-((2 : ℕ) : ℤ))).map
        ((conjugatingIso 2 (parameterDiagram P)).hom.app (specUnder.obj a))
      ((normalizedNegativeKComparison P 2 a).hom x) =
      -((stableHomotopyFunctor (-((2 : ℕ) : ℤ))).map ((loopMap 2
        (eqToHom (power_obj 2 (parameterDiagram P)).symm ≫
          (GeometricConeInterchange.permutationNatIso (parameterDiagram P)).hom ≫
            eqToHom (power_obj 2 (parameterDiagram P)))).app (specUnder.obj a))
              ((normalizedNegativeKComparison P 2 a).hom x)) :=
  congrArg (fun k => k x) (normalizedNegativeKComparison_two_conjugating P a)

example {A : AddCommGrpCat.{u + 1}}
    (f g : (boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor 2).obj a ⟶ A)
    (h : ∀ x, f (doubleLaurentQuotient P a x) = g (doubleLaurentQuotient P a x)) : f = g := by
  apply doubleLaurentQuotient_hom_ext P a
  apply AddCommGrpCat.ext
  exact h

example (E : Quillen.LoopPrespectrum.{u}) (x : stableHomotopyGroup
    (parameterLooping (parameterLooping E)) (-2)) :
    (stableHomotopyFunctor (-2)).map (LoopTranspose.transpose E) x = -x :=
  congrArg (fun k => k x) (LoopTranspose.stableHomotopyFunctor_map_transpose E (-2))
