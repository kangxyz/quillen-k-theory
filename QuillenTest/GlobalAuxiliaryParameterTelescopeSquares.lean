/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterTelescopeSquares

/-! # Original signed-class consumers of the actual auxiliary support telescope squares -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen Quillen.PerfectComplexes Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace QuillenTest.GlobalAuxiliaryParameterTelescopeSquares
open GlobalSectionChangeIndex GlobalAuxiliaryParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The actual inclusion square commutes on the original classes in every signed degree. -/
theorem original_signed_enlargement (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ)
    (z : stableHomotopyGroup
      ((SchemeNaturalSeed.iteratedTelescope (ParameterAuxiliarySupport.fiberAction f.left T)).obj
        (specUnder.obj a)) d) :
    (stableHomotopyFunctor d).map ((ambientTelescopeComparison Q T).app a)
        ((stableHomotopyFunctor d).map
          ((ParameterAuxiliarySupport.iteratedEnlargement f.left T).app (specUnder.obj a)) z) =
      (stableHomotopyFunctor d).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((stableHomotopyFunctor d).map ((fiberTelescopeComparison f T).app a) z) := by
  have h := NatTrans.congr_app (telescope_enlargement_square f T) a
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  have hstable := congrArg ((stableHomotopyFunctor d).map) h
  simp only [Functor.map_comp] at hstable
  exact ConcreteCategory.congr_hom hstable z

/-- Every original negative class retains the same fine-to-coarse-to-fine restriction word. -/
theorem original_negative_restriction (a : Under (CommRingCat.of (ULift.{u} ℤ))) (q : ℕ)
    (z : stableHomotopyGroup
      ((SchemeNaturalSeed.iteratedTelescope (ParameterAuxiliarySupport.ambientAction T)).obj
        (specUnder.obj a)) (-(q : ℤ) - 1)) :
    (stableHomotopyFunctor (-(q : ℤ) - 1)).map ((openTelescopeComparison f T).app a)
        ((stableHomotopyFunctor (-(q : ℤ) - 1)).map
          ((ParameterAuxiliarySupport.iteratedRestriction f.left T).app (specUnder.obj a)) z) =
      (stableHomotopyFunctor (-(q : ℤ) - 1)).map
        ((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a)
        ((stableHomotopyFunctor (-(q : ℤ) - 1)).map
          ((boundedFlatCoefficientSupportedAmbientBassTelescopeOpen f T).app a)
          ((stableHomotopyFunctor (-(q : ℤ) - 1)).map
            ((ambientTelescopeComparison Q T).app a) z)) := by
  have h := NatTrans.congr_app (telescope_restriction_square f T) a
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  have hstable := congrArg ((stableHomotopyFunctor (-(q : ℤ) - 1)).map) h
  simp only [Functor.map_comp] at hstable
  exact ConcreteCategory.congr_hom hstable z

end QuillenTest.GlobalAuxiliaryParameterTelescopeSquares
