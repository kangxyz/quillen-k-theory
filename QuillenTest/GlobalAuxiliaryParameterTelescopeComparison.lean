/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterTelescopeComparison

/-! # Actual G7 Spec-row comparison regressions in every signed stable degree -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum
open Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
universe u
namespace QuillenTest.GlobalAuxiliaryParameterTelescopeComparison
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]
    (T : Q.left.Opens)

/-- The original fiber telescope comparison is bijective in each signed stable degree. -/
theorem fiber_signed_bijective
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    Function.Bijective ((stableHomotopyFunctor d).map
      ((fiberTelescopeComparison f T).app a)) := by
  have := fiberTelescopeComparison_stable f T a d
  exact ConcreteCategory.bijective_of_isIso _

/-- The original ambient telescope comparison is bijective in each signed stable degree. -/
theorem ambient_signed_bijective (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    Function.Bijective ((stableHomotopyFunctor d).map
      ((ambientTelescopeComparison Q T).app a)) := by
  have := ambientTelescopeComparison_stable Q T a d
  exact ConcreteCategory.bijective_of_isIso _

omit [IsOpenImmersion f.left] in
/-- The original open telescope comparison is bijective in each signed stable degree. -/
theorem open_signed_bijective
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    Function.Bijective ((stableHomotopyFunctor d).map
      ((openTelescopeComparison f T).app a)) := by
  have := openTelescopeComparison_stable f T a d
  exact ConcreteCategory.bijective_of_isIso _

end QuillenTest.GlobalAuxiliaryParameterTelescopeComparison
