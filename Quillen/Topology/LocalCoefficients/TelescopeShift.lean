/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.ClassifyingSpace.TranslationTelescopeShift
public import Quillen.Topology.LocalCoefficients.HomotopyEquivalence

/-! # Actual right stabilization preserves all target local coefficients -/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace Quillen.TranslationTelescope
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)

/-- The original right-stabilization map, with arbitrary target local coefficients. -/
theorem rightStabilization_localHomology_isIso
    (A : LocalCoefficients.System.{max u v, max u v} (ClassifyingSpace (Model e))) (n : ℕ) :
    IsIso (LocalCoefficients.pushforwardHomologyMap
      (classifyingSpaceMap (rightStabilization e)).hom A n) := by
  rw [← rightStabilizationClassifyingHomotopyEquiv_toFun e]
  exact LocalCoefficients.isIso_pushforwardHomologyMap_of_homotopyEquiv _ A n

end Quillen.TranslationTelescope
