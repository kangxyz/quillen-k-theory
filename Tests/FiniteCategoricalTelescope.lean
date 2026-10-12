/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.FiniteTelescope
public import Tests.LocalCoefficientChains

/-!
# Consumers of the finite categorical telescope model

No stage transition is required to be an equivalence. Tests retain the original
projection and initial-unit maps and use the regular path-class local system.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace Quillen.Tests.FiniteCategoricalTelescope

variable (F : ℕ ⥤ Cat.{u, u}) (n : ℕ)

/-- The forward equivalence is exactly the original terminal projection. -/
theorem original_projection :
    (FiniteGrothendieckTelescope.classifyingHomotopyEquiv F n).toFun =
      (classifyingSpaceMap (FiniteGrothendieckTelescope.projection F n)).hom := rfl

/-- The original stage-zero unit projects by the original sequence transition. -/
theorem original_unit :
    FiniteGrothendieckTelescope.inclusion F n 0 ⋙
        FiniteGrothendieckTelescope.projection F n =
      (F.map (homOfLE (Nat.zero_le n))).toFunctor :=
  FiniteGrothendieckTelescope.initial_unit_projection F n

/-- Final-stage inclusion preserves genuinely path-dependent local coefficients. -/
theorem regular_last_stage
    (b : ClassifyingSpace (FiniteGrothendieckTelescope.Model F n))
    (V : ModuleCat.{u} ℤ) (k : ℕ) :
    IsIso (LocalCoefficients.pushforwardHomologyMap
      (classifyingSpaceMap (FiniteGrothendieckTelescope.inclusion F n (Fin.last n))).hom
      (LocalCoefficientChains.regularSystem b V) k) :=
  LocalCoefficients.finiteTelescopeLastInclusion_isIso F n _ k

end Quillen.Tests.FiniteCategoricalTelescope
