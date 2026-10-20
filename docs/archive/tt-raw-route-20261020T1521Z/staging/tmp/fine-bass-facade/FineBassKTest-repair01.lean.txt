/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FineBassK

/-! Regression: actual seed stability, original K₀ inclusion, and both specified-null lifts. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace QuillenTest.FineBassK
open Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (a : Under R)

/-- The actual ambient seed yields a stable Bass map without an external topology premise. -/
theorem ambient_bass_stable : IsStableEquivalence ((FineBassK.bassMap Q).app a) :=
  FineBassK.bassMap_isStableEquivalence Q a

/-- The supported seed yields its actual stable Bass map. -/
theorem supported_bass_stable : IsStableEquivalence ((FineBassK.supportedBassMap f).app a) :=
  FineBassK.supportedBassMap_isStableEquivalence f a

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The connective degree-zero comparison retains the original inclusion. -/
theorem original_kzero_class : (FineBassK.connectiveComparison Q 0).hom.app a =
    (boundedFlatCoefficientSectionKStableNatIso Q 0).hom.app a ≫
      (stableHomotopyFunctor (0 : ℤ)).map
        ((boundedFlatCoefficientAmbientBassTelescopeInclusion Q 0).app a) :=
  boundedFlatCoefficientAmbientKTelescopeComparison_hom_app Q 0 a

/-- The basic localization theorem applies to the original specified-null lift. -/
theorem basic_same_null : IsStableEquivalence
    (homotopyFiberLift ((FineBassK.restriction f).app a)
      ((FineBassK.supportForget f).app a) ((FineBassK.localizationNull f).homotopy a)) :=
  FineBassK.localization f a

/-- The compact auxiliary localization theorem applies to its original lift. -/
theorem auxiliary_same_null (T : Q.left.Opens) [CompactSpace T] : IsStableEquivalence
    (homotopyFiberLift ((FineBassK.auxiliaryRestriction f T).app a)
      ((FineBassK.auxiliaryForget f T).app a) ((FineBassK.auxiliaryNull f T).homotopy a)) :=
  FineBassK.auxiliaryLocalization f T a

end QuillenTest.FineBassK
