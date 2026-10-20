/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FineBassK

/-! Independent signed-degree consumers of the selected fine-model localization lifts. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Consumer.FineBassK
open Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (a : Under R)

/-- Every signed degree sees the actual basic same-null fiber lift as an isomorphism. -/
theorem basic_signed (d : ℤ) : IsIso ((stableHomotopyFunctor d).map
    (homotopyFiberLift ((FineBassK.restriction f).app a)
      ((FineBassK.supportForget f).app a) ((FineBassK.localizationNull f).homotopy a))) :=
  FineBassK.localization f a d

/-- Compact auxiliary support uses its own original arrows and null in every signed degree. -/
theorem auxiliary_signed (T : Q.left.Opens) [CompactSpace T] (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((FineBassK.auxiliaryRestriction f T).app a)
        ((FineBassK.auxiliaryForget f T).app a) ((FineBassK.auxiliaryNull f T).homotopy a))) :=
  FineBassK.auxiliaryLocalization f T a d

end Consumer.FineBassK
