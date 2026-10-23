/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module
public import Aglib.Algebra.Homology.CochainComplexPlus.Shift
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # Shift stability of bounded-below quasi-isomorphisms

Use the native shift-compatible comparison maps and retain stability of the original
bounded-below quasi-isomorphism property.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.Plus
/-- The original bounded-below quasi-isomorphisms are stable under installed shifts. -/
instance quasiIsoCompatibleWithShift (C : Type*) [Category* C]
    [Preadditive C] [CategoryWithHomology C] :
    (quasiIso C).IsCompatibleWithShift ℤ where
  condition n := by
    ext K L g
    change HomologicalComplex.quasiIso C (.up ℤ) ((g⟦n⟧').hom) ↔
      HomologicalComplex.quasiIso C (.up ℤ) g.hom
    rw [← MorphismProperty.IsCompatibleWithShift.iff
      (HomologicalComplex.quasiIso C (.up ℤ)) g.hom n]
    exact (HomologicalComplex.quasiIso C (.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((ι C).commShiftIso n) (Arrow.mk g))
end CochainComplex.Plus
