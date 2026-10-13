/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.ExactCategory.Abelian
public import Quillen.KTheory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The exact category of integer modules

Instantiate the abelian exact structure and Q-construction on `ModuleCat ℤ`,
check the zero basepoint and K-group instances, and exhibit the split conflation
`ℤ ⟶ ℤ ⊞ ℤ ⟶ ℤ`. The category here contains all small integer modules.
-/
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Quillen

namespace QuillenTest.IntegerModules

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The standard exact structure on the concrete abelian category of ℤ-modules. -/
abbrev integerModuleExactStructure : ExactStructure (ModuleCat.{0} ℤ) :=
  abelianExactStructure (ModuleCat.{0} ℤ)

/-- The actual Q-category attached to the exact category of ℤ-modules. -/
abbrev IntegerModuleQ := integerModuleExactStructure.QCategory


/-- The rank-one free integer module gives a concrete object of the Q-category. -/
def integerQRankOne : IntegerModuleQ :=
  Q.of integerModuleExactStructure.deflation integerModuleExactStructure.inflation
    (ModuleCat.of ℤ ℤ)



/-- The defined K-groups of this concrete exact category. -/
abbrev IntegerModuleK (n : ℕ) := integerModuleExactStructure.K n




/-- The standard split sequence with both outside terms equal to ℤ. -/
def integerSplitSequence : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk
    (biprod.inl : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ ⊞ ModuleCat.of ℤ ℤ)
    (biprod.snd : ModuleCat.of ℤ ℤ ⊞ ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)
    (by simp)

/-- This explicit split sequence really belongs to the instantiated exact structure. -/
theorem integerSplitSequence_conflation :
    integerModuleExactStructure.conflation integerSplitSequence :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct
    (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ)).shortExact

example : Category IntegerModuleQ := inferInstance

example : integerQRankOne ⟶ integerQRankOne := 𝟙 integerQRankOne

/-- The basepoint is constructed from the zero module. -/
example : integerModuleExactStructure.KSpace :=
  integerModuleExactStructure.kBasepoint

example (n : ℕ) : Group (IntegerModuleK n) := inferInstance

example (n : ℕ) : CommGroup (IntegerModuleK (n + 1)) := inferInstance

example : IntegerModuleK 0 := 1

end QuillenTest.IntegerModules
