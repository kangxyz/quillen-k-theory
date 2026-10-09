import Quillen.CategoryTheory.ExactCategory.Abelian
import Quillen.KTheory.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Concrete instantiation sanity tests: integer modules

These examples instantiate the exact structure, Q-category, based classifying
space, and K-groups for the actual category `ModuleCat ℤ`. No hypothetical exact
structure or admissibility assumptions are supplied. They also exhibit the
conflation `ℤ ⟶ ℤ ⊞ ℤ ⟶ ℤ`.

These are instantiation tests, not computations of K-groups. In particular,
the exact category here consists of all small integer modules, not just the
finitely generated projective modules used to define the usual K-theory of ℤ.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Quillen.Examples

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The standard exact structure on the concrete abelian category of ℤ-modules. -/
abbrev integerModuleExactStructure : ExactStructure (ModuleCat.{0} ℤ) :=
  abelianExactStructure (ModuleCat.{0} ℤ)

/-- The actual Q-category attached to the exact category of ℤ-modules. -/
abbrev IntegerModuleQ := integerModuleExactStructure.QCategory

example : Category IntegerModuleQ := inferInstance

/-- The rank-one free integer module gives a concrete object of the Q-category. -/
def integerQRankOne : IntegerModuleQ :=
  Q.of integerModuleExactStructure.deflation integerModuleExactStructure.inflation
    (ModuleCat.of ℤ ℤ)

example : integerQRankOne ⟶ integerQRankOne := 𝟙 integerQRankOne

/-- The basepoint is constructed from the zero module. -/
example : integerModuleExactStructure.KSpace :=
  integerModuleExactStructure.kBasepoint

/-- The defined K-groups of this concrete exact category. -/
abbrev IntegerModuleK (n : ℕ) := integerModuleExactStructure.K n

example (n : ℕ) : Group (IntegerModuleK n) := inferInstance

example (n : ℕ) : CommGroup (IntegerModuleK (n + 1)) := inferInstance

example : IntegerModuleK 0 := 1

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

end Quillen.Examples
