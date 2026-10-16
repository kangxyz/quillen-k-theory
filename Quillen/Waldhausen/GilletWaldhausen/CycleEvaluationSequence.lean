/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.CycleEvaluationSequence
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.CyclesExact
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence
public import Aglib.Algebra.Homology.CochainComplex.Cycles

/-! # The actual cycle-to-term incidence cofibration sequence

On bounded acyclic termwise-P complexes, the original cycle inclusion and
original differential factorization give a genuine cofibration sequence of
exact functors `Z_n → E_n → Z_(n+1)` into P. Quotient exactness supplies the
relative-pushout cofibration condition. The weak maps here are isomorphisms:
cycles and terms do not generally send quasi-isomorphisms to isomorphisms.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A)

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The relative pushout comparison is genuinely admissible, derived from
exactness of the next-cycle functor rather than assumed. -/
theorem boundedAcyclicCycleEvaluation_cofibration (n : ℤ) :
    Additivity.IsCofibrationTransformation
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P))
      (boundedAcyclicCycleInclusion P n) (ofExactCategory (boundedAcyclicExactStructure P)) :=
  exactFunctorSequence_cofibration _ _ _ _ (boundedAcyclicCycle_comp_zero P n)
    (boundedAcyclicCycleEvaluation_conflation P n)
    (boundedAcyclicCyclesExactFunctor P (n + 1)).map_inflation

/-- The genuine incidence cofibration sequence in the isomorphism models,
retaining the original term evaluation and original cycle arrows. -/
theorem boundedAcyclicCycleEvaluation_isCofibrationSequence (n : ℤ) :
    Additivity.IsCofibrationSequence (ofExactCategory (boundedAcyclicExactStructure P))
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P))
      (boundedAcyclicCycleInclusion P n) (boundedAcyclicCycleProjection P n) :=
  exactFunctorSequence_isCofibrationSequence _ _ _ _ (boundedAcyclicCycle_comp_zero P n)
    (boundedAcyclicCycleEvaluation_conflation P n)
    (boundedAcyclicCyclesExactFunctor P n) (boundedAcyclicEvaluationExactFunctor P n)
    (boundedAcyclicCyclesExactFunctor P (n + 1)) rfl rfl rfl

end Quillen.Waldhausen.GilletWaldhausen
