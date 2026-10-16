/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteCycleFiltration
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteCycleBounds
public import Quillen.Waldhausen.GilletWaldhausen.AdjacentTruncation

/-! # Actual finite-stratum acyclic truncation endofunctors

The original smart truncations and their original disk quotients stay in
one specified actual term-bound stratum. Their original adjacent maps form
genuine cofibration sequences in the isomorphism weak model. The lower
endpoint is zero by actual acyclicity, and the upper endpoint is the identity.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
universe v u
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]

/-- Genuine structural additivity data within one actual acyclic bound stratum. -/
theorem finiteCycle_isCofibrationSequence (a b n : ℤ) :
    Additivity.IsCofibrationSequence (ofExactCategory (fixedAcyclicExactStructure P a b))
      (ofExactCategory (fixedAcyclicExactStructure P a b))
      (finiteCycleInclusion P a b n) (finiteCycleProjection P a b n) :=
  exactFunctorSequence_isCofibrationSequence _ _ _ _ (finiteCycle_comp_zero P a b n)
    (finiteCycleLayer_conflation P a b n)
    (finiteCycleTruncationExact P a b n) (finiteCycleTruncationExact P a b (n + 1))
    (finiteCycleLayerExact P a b n) rfl rfl rfl

end Quillen.Waldhausen.GilletWaldhausen
