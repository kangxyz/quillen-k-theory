/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteTermFiltration
public import Aglib.Algebra.Homology.Embedding.StupidTrunc.Layer
public import Aglib.Algebra.Homology.Embedding.StupidTrunc.Maps
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.StupidTruncationFixedBounds

/-! # The actual brutal filtration inside each finite term stratum

The original brutal and single-layer functors stay inside the specified
actual term-bound category. Their original maps give a genuine structural
cofibration sequence of exact endofunctors, with identity and zero endpoints.
Only isomorphism weak equivalences are used, and kernel closure is absent.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex


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
  [(abelianExactStructure A).IsExtensionClosed P]

/-- Genuine finite-stratum structural additivity data, with original maps. -/
theorem finiteTerm_isCofibrationSequence (a b n : ℤ) :
    Additivity.IsCofibrationSequence (ofExactCategory (fixedTermsExactStructure P a b))
      (ofExactCategory (fixedTermsExactStructure P a b))
      (finiteTermTransition P a b (by omega : n ≤ n + 1)) (finiteTermProjection P a b n) :=
  exactFunctorSequence_isCofibrationSequence _ _ _ _ (finiteTerm_comp_zero P a b n)
    (finiteTermLayer_conflation P a b n)
    (finiteTermTruncationExact P a b (n + 1)) (finiteTermTruncationExact P a b n)
    (finiteTermLayerExact P a b n) rfl rfl rfl

end Quillen.Waldhausen.GilletWaldhausen
