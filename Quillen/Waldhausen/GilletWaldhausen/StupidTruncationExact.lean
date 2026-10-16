/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.StupidTruncationExact
public import Aglib.Algebra.Homology.Embedding.StupidTrunc.Maps
public import Aglib.Algebra.Homology.Embedding.StupidTrunc.Transition
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.Algebra.Homology.Embedding.StupidTrunc.Layer
public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedTerms
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence

/-! # Exact brutal truncation and its actual bounded-term cofibration sequence

Original brutal truncations and single-term layers preserve bounded termwise-P
complexes and inherited conflations. Their original adjacent maps form a
cofibration sequence of exact functors for isomorphism weak equivalences.
No kernel closure is needed, and no preservation of quasi-isomorphisms is asserted.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The genuine term-filtration cofibration sequence for isomorphism weak maps.
The relative-pushout condition follows from the proved exact quotient functor. -/
theorem boundedTermsStupidLayer_isCofibrationSequence (n : ℤ) :
    Additivity.IsCofibrationSequence (ofExactCategory (boundedTermsExactStructure P))
      (ofExactCategory (boundedTermsExactStructure P))
      (boundedTermsStupidTruncGETransitionNat P (by omega : n ≤ n + 1))
      (boundedTermsStupidLayerProjectionNat P n) :=
  exactFunctorSequence_isCofibrationSequence _ _ _ _ (boundedTermsStupidLayer_comp_zero P n)
    (boundedTermsStupidLayer_conflation P n)
    (boundedTermsStupidTruncGEExactFunctor P (n + 1)) (boundedTermsStupidTruncGEExactFunctor P n)
    (boundedTermsStupidLayerExactFunctor P n) rfl rfl rfl

end Quillen.Waldhausen.GilletWaldhausen
