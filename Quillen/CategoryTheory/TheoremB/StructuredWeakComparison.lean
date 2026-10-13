/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.TheoremB.WeakComparison
public import Quillen.CategoryTheory.TheoremB.StructuredWeakTransport

/-!
# Quillen's Theorem B in the structured-arrow convention

The actual contravariant structured-comma transition hypothesis implies
bijectivity of the canonical structured comparison on every based homotopy
set at the identity-arrow basepoint. The opposite-category realization and
its path-coordinate reversal preserve that specific comparison and basepoint.
No global homotopy inverse of the fiber comparison is asserted.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
namespace Quillen.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- Structured Theorem B at the actual identity-arrow basepoint, including
π₀, under only the actual structured transition hypothesis. -/
theorem structuredFiberComparison_bijective
    (h : StructuredTransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (structuredFiberComparison F (F.obj c)) (structuredFiberComparison_identity F c)) :=
  structuredFiberComparison_bijective_of_opposite F c n
    (fiberComparison_bijective F.op
      (transitionHomotopyEquivalences_op_of_structured F h) (op c) n)

/-- The structured comparison induces its canonical positive-degree group
isomorphism; no separately chosen unbased equivalence is substituted. -/
def structuredFiberComparisonPiEquiv
    (h : StructuredTransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (ClassifyingSpace (StructuredArrow (F.obj c) F))
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) ≃*
    HomotopyGroup.Pi (n + 1)
      (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c)))
      (HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c)) :=
  MulEquiv.ofBijective
    (piMap n (structuredFiberComparison F (F.obj c)) (structuredFiberComparison_identity F c))
    (structuredFiberComparison_bijective F h c (n + 1))

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem structuredFiberComparisonPiEquiv_coe
    (h : StructuredTransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    ↑(structuredFiberComparisonPiEquiv F h c n) =
      piMap n (structuredFiberComparison F (F.obj c)) (structuredFiberComparison_identity F c)
        := rfl

end Quillen.TheoremB
