/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremB.ResolutionFiber
public import Quillen.Topology.HomotopyGroups.WeakEquivalence

/-!
# Canonical weak comparison through the categorical resolution

At the identity comma object the already constructed resolution homotopy
fixes the actual constant-path basepoint. Thus all-degree bijectivity of
the strict resolved comparison transfers to the prescribed original
comparison, including π₀. No based inverse homotopy is assumed.
-/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

namespace Quillen.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The actual resolution fiber equivalence carries the identity strict
comparison point to the canonical constant-path basepoint. -/
theorem resolutionFiberEquiv_identity (c : C) :
    (resolutionFiberEquiv F (F.obj c)).toFun
      (resolutionStrictFiberComparison F (F.obj c)
        (classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c))))) =
      HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c) :=
  ((resolutionComparisonHomotopy F (F.obj c)).map_zero_left
    (classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c))))).symm.trans
      (resolutionComparisonHomotopy_identity F c 0)

/-- A proved weak strict-fiber comparison in the resolution yields the
canonical original comma-to-fiber bijection in every homotopy degree.
This transports actual maps; it does not assert the open finite-stage
cartesian gluing input. -/
theorem fiberComparison_bijective_of_resolutionStrict (c : C) (n : ℕ)
    (h : Function.Bijective (homotopyGroupMap (N := Fin n)
      (resolutionStrictFiberComparison F (F.obj c))
      (x := classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) rfl)) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (fiberComparison F (F.obj c)) (fiberComparison_identity F c)) := by
  have hcomp := homotopyGroupMap_bijective_comp
    (resolutionStrictFiberComparison F (F.obj c)) (resolutionFiberEquiv F (F.obj c)).toFun
    rfl (resolutionFiberEquiv_identity F c) n h
    (homotopyGroupMap_bijective_of_homotopyEquiv
      (resolutionFiberEquiv F (F.obj c)) (resolutionFiberEquiv_identity F c) n)
  exact homotopyGroupMap_bijective_of_based_homotopy
    (f := transferredResolutionComparison F (F.obj c))
    (g := fiberComparison F (F.obj c))
    (x := classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c))))
    (resolutionFiberEquiv_identity F c) (fiberComparison_identity F c)
    (resolutionComparisonHomotopy F (F.obj c))
    (resolutionComparisonHomotopy_identity F c) n hcomp

/-- The positive-degree group isomorphism uses exactly the canonical comma
comparison; the resolution enters only in its proved bijectivity. -/
def fiberComparisonPiEquivOfResolutionStrict (c : C) (n : ℕ)
    (h : Function.Bijective (homotopyGroupMap (N := Fin (n + 1))
      (resolutionStrictFiberComparison F (F.obj c))
      (x := classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) rfl)) :
    HomotopyGroup.Pi (n + 1) (ClassifyingSpace (CostructuredArrow F (F.obj c)))
      (classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) ≃*
    HomotopyGroup.Pi (n + 1)
      (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c)))
      (HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c)) :=
  MulEquiv.ofBijective (piMap n (fiberComparison F (F.obj c)) (fiberComparison_identity F c))
    (fiberComparison_bijective_of_resolutionStrict F c (n + 1) h)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem fiberComparisonPiEquivOfResolutionStrict_coe (c : C) (n : ℕ)
    (h : Function.Bijective (homotopyGroupMap (N := Fin (n + 1))
      (resolutionStrictFiberComparison F (F.obj c))
      (x := classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) rfl)) :
    ↑(fiberComparisonPiEquivOfResolutionStrict F c n h) =
      piMap n (fiberComparison F (F.obj c)) (fiberComparison_identity F c) := rfl

end Quillen.TheoremB
