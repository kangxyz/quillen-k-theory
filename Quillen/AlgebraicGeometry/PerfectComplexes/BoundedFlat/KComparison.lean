/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Approximation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Functor
public import Quillen.Waldhausen.Approximation.GeneralKEquivalence

/-!
# The original bounded-flat-to-perfect K-comparison

Actual relative replacements prove App1/App2 for the literal inclusion on
quasi-compact schemes. The actual bounded-flat joint cylinders and the proved
independent-universe approximation theorem show that its original canonical
K-map is bijective in every connective degree, including zero. The resulting
group equivalence has precisely that unchanged inclusion map as its forward map.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes

/-- On quasi-compact schemes the literal bounded-flat inclusion K-map is bijective
in every connective degree, from actual relative replacements and actual cylinders. -/
theorem boundedFlatPerfectToPerfectKMap_bijective (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    Function.Bijective (boundedFlatPerfectToPerfectKMap X n) := by
  let : (perfectWaldhausen X).weq.HasTwoOutOfThreeProperty :=
    Waldhausen.complexSubcategory_saturated (locallyPerfect X)
  exact (boundedFlatPerfectInclusion_approximation X).KMap_bijective_general
    (boundedFlatPerfectInclusion_exact X) (boundedFlatPerfectJointData X) n

/-- The actual bounded-flat model computes the original locally-perfect K-groups
on quasi-compact schemes. Its forward map is the original literal inclusion. -/
def boundedFlatPerfectKEquiv (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    BoundedFlatPerfectK X n ≃* PerfectK X n :=
  MulEquiv.ofBijective (boundedFlatPerfectToPerfectKMap X n)
    (boundedFlatPerfectToPerfectKMap_bijective X n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem boundedFlatPerfectKEquiv_coe (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    ↑(boundedFlatPerfectKEquiv X n) = boundedFlatPerfectToPerfectKMap X n := rfl

end Quillen.PerfectComplexes
