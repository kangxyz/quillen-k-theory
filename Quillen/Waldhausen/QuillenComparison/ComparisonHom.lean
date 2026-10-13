/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.Basepoint
public import Quillen.Topology.Realization.EdgewiseRealization
public import Quillen.Topology.HomotopyGroups.Equivalence

/-! # The canonical homomorphism from exact S-theory to Quillen K-theory

The edgewise endpoint is proved to be a homotopy equivalence for every
simplicial set. Inverting its induced based group isomorphism turns the
explicit comparison zigzag into an actual homomorphism between the two
already-defined K-theories. The Q/S map's equivalence remains a separate
mathematical theorem; it is not assumed by this construction.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)

/-- The left arrow of the Q/S zigzag is a proved based K-group isomorphism. -/
def subdivisionKEquiv (n : ℕ) : SubdivisionK E n ≃* (ofExactCategory E).K n :=
  homotopyEquivPiEquiv
    (Edgewise.realizationHomotopyEquiv (sSet E.inflation (MorphismProperty.isomorphisms C)))
    (realizationEndpoint_basepoint E) n

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem subdivisionKEquiv_coe (n : ℕ) :
    (↑(subdivisionKEquiv E n) : SubdivisionK E n →* (ofExactCategory E).K n) =
        subdivisionEndpointK E n := rfl


/-- The canonical comparison homomorphism from the exact-category Waldhausen
S-model to the existing Quillen Q-model. No comparison equivalence is an input. -/
def comparisonK (n : ℕ) : (ofExactCategory E).K n →* E.K n :=
  (subdivisionComparisonK E n).comp (subdivisionKEquiv E n).symm.toMonoidHom

/-- The comparison is characterized by the actual based zigzag. -/
@[simp]
theorem comparisonK_comp_endpoint (n : ℕ) :
    (comparisonK E n).comp (subdivisionEndpointK E n) = subdivisionComparisonK E n := by
  ext a
  exact congrArg (subdivisionComparisonK E n) ((subdivisionKEquiv E n).symm_apply_apply a)

/-- There is only one homomorphism having the stated zigzag property. -/
theorem comparisonK_unique (n : ℕ) (f : (ofExactCategory E).K n →* E.K n)
    (hf : f.comp (subdivisionEndpointK E n) = subdivisionComparisonK E n) :
    f = comparisonK E n := by
  ext a
  have h := DFunLike.congr_fun hf ((subdivisionKEquiv E n).symm a)
  change f (subdivisionKEquiv E n ((subdivisionKEquiv E n).symm a)) =
    subdivisionComparisonK E n ((subdivisionKEquiv E n).symm a) at h
  rw [MulEquiv.apply_symm_apply] at h
  exact h

end Quillen.Waldhausen.QuillenComparison
