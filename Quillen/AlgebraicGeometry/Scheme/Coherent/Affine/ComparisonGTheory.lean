/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.Comparison
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.GTheory

/-!
# Lowest-universe affine G-theory of the global coherent category

The all-affine-chart coherent category on a noetherian spectrum now has a
proved small model in the base ring's universe. Forming its K-theory in this
universe yields the actual affine coherent G-theory and hence the G-theory
of finite modules. All forward maps are induced by the exact comparison
functors.

The earlier `G` for arbitrary locally noetherian schemes is formed in the
upper universe. No cross-universe realization comparison is asserted here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- G-theory of the actual global coherent category on an affine scheme,
formed in the base ring's universe using its proved smallness. -/
abbrev SpecG (n : ℕ) : Type u :=
  ExactStructure.SmallK.{u} (coherentExactStructure (Spec R)) n

/-- The canonical K-map induced by the identity-on-sheaves comparison. -/
def specGToAffineG (n : ℕ) : SpecG R n →* AffineG R n :=
  (coherentToAffineExact R).smallKMap n

instance coherentToAffineSmall_isEquivalence :
    ((coherentToAffineExact R).smallModel).toFunctor.IsEquivalence := by
  change (((equivSmallModel.{u} (FiniteTypeSheaves (Spec R))).inverse ⋙
    (finiteTypeSheavesAffineEquivalence R).functor) ⋙
    (equivSmallModel.{u} (AffineFiniteType R)).functor).IsEquivalence
  infer_instance

instance coherentToAffineSmall_mapQ_isEquivalence :
    ((coherentToAffineExact R).smallModel).mapQ.IsEquivalence := by
  apply ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro X Y i hi
    change (abelianExactStructure (AffineFiniteType R)).smallModel.inflation _ at hi
    change (abelianExactStructure (FiniteTypeSheaves (Spec R))).smallModel.inflation i
    rw [abelianExactStructure_smallModel, abelianExactStructure_inflation_iff] at hi ⊢
    exact ((coherentToAffineExact R).smallModel).toFunctor.mono_of_mono_map hi
  · intro X Y p hp
    change (abelianExactStructure (AffineFiniteType R)).smallModel.deflation _ at hp
    change (abelianExactStructure (FiniteTypeSheaves (Spec R))).smallModel.deflation p
    rw [abelianExactStructure_smallModel, abelianExactStructure_deflation_iff] at hp ⊢
    exact ((coherentToAffineExact R).smallModel).toFunctor.epi_of_epi_map hp

/-- The G-groups of the actual global and affine coherent categories agree. -/
def specGAffineEquiv (n : ℕ) : SpecG R n ≃* AffineG R n :=
  ((coherentToAffineExact R).smallModel).KEquivOfMapQIsEquivalence n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem specGAffineEquiv_coe (n : ℕ) :
    ↑(specGAffineEquiv R n) = specGToAffineG R n := rfl

/-- The actual coherent-sheaf G-theory on `Spec R` agrees with module G-theory. -/
def specGRingEquiv (n : ℕ) : SpecG R n ≃* RingG R n :=
  (specGAffineEquiv R n).trans (affineGEquiv R n)

/-- Its forward homomorphism is the composite of the canonical exact K-maps. -/
theorem specGRingEquiv_toMonoidHom (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom =
      (affineGToRingG R n).comp (specGToAffineG R n) := rfl

end Quillen.CoherentScheme
