/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.Exact
public import Quillen.CategoryTheory.SmallModel.Abelian

/-!
# Genuine affine G-theory and its module comparison

For a commutative noetherian ring `R`, affine G-theory is the Quillen K-theory
of an actual small model of coherent sheaves on `Spec R`, with the exact
structure whose short exact sequences agree with ambient sheaf sequences.
The global-sections equivalence induces the canonical comparison with the
G-theory of finite `R`-modules.
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

instance affineGlobalSections_additive : (affineFiniteTypeModuleEquivalence R).functor.Additive :=
  by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (affineFiniteTypeModuleEquivalence
    R).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The actual global-sections equivalence as an exact functor. -/
def affineGlobalSectionsExact :
    ExactFunctor (affineCoherentExactStructure R) (finiteModuleExactStructure.{u, u} R) where
  toFunctor := (affineFiniteTypeModuleEquivalence R).functor
  map_conflation _ h := h.map_of_exact _

/-- G-theory of finite modules over a commutative noetherian ring, in the base
ring's universe. -/
abbrev RingG (n : ℕ) : Type u :=
  ExactStructure.SmallK.{u} (finiteModuleExactStructure.{u, u} R) n

/-- G-theory of the actual coherent sheaf category on `Spec R`. -/
abbrev AffineG (n : ℕ) : Type u :=
  ExactStructure.SmallK.{u} (affineCoherentExactStructure R) n

/-- The canonical map induced by actual global sections, transported to the
chosen small models. -/
def affineGToRingG (n : ℕ) : AffineG R n →* RingG R n :=
  (affineGlobalSectionsExact R).smallKMap n

instance affineGlobalSectionsSmall_isEquivalence :
    ((affineGlobalSectionsExact R).smallModel).toFunctor.IsEquivalence := by
  change (((equivSmallModel.{u} (AffineFiniteType R)).inverse ⋙
    (affineFiniteTypeModuleEquivalence R).functor) ⋙
    (equivSmallModel.{u} (FiniteModule.{u, u} R)).functor).IsEquivalence
  infer_instance

instance affineGlobalSectionsSmall_mapQ_isEquivalence :
    ((affineGlobalSectionsExact R).smallModel).mapQ.IsEquivalence := by
  apply ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro X Y i hi
    change (abelianExactStructure (FiniteModule.{u, u} R)).smallModel.inflation _ at hi
    change (abelianExactStructure (AffineFiniteType R)).smallModel.inflation i
    rw [abelianExactStructure_smallModel, abelianExactStructure_inflation_iff] at hi ⊢
    exact ((affineGlobalSectionsExact R).smallModel).toFunctor.mono_of_mono_map hi
  · intro X Y p hp
    change (abelianExactStructure (FiniteModule.{u, u} R)).smallModel.deflation _ at hp
    change (abelianExactStructure (AffineFiniteType R)).smallModel.deflation p
    rw [abelianExactStructure_smallModel, abelianExactStructure_deflation_iff] at hp ⊢
    exact ((affineGlobalSectionsExact R).smallModel).toFunctor.epi_of_epi_map hp

/-- The genuine affine comparison `G_n(Spec R) ≃ G_n(R)` induced by global
sections. Its forward homomorphism is exactly the canonical K-map. -/
def affineGEquiv (n : ℕ) : AffineG R n ≃* RingG R n :=
  ((affineGlobalSectionsExact R).smallModel).KEquivOfMapQIsEquivalence n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem affineGEquiv_coe (n : ℕ) :
    ↑(affineGEquiv R n) = affineGToRingG R n := rfl

end Quillen.CoherentScheme
