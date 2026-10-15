/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.Algebra.Category.ModuleCat.Finite
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeCategory
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exact
public import Aglib.CategoryTheory.SmallModel.Abelian

/-!
# Genuine affine G-theory and its module comparison

For a commutative noetherian ring `R`, affine G-theory is the Quillen K-theory
of an actual small model of coherent sheaves on `Spec R`, with the exact
structure whose short exact sequences agree with ambient sheaf sequences.
The global-sections equivalence induces the canonical comparison with the
G-theory of finite `R`-modules.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent
open CategoryTheory.ExactCategory


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen





noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- G-theory of finite modules over a commutative noetherian ring, in the base
ring's universe. -/
abbrev RingG (n : ℕ) : Type u :=
  CategoryTheory.ExactCategory.ExactStructure.SmallK.{u} (finiteModuleExactStructure.{u, u} R) n

/-- G-theory of the actual coherent sheaf category on `Spec R`. -/
abbrev AffineG (n : ℕ) : Type u :=
  CategoryTheory.ExactCategory.ExactStructure.SmallK.{u} (affineCoherentExactStructure R) n

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
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
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

end AlgebraicGeometry.Scheme.Modules.Coherent
