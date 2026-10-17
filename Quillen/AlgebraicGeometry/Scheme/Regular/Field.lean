/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Field

public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.Scheme.Comparison.KToG
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The canonical K-to-G comparison on the spectrum of a field

A coherent sheaf on the spectrum of a field has a finite-dimensional module
of global sections. Its finite basis gives an actual global finite free
sheaf. Thus the genuine vector-bundle inclusion is an exact equivalence,
and the induced canonical comparison is an isomorphism in every degree.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules
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

namespace AlgebraicGeometry.Scheme.Modules

variable (k : Type u) [Field k]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme
variable (k : Type u) [Field k]

/-- The K-theory map of the actual inverse exact functor over a field. -/
def GToKField (n : ℕ) :
    G (Spec (CommRingCat.of k)) n →* K (Spec (CommRingCat.of k)) n :=
  (AlgebraicGeometry.Scheme.Modules.coherentToVectorBundleFieldExact k).smallKMap.{u+1} n

/-- The inverse field comparison cancels the canonical exact-functor K-map. -/
@[simp]
theorem GToKField_comp_smallKMap (n : ℕ) :
    (GToKField k n).comp
      ((AlgebraicGeometry.Scheme.Modules.vectorBundleToCoherentExact (Spec (CommRingCat.of
        k))).smallKMap.{u+1} n) =
      MonoidHom.id (K (Spec (CommRingCat.of k)) n) := by
  change ((AlgebraicGeometry.Scheme.Modules.coherentToVectorBundleFieldExact k).smallKMap.{u+1}
    n).comp
      ((AlgebraicGeometry.Scheme.Modules.vectorBundleToCoherentExact (Spec (CommRingCat.of
        k))).smallKMap.{u+1} n) = _
  rw [← CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp]
  exact (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (AlgebraicGeometry.Scheme.Modules.vectorBundleFieldUnitIso k) n).trans
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_id.{u+1} _ n)

/-- The canonical exact-functor K-map cancels the inverse field comparison. -/
@[simp]
theorem smallKMap_comp_GToKField (n : ℕ) :
    ((AlgebraicGeometry.Scheme.Modules.vectorBundleToCoherentExact (Spec (CommRingCat.of
      k))).smallKMap.{u+1} n).comp
      (GToKField k n) = MonoidHom.id (G (Spec (CommRingCat.of k)) n) := by
  change ((AlgebraicGeometry.Scheme.Modules.vectorBundleToCoherentExact (Spec (CommRingCat.of
    k))).smallKMap.{u+1}
    n).comp
      ((AlgebraicGeometry.Scheme.Modules.coherentToVectorBundleFieldExact k).smallKMap.{u+1} n) = _
  rw [← CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp]
  exact (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (AlgebraicGeometry.Scheme.Modules.vectorBundleFieldCounitIso k)
    n).trans
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_id.{u+1} _ n)

/-- The canonical finite-locally-free K-to-coherent-G map is bijective on a
field spectrum, in every degree. -/
theorem KToG_field_bijective (n : ℕ) :
    Function.Bijective (KToG (Spec (CommRingCat.of k)) n) := by
  have hl := DFunLike.congr_fun (GToKField_comp_smallKMap k n)
  have hr := DFunLike.congr_fun (smallKMap_comp_GToKField k n)
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

/-- The canonical comparison as a multiplicative equivalence. Its forward
homomorphism is exactly `Scheme.KToG`, not a newly chosen unrelated map. -/
def KToGFieldEquiv (n : ℕ) :
    K (Spec (CommRingCat.of k)) n ≃* G (Spec (CommRingCat.of k)) n :=
  MulEquiv.ofBijective (KToG (Spec (CommRingCat.of k)) n) (KToG_field_bijective k n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem KToGFieldEquiv_coe (n : ℕ) :
    ↑(KToGFieldEquiv k n) = KToG (Spec (CommRingCat.of k)) n := rfl

end AlgebraicGeometry.Scheme
