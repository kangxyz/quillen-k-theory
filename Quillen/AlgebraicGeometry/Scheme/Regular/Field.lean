/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Comparison.KToG
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.Comparison
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The canonical K-to-G comparison on the spectrum of a field

A coherent sheaf on the spectrum of a field has a finite-dimensional module
of global sections. Its finite basis gives an actual global finite free
sheaf. Thus the genuine vector-bundle inclusion is an exact equivalence,
and the induced canonical comparison is an isomorphism in every degree.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.SchemeSheaf


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- A genuinely finite free module gives a finite locally free sheaf by
transporting its basis through the actual tilde/free-sheaf comparison. -/
theorem finiteLocallyFree_tilde_of_finite_free (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] :
    IsFiniteLocallyFree (Spec R) (tilde M) := by
  let b := Module.Free.chooseBasis R M
  let e : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (Module.Free.ChooseBasisIndex R M) ≅ tilde M :=
    (tildeFinsupp (Module.Free.ChooseBasisIndex R M)).symm ≪≫
      (tilde.functor R).mapIso b.repr.symm.toModuleIso
  exact finiteLocallyFree_of_iso e

variable (k : Type u) [Field k]

/-- On the spectrum of a field, every actual coherent sheaf is finite
locally free. The proof chooses a finite basis of global sections. -/
theorem finiteLocallyFree_of_coherent_field
    (M : (Spec (CommRingCat.of k)).Modules)
    (hM : AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (Spec
      (CommRingCat.of k)) M) :
    IsFiniteLocallyFree (Spec (CommRingCat.of k)) M := by
  have h := (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_spec_iff
    (CommRingCat.of k) M).mp hM
  have : M.IsQuasicoherent := h.1
  have : Module.Finite k (moduleSpecΓFunctor.obj M) := h.2
  have : IsFiniteLocallyFree (Spec (CommRingCat.of k))
      (tilde (moduleSpecΓFunctor.obj M)) :=
    finiteLocallyFree_tilde_of_finite_free (CommRingCat.of k) _
  let e : tilde (moduleSpecΓFunctor.obj M) ≅ M := asIso M.fromTildeΓ
  exact finiteLocallyFree_of_iso e

/-- The inverse to the actual vector-bundle inclusion on a field spectrum.
It retains the sheaf and every sheaf morphism. -/
def coherentToVectorBundleField :
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves (Spec (CommRingCat.of k)) ⥤
      FiniteLocallyFree (Spec (CommRingCat.of k)) :=
  ObjectProperty.ιOfLE (fun M hM => finiteLocallyFree_of_coherent_field k M hM)

instance coherentToVectorBundleField_additive : (coherentToVectorBundleField k).Additive where
  map_add := by intros; rfl

/-- The inverse preserves actual short exact sheaf sequences. -/
def coherentToVectorBundleFieldExact :
    ExactFunctor (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure (Spec
      (CommRingCat.of k)))
      (vectorBundleExactStructure (Spec (CommRingCat.of k))) where
  toFunctor := coherentToVectorBundleField k
  map_conflation S hS :=
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherent_shortExact_iff (Spec (CommRingCat.of k))
      S).mp hS

/-- Inclusion followed by the field inverse keeps the same vector bundle. -/
def vectorBundleFieldUnitIso :
    ((vectorBundleToCoherentExact (Spec (CommRingCat.of k))).comp
      (coherentToVectorBundleFieldExact k)).toFunctor ≅
      (CategoryTheory.ExactCategory.ExactFunctor.id (vectorBundleExactStructure (Spec
        (CommRingCat.of k)))).toFunctor :=
  Iso.refl _

/-- The field inverse followed by inclusion keeps the same coherent sheaf. -/
def vectorBundleFieldCounitIso :
    ((coherentToVectorBundleFieldExact k).comp
      (vectorBundleToCoherentExact (Spec (CommRingCat.of k)))).toFunctor ≅
      (CategoryTheory.ExactCategory.ExactFunctor.id
        (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
        (Spec (CommRingCat.of k)))).toFunctor :=
  Iso.refl _

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
