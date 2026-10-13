/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Pullback
public import Quillen.AlgebraicGeometry.Scheme.KTheory
public import Quillen.CategoryTheory.SmallModel.Functoriality

/-!
# Contravariant vector-bundle K-theory on all schemes

The actual arbitrary-morphism bundle pullback induces `pullbackK`. Its identity
and composition laws follow from the geometric pullback isomorphisms, and on
open immersions it is the existing `restrictK`. This does not assert arbitrary
coherent G-theory pullback or substitute underived pullback for derived
pullback of perfect complexes.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Scheme
variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

/-- Contravariant pullback on genuine vector-bundle K-theory for every
scheme morphism. -/
def pullbackK (f : X ⟶ Y) (n : ℕ) : K Y n →* K X n :=
  (SchemeSheaf.vectorBundleExactPullback f).smallKMap n

/-- The public map uses exactly the actual geometric bundle pullback. -/
@[simp]
theorem pullbackK_eq_smallKMap (f : X ⟶ Y) (n : ℕ) :
    pullbackK f n = (SchemeSheaf.vectorBundleExactPullback f).smallKMap n := rfl

/-- Identity pullback is the identity on the original scheme K-groups. -/
@[simp high]
theorem pullbackK_id (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    pullbackK (𝟙 X) n = MonoidHom.id (K X n) := by
  exact (ExactFunctor.smallKMap_eq_of_natIso
    (F := SchemeSheaf.vectorBundleExactPullback (𝟙 X))
    (G := ExactFunctor.id (SchemeSheaf.vectorBundleExactStructure X))
    (SchemeSheaf.vectorBundlePullbackIdIso X) n).trans
    (ExactFunctor.smallKMap_id _ n)

/-- Actual bundle pullback is strictly contravariantly functorial on K-groups. -/
@[simp high]
theorem pullbackK_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    pullbackK (f ≫ g) n = (pullbackK f n).comp (pullbackK g n) := by
  exact (ExactFunctor.smallKMap_eq_of_natIso
    (F := SchemeSheaf.vectorBundleExactPullback (f ≫ g))
    (G := (SchemeSheaf.vectorBundleExactPullback g).comp
      (SchemeSheaf.vectorBundleExactPullback f))
    (SchemeSheaf.vectorBundlePullbackCompIso f g) n).trans
    (ExactFunctor.smallKMap_comp _ _ n)

/-- On an open immersion, the new pullback is exactly the existing geometric
open-restriction K-map. -/
theorem pullbackK_eq_restrictK (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    pullbackK j n = restrictK j n :=
  ExactFunctor.smallKMap_eq_of_natIso
    (F := SchemeSheaf.vectorBundleExactPullback j)
    (G := SchemeSheaf.vectorBundleExactRestrict j)
    (SchemeSheaf.vectorBundleRestrictIsoPullback j).symm n

/-- The vector-bundle K-group in each nonnegative degree forms a
contravariant functor on the full category of schemes. -/
def KFunctor (n : ℕ) : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (K X.unop n)
  map f := GrpCat.ofHom (pullbackK f.unop n)
  map_id X := by
    apply GrpCat.hom_ext
    exact pullbackK_id X.unop n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact pullbackK_comp g.unop f.unop n

/-- The functor retains the canonical pullback on each map. -/
@[simp]
theorem KFunctor_map {X Y : AlgebraicGeometry.Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) : ((KFunctor n).map f).hom = pullbackK f.unop n := rfl

/-- A scheme isomorphism induces inverse K-theory pullbacks. -/
theorem pullbackK_iso_hom_inv (e : X ≅ Y) (n : ℕ) :
    (pullbackK e.hom n).comp (pullbackK e.inv n) = MonoidHom.id (K X n) := by
  rw [← pullbackK_comp, e.hom_inv_id, pullbackK_id]

end Quillen.Scheme
