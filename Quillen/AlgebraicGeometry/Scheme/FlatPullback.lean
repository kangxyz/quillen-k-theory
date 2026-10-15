/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.FlatPullback
public import Quillen.AlgebraicGeometry.Scheme.Pullback
public import Quillen.AlgebraicGeometry.Scheme.Comparison.KToG
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Genuine flat functoriality of coherent G-theory

The actual flat coherent pullback induces maps on the existing G-groups.
Identity, composition, and agreement with open restriction follow from the
original geometric comparison isomorphisms. The original K-to-G comparison
is natural for these actual flat pullbacks.
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
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

/-- Pullback on the existing coherent G-groups along a flat scheme morphism. -/
def pullbackG (f : X ⟶ Y) [Flat f] (n : ℕ) : G Y n →* G X n :=
  (CoherentScheme.coherentExactPullback f).smallKMap n

/-- The public G-map uses precisely actual geometric coherent pullback. -/
@[simp] theorem pullbackG_eq_smallKMap (f : X ⟶ Y) [Flat f] (n : ℕ) :
    pullbackG f n = (CoherentScheme.coherentExactPullback f).smallKMap n := rfl

/-- Identity pullback is the identity on the original coherent G-groups. -/
@[simp high] theorem pullbackG_id (X : AlgebraicGeometry.Scheme.{u})
    [IsLocallyNoetherian X] (n : ℕ) :
    pullbackG (𝟙 X) n = MonoidHom.id (G X n) := by
  exact (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso
    (F := CoherentScheme.coherentExactPullback (𝟙 X))
    (G := CategoryTheory.ExactCategory.ExactFunctor.id (CoherentScheme.coherentExactStructure X))
    (CoherentScheme.coherentPullbackIdIso X) n).trans
      (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_id _ n)

/-- Flat pullbacks are contravariantly functorial on coherent G-groups. -/
@[simp high] theorem pullbackG_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [Flat f] [Flat g] (n : ℕ) :
    pullbackG (f ≫ g) n = (pullbackG f n).comp (pullbackG g n) := by
  exact (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso
    (F := CoherentScheme.coherentExactPullback (f ≫ g))
    (G := (CoherentScheme.coherentExactPullback g).comp
      (CoherentScheme.coherentExactPullback f))
    (CoherentScheme.coherentPullbackCompIso f g) n).trans
      (CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp _ _ n)

/-- Flat pullback agrees with the original open-restriction G-map. -/
theorem pullbackG_eq_restrictG (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    pullbackG j n = restrictG j n :=
  CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso
    (F := CoherentScheme.coherentExactPullback j)
    (G := CoherentScheme.coherentRestrictionExact j)
    (CoherentScheme.coherentRestrictionIsoPullback j).symm n

omit [IsLocallyNoetherian X] in
/-- The actual bundle-to-coherent inclusion commutes with arbitrary pullback
as a functor, before flatness is needed for the coherent exact structure. -/
theorem vectorBundleToCoherent_pullback (f : X ⟶ Y) :
    SchemeSheaf.vectorBundleToCoherent Y ⋙ CoherentScheme.coherentPullback f =
      SchemeSheaf.vectorBundlePullback f ⋙ SchemeSheaf.vectorBundleToCoherent X := rfl

/-- Naturality of the original canonical K-to-G map for actual flat pullback. -/
theorem KToG_pullback (f : X ⟶ Y) [Flat f] (n : ℕ) :
    (pullbackG f n).comp (KToG Y n) = (KToG X n).comp (pullbackK f n) := by
  change ((CoherentScheme.coherentExactPullback f).smallKMap n).comp
      ((SchemeSheaf.vectorBundleToCoherentExact Y).smallKMap n) =
    ((SchemeSheaf.vectorBundleToCoherentExact X).smallKMap n).comp
      ((SchemeSheaf.vectorBundleExactPullback f).smallKMap n)
  rw [← CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, ←
    CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp]
  exact CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso (Iso.refl _) n

/-- Elementwise naturality retains the same canonical comparison maps. -/
theorem KToG_pullback_apply (f : X ⟶ Y) [Flat f] (n : ℕ) (x : K Y n) :
    pullbackG f n (KToG Y n x) = KToG X n (pullbackK f n x) :=
  DFunLike.congr_fun (KToG_pullback f n) x

/-- Schemes with genuinely flat scheme morphisms. -/
abbrev FlatSchemes := WideSubcategory (@Flat : MorphismProperty AlgebraicGeometry.Scheme.{u})

instance flatSchemes_flat {X Y : FlatSchemes.{u}} (f : X ⟶ Y) : Flat f.hom := f.property

/-- The actual locally noetherian object property on flat schemes. -/
abbrev locallyNoetherianFlatSchemeProperty : ObjectProperty FlatSchemes.{u} :=
  fun X => IsLocallyNoetherian X.obj

/-- Locally noetherian schemes with flat morphisms. -/
abbrev LocallyNoetherianFlatSchemes := locallyNoetherianFlatSchemeProperty.{u}.FullSubcategory

instance locallyNoetherianFlatSchemes_isLocallyNoetherian
    (X : LocallyNoetherianFlatSchemes.{u}) : IsLocallyNoetherian X.obj.obj := X.property

/-- Vector-bundle K-theory restricted to flat maps of locally noetherian schemes. -/
def KLocallyNoetherianFlatFunctor (n : ℕ) :
    LocallyNoetherianFlatSchemes.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (K X.unop.obj.obj n)
  map f := GrpCat.ofHom (pullbackK f.unop.hom.hom n)
  map_id X := by
    apply GrpCat.hom_ext
    exact pullbackK_id X.unop.obj.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact pullbackK_comp g.unop.hom.hom f.unop.hom.hom n

/-- Genuine coherent G-theory is contravariant for flat locally noetherian maps. -/
def GFlatFunctor (n : ℕ) : LocallyNoetherianFlatSchemes.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (G X.unop.obj.obj n)
  map f := GrpCat.ofHom (pullbackG f.unop.hom.hom n)
  map_id X := by
    apply GrpCat.hom_ext
    exact pullbackG_id X.unop.obj.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact pullbackG_comp g.unop.hom.hom f.unop.hom.hom n

/-- The bundled G-functor retains actual flat pullback. -/
@[simp] theorem GFlatFunctor_map {X Y : LocallyNoetherianFlatSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) : ((GFlatFunctor n).map f).hom = pullbackG f.unop.hom.hom n := rfl

/-- The original K-to-G comparison is a natural transformation on flat maps. -/
def KToGFlatNatTrans (n : ℕ) : KLocallyNoetherianFlatFunctor.{u} n ⟶ GFlatFunctor n where
  app X := GrpCat.ofHom (KToG X.unop.obj.obj n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (KToG_pullback f.unop.hom.hom n).symm

/-- The bundled comparison retains the original public K-to-G map. -/
@[simp] theorem KToGFlatNatTrans_app (n : ℕ) (X : LocallyNoetherianFlatSchemes.{u}ᵒᵖ) :
    ((KToGFlatNatTrans n).app X).hom = KToG X.unop.obj.obj n := rfl

end Quillen.Scheme
