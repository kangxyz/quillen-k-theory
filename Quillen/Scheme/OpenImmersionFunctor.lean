import Quillen.Scheme.RestrictionFunctoriality
import Quillen.Scheme.Comparison.KToG
import Mathlib.CategoryTheory.Widesubcategory

/-!
# Group-valued K- and G-theory functors for open immersions

The domain category explicitly restricts morphisms to open immersions.
G-theory and the K-to-G comparison are further restricted to locally
noetherian objects. Every map is the public geometric restriction map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Scheme

/-- Schemes with only open immersions as morphisms. -/
abbrev OpenImmersionSchemes :=
  WideSubcategory (@IsOpenImmersion : MorphismProperty AlgebraicGeometry.Scheme.{u})

instance openImmersionSchemes_isOpenImmersion {X Y : OpenImmersionSchemes.{u}}
    (f : X ⟶ Y) : IsOpenImmersion f.hom := f.property

/-- Local noetherianity as an object property of the open-immersion category. -/
abbrev locallyNoetherianOpenSchemeProperty : ObjectProperty OpenImmersionSchemes.{u} :=
  fun X => IsLocallyNoetherian X.obj

/-- Locally noetherian schemes with only open immersions as morphisms. -/
abbrev LocallyNoetherianOpenSchemes :=
  locallyNoetherianOpenSchemeProperty.{u}.FullSubcategory

instance locallyNoetherianOpenSchemes_isLocallyNoetherian
    (X : LocallyNoetherianOpenSchemes.{u}) : IsLocallyNoetherian X.obj.obj := X.property

/-- The inclusion retains the open-immersion restriction on morphisms. -/
abbrev locallyNoetherianOpenSchemesInclusion :
    LocallyNoetherianOpenSchemes.{u} ⥤ OpenImmersionSchemes.{u} :=
  locallyNoetherianOpenSchemeProperty.{u}.ι

/-- Genuine scheme K-theory as a contravariant group-valued functor on open immersions. -/
def KOpenFunctor (n : ℕ) : OpenImmersionSchemes.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (K X.unop.obj n)
  map f := GrpCat.ofHom (restrictK f.unop.hom n)
  map_id X := by
    apply GrpCat.hom_ext
    exact restrictK_id X.unop.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact restrictK_comp g.unop.hom f.unop.hom n

/-- The K-functor's morphism is definitionally the original public restriction map. -/
@[simp]
theorem KOpenFunctor_map {X Y : OpenImmersionSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((KOpenFunctor n).map f).hom = restrictK f.unop.hom n := rfl

/-- K-theory on the locally noetherian open-immersion category. -/
abbrev KLocallyNoetherianOpenFunctor (n : ℕ) :
    LocallyNoetherianOpenSchemes.{u}ᵒᵖ ⥤ GrpCat.{u + 1} :=
  locallyNoetherianOpenSchemesInclusion.op ⋙ KOpenFunctor n

/-- Genuine coherent G-theory as a contravariant functor on locally noetherian
schemes and open immersions. -/
def GOpenFunctor (n : ℕ) : LocallyNoetherianOpenSchemes.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (G X.unop.obj.obj n)
  map f := GrpCat.ofHom (restrictG f.unop.hom.hom n)
  map_id X := by
    apply GrpCat.hom_ext
    exact restrictG_id X.unop.obj.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact restrictG_comp g.unop.hom.hom f.unop.hom.hom n

/-- The G-functor's morphism is definitionally the original public restriction map. -/
@[simp]
theorem GOpenFunctor_map {X Y : LocallyNoetherianOpenSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((GOpenFunctor n).map f).hom = restrictG f.unop.hom.hom n := rfl

/-- The canonical vector-bundle inclusion forms a natural transformation from
K-theory to G-theory on locally noetherian schemes and open immersions. -/
def KToGOpenNatTrans (n : ℕ) :
    KLocallyNoetherianOpenFunctor.{u} n ⟶ GOpenFunctor n where
  app X := GrpCat.ofHom (KToG X.unop.obj.obj n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (KToG_restrict f.unop.hom.hom n).symm

/-- The bundled comparison retains the existing canonical public comparison. -/
@[simp]
theorem KToGOpenNatTrans_app (n : ℕ) (X : LocallyNoetherianOpenSchemes.{u}ᵒᵖ) :
    ((KToGOpenNatTrans n).app X).hom = KToG X.unop.obj.obj n := rfl

end Quillen.Scheme
