/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Original naturality squares under a Cat-valued pseudofunctor

An ordinary natural transformation between base functors gives a strong transformation between
their composites with a fixed pseudofunctor. Its comparison is the original inverse composition
constraint, the image of the original square equality, and the original composition constraint.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
universe u v u' v' u'' v''
namespace Quillen.CategoryTheory.PseudofunctorNaturality
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (P : Pseudofunctor (LocallyDiscrete D) Cat.{v'', u''})
    {F G : C ⥤ D} (η : F ⟶ G)


/-- An original commuting base square, with all four arrows explicit. -/
def squareOfEq {a b a' b' : D} (f : a ⟶ b) (v : b ⟶ b') (u : a ⟶ a')
    (g : a' ⟶ b') (h : f ≫ v = u ≫ g) :
    P.map f.toLoc ≫ P.map v.toLoc ≅ P.map u.toLoc ≫ P.map g.toLoc :=
  (P.mapComp f.toLoc v.toLoc).symm ≪≫
    P.map₂Iso (eqToIso (Discrete.ext h)) ≪≫ P.mapComp u.toLoc g.toLoc

/-- The original square in ordinary functor notation, retaining its exact equality transport. -/
theorem squareOfEq_toNatIso {a b a' b' : D} (f : a ⟶ b) (v : b ⟶ b')
    (u : a ⟶ a') (g : a' ⟶ b') (h : f ≫ v = u ≫ g) :
    Cat.Hom.toNatIso (squareOfEq P f v u g h) =
      (Cat.Hom.toNatIso (P.mapComp f.toLoc v.toLoc)).symm ≪≫
        eqToIso (congrArg (fun k => (P.map k.toLoc).toFunctor) h) ≪≫
          Cat.Hom.toNatIso (P.mapComp u.toLoc g.toLoc) := by
  simp only [squareOfEq, PrelaxFunctor.map₂Iso_eqToIso]
  apply Iso.ext
  apply NatTrans.ext
  funext x
  simp only [Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv, Iso.trans_hom, Iso.symm_hom,
    Cat.Hom₂.comp_app, Cat.Hom₂.eqToHom_toNatTrans, eqToIso.hom, eqToHom_app,
    NatTrans.comp_app]

/-- The actual identity constraint with a specified original identity equation. -/
def idOfEq {a : D} (f : a ⟶ a) (h : f = 𝟙 a) : P.map f.toLoc ≅ 𝟙 (P.obj ⟨a⟩) :=
  P.map₂Iso (eqToIso (by rw [h]; rfl)) ≪≫ P.mapId ⟨a⟩

/-- The actual composition constraint with a specified original composition equation. -/
def compOfEq {a b c : D} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c)
    (h : fg = f ≫ g) : P.map fg.toLoc ≅ P.map f.toLoc ≫ P.map g.toLoc :=
  P.map₂Iso (eqToIso (by rw [h]; rfl)) ≪≫ P.mapComp f.toLoc g.toLoc

/-- The original square preserves the actual identity constraints. -/
theorem squareOfEq_id {a b : D} (u : a ⟶ b) (f : a ⟶ a) (g : b ⟶ b)
    (hf : f = 𝟙 a) (hg : g = 𝟙 b) (h : f ≫ u = u ≫ g) :
    (squareOfEq P f u u g h).hom ≫ P.map u.toLoc ◁ (idOfEq P g hg).hom =
      (idOfEq P f hf).hom ▷ P.map u.toLoc ≫
        (λ_ (P.map u.toLoc)).hom ≫ (ρ_ (P.map u.toLoc)).inv := by
  subst f
  subst g
  ext x
  simp [squareOfEq, idOfEq, P.mapComp_id_left_inv_app,
    P.mapComp_id_right_hom_app, Strict.leftUnitor_eqToIso,
    Strict.rightUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom]

/-- The original squares preserve the actual composition constraints. -/
theorem squareOfEq_comp {a b c a' b' c' : D}
    (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c')
    (u : a ⟶ a') (v : b ⟶ b') (w : c ⟶ c')
    (h₁ : f ≫ v = u ≫ f') (h₂ : g ≫ w = v ≫ g')
    (fg : a ⟶ c) (fg' : a' ⟶ c') (hfg : fg = f ≫ g) (hfg' : fg' = f' ≫ g')
    (h : fg ≫ w = u ≫ fg') :
    (squareOfEq P fg w u fg' h).hom ≫ P.map u.toLoc ◁ (compOfEq P f' g' fg' hfg').hom =
      (compOfEq P f g fg hfg).hom ▷ P.map w.toLoc ≫
        (α_ _ _ _).hom ≫ P.map f.toLoc ◁ (squareOfEq P g w v g' h₂).hom ≫
        (α_ _ _ _).inv ≫ (squareOfEq P f v u f' h₁).hom ▷ P.map g'.toLoc ≫
        (α_ _ _ _).hom := by
  subst fg
  subst fg'
  ext x
  simp only [squareOfEq, compOfEq, Iso.trans_hom, Iso.symm_hom,
    PrelaxFunctor.map₂Iso_hom, eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app, Cat.associator_hom_app,
    Cat.associator_inv_app, Functor.map_comp, Category.assoc,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  apply (cancel_epi ((P.mapComp (f ≫ g).toLoc w.toLoc).hom.toNatTrans.app x)).mp
  simp only [← Cat.Hom.toNatIso_hom, ← Cat.Hom.toNatIso_inv,
    Iso.hom_inv_id_app_assoc]
  have h₁t := eqToHom_naturality
    (fun k : a ⟶ b' => (P.mapComp k.toLoc g'.toLoc).hom.toNatTrans.app x) h₁
  have h₂t := eqToHom_naturality
    (fun k : b ⟶ c' => (P.mapComp f.toLoc k.toLoc).hom.toNatTrans.app x) h₂
  simp only [Quiver.Hom.comp_toLoc, Cat.Hom.comp_toFunctor, Functor.comp_obj,
    Cat.Hom.toNatIso_hom, PrelaxFunctor.map₂_id, Cat.Hom.toNatTrans_id, NatTrans.id_app,
    Category.id_comp, Functor.map_id, Cat.Hom.toNatIso_inv,
    P.mapComp_assoc_left_hom_app_assoc, Strict.associator_eqToIso, eqToIso.hom,
    PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  erw [reassoc_of% h₂t]
  simp only [Quiver.Hom.comp_toLoc, Cat.Hom.comp_toFunctor, Functor.comp_obj,
    ← Functor.map_comp, P.mapComp_assoc_right_hom_app_assoc, Strict.associator_eqToIso,
    eqToIso.inv, PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc, eqToHom_trans_assoc]
  simp only [Functor.map_comp, eqToHom_map]
  erw [reassoc_of% h₁t]
  erw [P.mapComp_assoc_right_hom_app]
  simp [Strict.associator_eqToIso, PrelaxFunctor.map₂_eqToHom]

/-- The specified base square is mapped through the two original composition constraints. -/
def square {a b : C} (f : a ⟶ b) :
    P.map (F.map f).toLoc ≫ P.map (η.app b).toLoc ≅
      P.map (η.app a).toLoc ≫ P.map (G.map f).toLoc :=
  squareOfEq P (F.map f) (η.app b) (η.app a) (G.map f) (η.naturality f)

/-- Original base naturality becomes strong naturality with the original pseudo constraints. -/
def strongTrans : Pseudofunctor.StrongTrans (F.toPseudofunctor.comp P)
    (G.toPseudofunctor.comp P) where
  app a := P.map (η.app a.as).toLoc
  naturality f := square P η f.as
  naturality_naturality {a b} {f g} α := by
    obtain rfl := LocallyDiscrete.eq_of_hom α
    have hα : α = 𝟙 f := Subsingleton.elim _ _
    subst hα
    simp
  naturality_id a :=
    squareOfEq_id P (η.app a.as) (F.map (𝟙 a.as)) (G.map (𝟙 a.as))
      (F.map_id a.as) (G.map_id a.as) (η.naturality (𝟙 a.as))
  naturality_comp f g :=
    squareOfEq_comp P (F.map f.as) (F.map g.as) (G.map f.as) (G.map g.as)
      (η.app _) (η.app _) (η.app _) (η.naturality f.as) (η.naturality g.as)
      (F.map (f.as ≫ g.as)) (G.map (f.as ≫ g.as)) (F.map_comp _ _) (G.map_comp _ _)
      (η.naturality (f.as ≫ g.as))

end Quillen.CategoryTheory.PseudofunctorNaturality
