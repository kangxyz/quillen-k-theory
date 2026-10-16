/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.GrothendieckCocartesianIso

/-!
# Original fiber maps of lifted Grothendieck arrows

Only the supplied base equalities are transported. Strong cocartesianness proves that the
resulting original fiber map is invertible, without choosing a replacement functor.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckFiber
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})
  {R S : C} (f : R ⟶ S)
  {x : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R}
  {y : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S}
  (φ : x.val ⟶ y.val) [(Pseudofunctor.Grothendieck.forget F).IsHomLift f φ]

/-- The actual fiber component, with its proved base equalities transported. -/
def liftedMap : (F.map f.toLoc).toFunctor.obj (originalObject F R x) ⟶
    originalObject F S y := by
  rcases x with ⟨⟨R', x⟩, hx⟩
  rcases y with ⟨⟨S', y⟩, hy⟩
  change R' = R at hx
  change S' = S at hy
  subst R'
  subst S'
  have hf : φ.base = f := by
    simpa using IsHomLift.fac' (Pseudofunctor.Grothendieck.forget F) f φ
  exact eqToHom (by rw [hf]; rfl) ≫ φ.fiber

/-- For already literal base objects, this is the original fiber component after base transport. -/
theorem liftedMap_mk (a : F.obj ⟨R⟩) (b : F.obj ⟨S⟩)
    (ψ : (⟨R, a⟩ : Pseudofunctor.Grothendieck F) ⟶ ⟨S, b⟩)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f ψ]
    (h : ψ.base = f) :
    liftedMap F f (x := ⟨⟨R, a⟩, rfl⟩) (y := ⟨⟨S, b⟩, rfl⟩) ψ =
      eqToHom (by rw [h]; rfl) ≫ ψ.fiber := rfl

/-- A strongly cocartesian arrow supplies an isomorphism on the original fibers. -/
theorem isIso_liftedMap
    [(Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian f φ] :
    IsIso (liftedMap F f φ) := by
  rcases x with ⟨⟨R', x⟩, hx⟩
  rcases y with ⟨⟨S', y⟩, hy⟩
  change R' = R at hx
  change S' = S at hy
  subst R'
  subst S'
  have hf : φ.base = f := by
    simpa using IsHomLift.fac' (Pseudofunctor.Grothendieck.forget F) f φ
  have : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian φ.base φ :=
    hf.symm ▸ inferInstance
  have : IsIso φ.fiber := GrothendieckCocartesian.isIso_fiber F φ
  rw [liftedMap_mk F f x y φ hf]
  infer_instance

/-- Mapping the concrete inverse back to the actual fiber retains only canonical base transports. -/
theorem toFiber_map_fromFiber_map {x y : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R}
    (a : x ⟶ y) :
    (toFiber F R).map ((fromFiber F R).map a) =
      eqToHom (toFiber_originalObject F R x) ≫ a ≫
        eqToHom (toFiber_originalObject F R y).symm :=
  (toFiber F R).map_preimage _

attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- A literal original Grothendieck square gives the actual naturality equation on fiber maps. -/
theorem fiber_square {a b : F.obj ⟨R⟩} {c d : F.obj ⟨S⟩}
    (α : a ⟶ b) (β : c ⟶ d)
    (p : (F.map f.toLoc).toFunctor.obj a ⟶ c)
    (q : (F.map f.toLoc).toFunctor.obj b ⟶ d)
    (h : (inclusion F R).map α ≫
        (⟨f, q⟩ : (⟨R, b⟩ : Pseudofunctor.Grothendieck F) ⟶ ⟨S, d⟩) =
      (⟨f, p⟩ : (⟨R, a⟩ : Pseudofunctor.Grothendieck F) ⟶ ⟨S, c⟩) ≫
        (inclusion F S).map β) :
    (F.map f.toLoc).toFunctor.map α ≫ q = p ≫ β := by
  have he := (Pseudofunctor.Grothendieck.Hom.ext_iff _ _).mp h
  obtain ⟨e, he⟩ := he
  simp only [inclusion, Pseudofunctor.Grothendieck.categoryStruct_comp_fiber] at he
  simp only [Quiver.Hom.id_toLoc, Cat.Hom.id_toFunctor, Functor.id_obj,
    Pseudofunctor.Grothendieck.categoryStruct_comp_base, Quiver.Hom.comp_toLoc,
    F.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso, eqToIso.hom,
    PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
    Functor.map_comp, Category.assoc, eqToHom_trans_assoc, F.mapComp_id_right_hom_app,
    Strict.rightUnitor_eqToIso, NatTrans.naturality_assoc, Functor.id_map,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc] at he
  simp only [← Cat.Hom.toNatIso_inv, ← Cat.Hom.toNatIso_hom,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc] at he
  exact (cancel_epi _).mp he

/-- The original maps extracted from a genuine lifted square satisfy naturality. -/
theorem liftedMap_naturality
    {x x' : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R}
    {y y' : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S}
    (α : x ⟶ x') (β : y ⟶ y') (p : x.val ⟶ y.val) (q : x'.val ⟶ y'.val)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f p]
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f q]
    (h : α.val ≫ q = p ≫ β.val) :
    (F.map f.toLoc).toFunctor.map ((fromFiber F R).map α) ≫ liftedMap F f q =
      liftedMap F f p ≫ (fromFiber F S).map β := by
  rcases x with ⟨⟨R₁, x⟩, hx⟩
  rcases x' with ⟨⟨R₂, x'⟩, hx'⟩
  rcases y with ⟨⟨S₁, y⟩, hy⟩
  rcases y' with ⟨⟨S₂, y'⟩, hy'⟩
  change R₁ = R at hx
  change R₂ = R at hx'
  change S₁ = S at hy
  change S₂ = S at hy'
  subst R₁
  subst R₂
  subst S₁
  subst S₂
  have hp : p.base = f := by
    simpa using IsHomLift.fac' (Pseudofunctor.Grothendieck.forget F) f p
  have hq : q.base = f := by
    simpa using IsHomLift.fac' (Pseudofunctor.Grothendieck.forget F) f q
  rcases p with ⟨fp, p⟩
  rcases q with ⟨fq, q⟩
  change fp = f at hp
  change fq = f at hq
  subst fp
  subst fq
  have ha := congrArg Subtype.val (toFiber_map_fromFiber_map F α)
  have hb := congrArg Subtype.val (toFiber_map_fromFiber_map F β)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at ha hb
  change (inclusion F R).map ((fromFiber F R).map α) = α.val at ha
  change (inclusion F S).map ((fromFiber F S).map β) = β.val at hb
  rw [liftedMap_mk F f x' y' _ rfl, liftedMap_mk F f x y _ rfl]
  simp only [eqToHom_refl, Category.id_comp]
  apply fiber_square F f
  rw [ha, hb]
  exact h

end Quillen.CategoryTheory.GrothendieckFiber
