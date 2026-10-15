/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomNodeFunctors

/-! Canonical reference algebra for the original Bass chart/bottom node comparison. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u v
namespace Quillen.PerfectComplexes.BassReferenceMerge

section Small
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

/--
Transport a natural isomorphism to the `AsSmall` functors by whiskering with `AsSmall.down` and
`AsSmall.up`.
-/
def smallIso {F G : C ⥤ D} (e : F ≅ G) :
    (AsSmall.down ⋙ F ⋙ AsSmall.up) ≅ (AsSmall.down ⋙ G ⋙ AsSmall.up) :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight e AsSmall.up)

theorem smallIso_trans {F G H : C ⥤ D} (e : F ≅ G) (f : G ≅ H) :
    smallIso (e ≪≫ f) = smallIso e ≪≫ smallIso f := by
  apply Iso.ext
  simp only [smallIso, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_comp, whiskerRight_comp]

theorem smallIso_precomp (F : C ⥤ D) {G H : D ⥤ E} (e : G ≅ H) :
    isoWhiskerLeft (AsSmall.down ⋙ F ⋙ AsSmall.up) (smallIso e) =
      smallIso (isoWhiskerLeft F e) := by
  apply Iso.ext
  ext X
  rfl

theorem smallIso_postcomp {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ E) :
    isoWhiskerRight (smallIso e) (AsSmall.down ⋙ H ⋙ AsSmall.up) =
      smallIso (isoWhiskerRight e H) := by
  apply Iso.ext
  ext X
  rfl

theorem smallIso_eqToIso {F G : C ⥤ D} (h : F = G) :
    smallIso (eqToIso h) =
      eqToIso (congrArg (fun K ↦ AsSmall.down ⋙ K ⋙ AsSmall.up) h) := by
  subst G
  rfl

theorem composition_pair_iso {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ E}
    (e : F₀ ≅ F₁) (f : G₀ ≅ G₁) :
    (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod f) =
      isoWhiskerRight e G₀ ≪≫ isoWhiskerLeft F₁ f := by
  apply Iso.ext
  rfl
end Small

/-- Equality transports of a binary factorization are the canonical ones. -/
theorem comp_change_source {X Y Z : Scheme.{u}} {f f' : X ⟶ Y}
    (e : f = f') (g : Y ⟶ Z) :
    eqToIso (congrArg boundedFlatNormalizedPullback (congrArg (fun k ↦ k ≫ g) e)) ≪≫
      boundedFlatNormalizedPullbackCompIso f' g =
      boundedFlatNormalizedPullbackCompIso f g ≪≫
        isoWhiskerLeft (boundedFlatNormalizedPullback g)
          (eqToIso (congrArg boundedFlatNormalizedPullback e)) := by
  subst f'
  simp

/-- The analogous actual equality transport in the other binary factor. -/
theorem comp_change_target {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g g' : Y ⟶ Z}
    (e : g = g') :
    eqToIso (congrArg boundedFlatNormalizedPullback (congrArg (fun k ↦ f ≫ k) e)) ≪≫
      boundedFlatNormalizedPullbackCompIso f g' =
      boundedFlatNormalizedPullbackCompIso f g ≪≫
        isoWhiskerRight (eqToIso (congrArg boundedFlatNormalizedPullback e))
          (boundedFlatNormalizedPullback f) := by
  subst g'
  simp

/-- The anchored three-factor routes agree, retaining actual association transports. -/
theorem anchored_three_routes {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (w : X ⟶ T)
    (el : w = (f ≫ g) ≫ h) (er : w = f ≫ g ≫ h) :
    eqToIso (congrArg boundedFlatNormalizedPullback el) ≪≫
      boundedFlatNormalizedPullbackCompIso (f ≫ g) h ≪≫
        isoWhiskerLeft (boundedFlatNormalizedPullback h)
          (boundedFlatNormalizedPullbackCompIso f g) =
    eqToIso (congrArg boundedFlatNormalizedPullback er) ≪≫
      boundedFlatNormalizedPullbackCompIso f (g ≫ h) ≪≫
        isoWhiskerRight (boundedFlatNormalizedPullbackCompIso g h)
          (boundedFlatNormalizedPullback f) ≪≫
        Functor.associator (boundedFlatNormalizedPullback h)
          (boundedFlatNormalizedPullback g) (boundedFlatNormalizedPullback f) := by
  subst w
  apply Iso.ext
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom]
  have ht := boundedFlatNormalizedPullbackCompIso_two_routes f g h
  have hh := congrArg (fun η ↦
    eqToHom (congrArg boundedFlatNormalizedPullback (Category.assoc f g h)) ≫ η) ht
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] using hh.symm

/-- The same canonical three-factor equality with both actual equality transports retained. -/
theorem anchored_factorizations {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (d : X ⟶ Z) (e : Y ⟶ T) (w : X ⟶ T)
    (hd : d = f ≫ g) (he : e = g ≫ h) (hl : w = d ≫ h) (hr : w = f ≫ e) :
    eqToIso (congrArg boundedFlatNormalizedPullback hl) ≪≫
      boundedFlatNormalizedPullbackCompIso d h ≪≫
        isoWhiskerLeft (boundedFlatNormalizedPullback h)
          (eqToIso (congrArg boundedFlatNormalizedPullback hd) ≪≫
            boundedFlatNormalizedPullbackCompIso f g) =
    eqToIso (congrArg boundedFlatNormalizedPullback hr) ≪≫
      boundedFlatNormalizedPullbackCompIso f e ≪≫
        isoWhiskerRight
          (eqToIso (congrArg boundedFlatNormalizedPullback he) ≪≫
            boundedFlatNormalizedPullbackCompIso g h) (boundedFlatNormalizedPullback f) ≪≫
        Functor.associator (boundedFlatNormalizedPullback h)
          (boundedFlatNormalizedPullback g) (boundedFlatNormalizedPullback f) := by
  subst d
  subst e
  simpa only [eqToIso_refl, Iso.refl_trans] using anchored_three_routes f g h w hl hr

/-- The same reference equality at the literally associated original functors. -/
theorem anchored_factorizations_strict {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (d : X ⟶ Z) (e : Y ⟶ T) (w : X ⟶ T)
    (hd : d = f ≫ g) (he : e = g ≫ h) (hl : w = d ≫ h) (hr : w = f ≫ e) :
    eqToIso (congrArg boundedFlatNormalizedPullback hl) ≪≫
      boundedFlatNormalizedPullbackCompIso d h ≪≫
        isoWhiskerLeft (boundedFlatNormalizedPullback h)
          (eqToIso (congrArg boundedFlatNormalizedPullback hd) ≪≫
            boundedFlatNormalizedPullbackCompIso f g) =
    eqToIso (congrArg boundedFlatNormalizedPullback hr) ≪≫
      boundedFlatNormalizedPullbackCompIso f e ≪≫
        isoWhiskerRight
          (eqToIso (congrArg boundedFlatNormalizedPullback he) ≪≫
            boundedFlatNormalizedPullbackCompIso g h) (boundedFlatNormalizedPullback f) := by
  have hA : Functor.associator (boundedFlatNormalizedPullback h)
      (boundedFlatNormalizedPullback g) (boundedFlatNormalizedPullback f) = Iso.refl _ := rfl
  simpa only [hA, Iso.trans_refl] using anchored_factorizations f g h d e w hd he hl hr

end Quillen.PerfectComplexes.BassReferenceMerge
