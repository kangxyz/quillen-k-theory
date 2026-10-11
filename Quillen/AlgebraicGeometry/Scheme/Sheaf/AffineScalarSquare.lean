/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineScalarAdjunction
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.CartesianBaseChange
public import Quillen.Algebra.Category.ModuleCat.CartesianBaseChange
public import Mathlib.Algebra.Category.Ring.Constructions

/-! # The original affine pushforward square

The actual global-sections and tilde pushforward comparisons preserve the specified
geometric square. Reflection through the fully faithful spectrum functor supplies
the coordinate-ring pushout from the genuine cartesian square.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.SchemeSheaf
variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]
variable (h : IsPullback
  (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  (Spec.map (CommRingCat.ofHom (algebraMap S B)))
  (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (Spec.map (CommRingCat.ofHom (algebraMap R S))))
include h in
/-- A genuine cartesian spectrum square yields the original coordinate-ring pushout. -/
theorem isPushout_of_affineCartesian : Algebra.IsPushout R S A B := by
  apply CommRingCat.isPushout_iff_isPushout.mp
  have hp := h.of_map_of_faithful Scheme.Spec
  exact hp.unop

/-- Global sections preserve the original commutative pushforward square. -/
theorem affinePushforwardSquare_globalSections (N : (Spec (CommRingCat.of B)).Modules) :
    (pushforwardGlobalSectionsIso (CommRingCat.ofHom (algebraMap R A))).hom.app
        ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj N) ≫
      (ModuleCat.restrictScalars (algebraMap R A)).map
        ((pushforwardGlobalSectionsIso (CommRingCat.ofHom (algebraMap A B))).hom.app N) ≫
      (ModuleCat.scalarSquareIso R S A B).hom.app (moduleSpecΓFunctor.obj N) =
    moduleSpecΓFunctor.map
        ((cartesianPushforwardSquare _ _ _ _ h).hom.app N) ≫
      (pushforwardGlobalSectionsIso (CommRingCat.ofHom (algebraMap R S))).hom.app
        ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap S B)))).obj N) ≫
      (ModuleCat.restrictScalars (algebraMap R S)).map
        ((pushforwardGlobalSectionsIso (CommRingCat.ofHom (algebraMap S B))).hom.app N) := by
  apply ModuleCat.hom_ext
  ext m
  change m = N.presheaf.map (𝟙 _) m
  simp
/-- The actual tilde pushforward comparisons preserve the original pushforward square. -/
theorem tildePushforwardIso_square (N : ModuleCat B) :
    (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map
        ((tildePushforwardIso (CommRingCat.ofHom (algebraMap A B))).hom.app N) ≫
      (tildePushforwardIso (CommRingCat.ofHom (algebraMap R A))).hom.app
        ((ModuleCat.restrictScalars (algebraMap A B)).obj N) ≫
      (tilde.functor (CommRingCat.of R)).map ((ModuleCat.scalarSquareIso R S A B).hom.app N) =
    (cartesianPushforwardSquare _ _ _ _ h).hom.app (tilde N) ≫
      (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((tildePushforwardIso (CommRingCat.ofHom (algebraMap S B))).hom.app N) ≫
      (tildePushforwardIso (CommRingCat.ofHom (algebraMap R S))).hom.app
        ((ModuleCat.restrictScalars (algebraMap S B)).obj N) := by
  have : ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (tilde N)).IsQuasicoherent := isQuasicoherent_pushforward _ _
  have : ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (tilde N))).IsQuasicoherent := isQuasicoherent_pushforward _ _
  apply hom_eq_of_globalSections_eq (M :=
    (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (tilde N)))
  simp only [Functor.map_comp, tildePushforwardIso_globalSections_unit, Category.assoc]
  have hf := (pushforwardGlobalSectionsIso (CommRingCat.ofHom (algebraMap R A))).hom.naturality
    ((tildePushforwardIso (CommRingCat.ofHom (algebraMap A B))).hom.app N)
  have hj := (pushforwardGlobalSectionsIso (CommRingCat.ofHom (algebraMap R S))).hom.naturality
    ((tildePushforwardIso (CommRingCat.ofHom (algebraMap S B))).hom.app N)
  dsimp only [Functor.comp_map] at hf hj
  erw [reassoc_of% hf, reassoc_of% hj]
  simp only [tildePushforwardIso_globalSections_unit, Functor.map_comp, Category.assoc]
  erw [← (tilde.adjunction (R := CommRingCat.of R)).unit.naturality]
  simp only [Functor.id_map]
  simp only [tilde.adjunction, ← Functor.map_comp_assoc]
  erw [Iso.hom_inv_id_app, Iso.hom_inv_id_app]
  simp only [Functor.map_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  have hn := (ModuleCat.scalarSquareIso R S A B).hom.naturality
    ((tilde.toTildeΓNatIso (R := CommRingCat.of B)).inv.app N)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  have he := congrArg (fun q => q ≫
      (ModuleCat.restrictScalars (algebraMap R S)).map
        ((ModuleCat.restrictScalars (algebraMap S B)).map
          ((tilde.toTildeΓNatIso (R := CommRingCat.of B)).inv.app N)) ≫
      (tilde.toTildeΓNatIso (R := CommRingCat.of R)).hom.app
        ((ModuleCat.restrictScalars (algebraMap R S)).obj
          ((ModuleCat.restrictScalars (algebraMap S B)).obj N)))
    (affinePushforwardSquare_globalSections R S A B h (tilde N))
  simpa only [Category.assoc, Functor.comp_obj, tilde.functor_obj, CommRingCat.hom_ofHom] using he
end Quillen.SchemeSheaf
