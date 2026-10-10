/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.HomotopyPushoutQuasiIso

/-! # Actual additive restriction of the homotopy pushout -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]
  {T A B : CochainComplex C ℤ} (f : T ⟶ A) (g : T ⟶ B)

/-- Additive termwise functors preserve the literal cone pushout by a genuine isomorphism. -/
def homotopyPushoutMapIso :
    (F.mapHomologicalComplex (.up ℤ)).obj (homotopyPushout f g) ≅
      homotopyPushout ((F.mapHomologicalComplex (.up ℤ)).map f)
        ((F.mapHomologicalComplex (.up ℤ)).map g) :=
  homotopyCofiber.mapHomologicalComplexObjIso _ F ≪≫
    homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j-1, by dsimp; omega⟩)
      (Arrow.isoMk (Iso.refl _) ((F.mapHomologicalComplex (.up ℤ)).mapBiprod A B) (by
        apply biprod.hom_ext <;> simp [← Functor.map_comp]))

/-- The isomorphism preserves the original first inclusion exactly. -/
@[reassoc (attr := simp)]
lemma homotopyPushoutMapIso_inl :
    (F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutInl f g) ≫
      (homotopyPushoutMapIso F f g).hom =
    homotopyPushoutInl ((F.mapHomologicalComplex (.up ℤ)).map f)
      ((F.mapHomologicalComplex (.up ℤ)).map g) := by
  dsimp [homotopyPushoutMapIso, homotopyPushoutInl, homotopyPushout, CochainComplex.mappingCone.inr,
    homotopyCofiber.mapArrowHom]
  rw [Functor.map_comp, Category.assoc,
    homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc,
    homotopyCofiber.inr_desc, ← Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [← Functor.map_comp]

/-- The isomorphism preserves the original second inclusion exactly. -/
@[reassoc (attr := simp)]
lemma homotopyPushoutMapIso_inr :
    (F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutInr f g) ≫
      (homotopyPushoutMapIso F f g).hom =
    homotopyPushoutInr ((F.mapHomologicalComplex (.up ℤ)).map f)
      ((F.mapHomologicalComplex (.up ℤ)).map g) := by
  dsimp [homotopyPushoutMapIso, homotopyPushoutInr, homotopyPushout, CochainComplex.mappingCone.inr,
    homotopyCofiber.mapArrowHom]
  rw [Functor.map_comp, Category.assoc,
    homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc,
    homotopyCofiber.inr_desc, ← Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [← Functor.map_comp]

/-- Weakness of the restricted overlap leg suffices for the original restricted first inclusion. -/
lemma quasiIso_map_homotopyPushoutInl
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map g)] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutInl f g)) := by
  have := quasiIso_homotopyPushoutInl ((F.mapHomologicalComplex (.up ℤ)).map f)
    ((F.mapHomologicalComplex (.up ℤ)).map g)
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutInl f g) ≫
      (homotopyPushoutMapIso F f g).hom) := by
    rw [homotopyPushoutMapIso_inl]
    infer_instance
  exact (quasiIso_iff_comp_right _ _).mp this

/-- Symmetric actual restriction statement. -/
lemma quasiIso_map_homotopyPushoutInr
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f)] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutInr f g)) := by
  have := quasiIso_homotopyPushoutInr ((F.mapHomologicalComplex (.up ℤ)).map f)
    ((F.mapHomologicalComplex (.up ℤ)).map g)
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutInr f g) ≫
      (homotopyPushoutMapIso F f g).hom) := by
    rw [homotopyPushoutMapIso_inr]
    infer_instance
  exact (quasiIso_iff_comp_right _ _).mp this

/-- A locally weak original first target map and overlap leg make the actual
mapped descent quasi-isomorphic; no global weakness assumption is needed. -/
lemma quasiIso_map_homotopyPushoutDesc {M : CochainComplex C ℤ}
    (a : A ⟶ M) (b : B ⟶ M) (H : Homotopy (f ≫ a) (g ≫ b))
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map g)]
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map a)] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutDesc f g a b H)) := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  have := quasiIso_map_homotopyPushoutInl F f g
  have he : FC.map (homotopyPushoutInl f g) ≫ FC.map (homotopyPushoutDesc f g a b H) =
      FC.map a := by rw [← FC.map_comp, homotopyPushoutInl_desc]
  have : QuasiIso (FC.map (homotopyPushoutInl f g) ≫
      FC.map (homotopyPushoutDesc f g a b H)) := by rw [he]; infer_instance
  exact (quasiIso_iff_comp_left _ _).mp this

/-- Symmetric local target-map gluing with literal original mapped descent. -/
lemma quasiIso_map_homotopyPushoutDesc_of_inr {M : CochainComplex C ℤ}
    (a : A ⟶ M) (b : B ⟶ M) (H : Homotopy (f ≫ a) (g ≫ b))
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f)]
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map b)] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutDesc f g a b H)) := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  have := quasiIso_map_homotopyPushoutInr F f g
  have he : FC.map (homotopyPushoutInr f g) ≫ FC.map (homotopyPushoutDesc f g a b H) =
      FC.map b := by rw [← FC.map_comp, homotopyPushoutInr_desc]
  have : QuasiIso (FC.map (homotopyPushoutInr f g) ≫
      FC.map (homotopyPushoutDesc f g a b H)) := by rw [he]; infer_instance
  exact (quasiIso_iff_comp_left _ _).mp this

end Quillen.CochainComplex
