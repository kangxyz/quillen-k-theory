/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.HomotopyPushoutMap

/-! # Actual homotopy-pushout and local weak-gluing consumers -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Quillen.CochainComplex
universe u v u' v'
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Tests.HomotopyPushout
variable {C : Type u} [Category.{v} C] [Abelian C]
  {T A B : CochainComplex C ℤ} (f : T ⟶ A) (g : T ⟶ B)

/-- A given original overlap homotopy yields an actual map solving both chain equations. -/
theorem strict_descent_equations {M : CochainComplex C ℤ} (a : A ⟶ M) (b : B ⟶ M)
    (H : Homotopy (f ≫ a) (g ≫ b)) :
    ∃ d : homotopyPushout f g ⟶ M,
      homotopyPushoutInl f g ≫ d = a ∧ homotopyPushoutInr f g ≫ d = b :=
  ⟨homotopyPushoutDesc f g a b H, homotopyPushoutInl_desc f g a b H,
    homotopyPushoutInr_desc f g a b H⟩

/-- Both actual injections have honest retractions in each original degree. -/
theorem original_degreewise_retractions (i : ℤ) :
    (∃ r, (homotopyPushoutInl f g).f i ≫ r = 𝟙 _) ∧
    (∃ r, (homotopyPushoutInr f g).f i ≫ r = 𝟙 _) :=
  ⟨⟨(homotopyPushoutInlSplitMono f g i).retraction, (homotopyPushoutInlSplitMono f g i).id⟩,
    ⟨(homotopyPushoutInrSplitMono f g i).retraction, (homotopyPushoutInrSplitMono f g i).id⟩⟩

/-- The original inclusions satisfy an actual overlap chain homotopy. -/
def actual_overlap_homotopy :
    Homotopy (f ≫ homotopyPushoutInl f g) (g ≫ homotopyPushoutInr f g) :=
  homotopyPushoutInclusionHomotopy f g

/-- Gluing along an identity overlap retains the original first summand quasi-isomorphically. -/
theorem identity_overlap_contraction : QuasiIso (homotopyPushoutInl f (𝟙 T)) :=
  quasiIso_homotopyPushoutInl f (𝟙 T)

/-- Next-degree injectivity gives unique actual homology descent, not merely a dimension count. -/
theorem actual_homology_pushout_desc (n : ℤ)
    [Mono (homologyMap (biprod.lift f (-g)) (n+1))]
    {M : C} (a : homology A n ⟶ M) (b : homology B n ⟶ M)
    (h : homologyMap f n ≫ a = homologyMap g n ≫ b) :
    ∃! d : homology (homotopyPushout f g) n ⟶ M,
      homologyMap (homotopyPushoutInl f g) n ≫ d = a ∧
      homologyMap (homotopyPushoutInr f g) n ≫ d = b := by
  let sq := homology_homotopyPushout_isPushout f g n
  refine ⟨sq.desc a b h, ⟨sq.inl_desc a b h, sq.inr_desc a b h⟩, ?_⟩
  intro d hd
  apply sq.hom_ext
  · exact hd.1.trans (sq.inl_desc a b h).symm
  · exact hd.2.trans (sq.inr_desc a b h).symm

section Mapped
variable {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]

/-- The genuine comparison isomorphism preserves both actual mapped inclusions. -/
theorem original_mapped_inclusions :
    (F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutInl f g) ≫
      (homotopyPushoutMapIso F f g).hom =
      homotopyPushoutInl ((F.mapHomologicalComplex (.up ℤ)).map f)
        ((F.mapHomologicalComplex (.up ℤ)).map g) ∧
    (F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutInr f g) ≫
      (homotopyPushoutMapIso F f g).hom =
      homotopyPushoutInr ((F.mapHomologicalComplex (.up ℤ)).map f)
        ((F.mapHomologicalComplex (.up ℤ)).map g) :=
  ⟨homotopyPushoutMapIso_inl F f g, homotopyPushoutMapIso_inr F f g⟩

/-- Only mapped overlap weakness is needed, even if no global quasi-isomorphism is given. -/
theorem local_first_inclusion [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map g)] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutInl f g)) :=
  quasiIso_map_homotopyPushoutInl F f g

/-- Local target gluing retains the entire original mapped descent and strict first equation. -/
theorem local_original_descent {M : CochainComplex C ℤ}
    (a : A ⟶ M) (b : B ⟶ M) (H : Homotopy (f ≫ a) (g ≫ b))
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map g)]
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map a)] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutDesc f g a b H)) ∧
    (F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutInl f g) ≫
      (F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutDesc f g a b H) =
      (F.mapHomologicalComplex (.up ℤ)).map a := by
  refine ⟨quasiIso_map_homotopyPushoutDesc F f g a b H, ?_⟩
  rw [← Functor.map_comp, homotopyPushoutInl_desc]

/-- Symmetric local target gluing does not require the first target map to be weak. -/
theorem local_original_descent_second {M : CochainComplex C ℤ}
    (a : A ⟶ M) (b : B ⟶ M) (H : Homotopy (f ≫ a) (g ≫ b))
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f)]
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map b)] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (homotopyPushoutDesc f g a b H)) :=
  quasiIso_map_homotopyPushoutDesc_of_inr F f g a b H
end Mapped
end Tests.HomotopyPushout
