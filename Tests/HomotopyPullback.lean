/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Algebra.Homology.HomotopyPullbackQuasiIso
import Quillen.PerfectComplexes.HomotopyPullback

/-! Semantic consumers of the actual mapping-cocone homotopy pullback. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry
open Quillen.CochainComplex Quillen.PerfectComplexes
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.Tests.HomotopyPullback

/-- A homotopy-commuting pair with weak first component rectifies to an actual
weak chain map, retaining both original chain-map equations. -/
theorem actual_weak_rectification {C : Type u} [Category.{v} C] [Abelian C]
    {A B T M : CochainComplex C ℤ} (f : A ⟶ T) (g : B ⟶ T)
    (a : M ⟶ A) (b : M ⟶ B) (h : Homotopy (a ≫ f) (b ≫ g))
    [QuasiIso g] [QuasiIso a] :
    ∃ l : M ⟶ homotopyPullback f g,
      l ≫ homotopyPullbackFst f g = a ∧ l ≫ homotopyPullbackSnd f g = b ∧
      ∀ n : ℤ, IsIso (homologyMap l n) := by
  have := quasiIso_homotopyPullbackLift f g a b h
  exact ⟨homotopyPullbackLift f g a b h, homotopyPullbackLift_fst _ _ _ _ _,
    homotopyPullbackLift_snd _ _ _ _ _, fun _ => inferInstance⟩

/-- Symmetric gluing only needs the original first leg and second component
weak; the other leg and component remain unrestricted. -/
theorem actual_symmetric_rectification {C : Type u} [Category.{v} C] [Abelian C]
    {A B T M : CochainComplex C ℤ} (f : A ⟶ T) (g : B ⟶ T)
    (a : M ⟶ A) (b : M ⟶ B) (h : Homotopy (a ≫ f) (b ≫ g))
    [QuasiIso f] [QuasiIso b] :
    ∃ l : M ⟶ homotopyPullback f g,
      l ≫ homotopyPullbackFst f g = a ∧ l ≫ homotopyPullbackSnd f g = b ∧
      ∀ n : ℤ, IsIso (homologyMap l n) := by
  have := quasiIso_homotopyPullbackLift_of_snd f g a b h
  exact ⟨homotopyPullbackLift f g a b h, homotopyPullbackLift_fst _ _ _ _ _,
    homotopyPullbackLift_snd _ _ _ _ _, fun _ => inferInstance⟩

/-- A single preceding-degree epimorphism gives unique lifting on actual
homology, without assuming either original chain map a quasi-isomorphism. -/
theorem actual_homology_unique_lift {C : Type u} [Category.{v} C] [Abelian C]
    {A B T : CochainComplex C ℤ} (f : A ⟶ T) (g : B ⟶ T) (n : ℤ)
    [Epi (homologyMap (biprod.desc f (-g)) (n-1))]
    {D : C} (a : D ⟶ A.homology n) (b : D ⟶ B.homology n)
    (h : a ≫ homologyMap f n = b ≫ homologyMap g n) :
    ∃! l : D ⟶ (homotopyPullback f g).homology n,
      l ≫ homologyMap (homotopyPullbackFst f g) n = a ∧
      l ≫ homologyMap (homotopyPullbackSnd f g) n = b := by
  let hp := homology_homotopyPullback_isPullback f g n
  refine ⟨hp.lift a b h, ⟨hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩, ?_⟩
  intro l hl
  apply hp.hom_ext
  · exact hl.1.trans (hp.lift_fst a b h).symm
  · exact hl.2.trans (hp.lift_snd a b h).symm

/-- Both original projection components have actual sections in every integer
degree even when neither leg is weak and the complexes are unbounded. -/
theorem actual_degreewise_sections {C : Type u} [Category.{v} C] [Abelian C]
    {A B T : CochainComplex C ℤ} (f : A ⟶ T) (g : B ⟶ T) (n : ℤ) :
    (∃ s : A.X n ⟶ (homotopyPullback f g).X n,
      s ≫ (homotopyPullbackFst f g).f n = 𝟙 _) ∧
    ∃ s : B.X n ⟶ (homotopyPullback f g).X n,
      s ≫ (homotopyPullbackSnd f g).f n = 𝟙 _ :=
  ⟨⟨(homotopyPullbackFstSplitEpi f g n).section_, (homotopyPullbackFstSplitEpi f g n).id⟩,
    ⟨(homotopyPullbackSndSplitEpi f g n).section_, (homotopyPullbackSndSplitEpi f g n).id⟩⟩

/-- The original projection homotopy gives the expected equality in the
actual homotopy category, including without a weak-leg hypothesis. -/
theorem actual_homotopy_category_square {C : Type u} [Category.{v} C] [Abelian C]
    {A B T : CochainComplex C ℤ} (f : A ⟶ T) (g : B ⟶ T) :
    (HomotopyCategory.quotient C (.up ℤ)).map (homotopyPullbackFst f g) ≫
      (HomotopyCategory.quotient C (.up ℤ)).map f =
    (HomotopyCategory.quotient C (.up ℤ)).map (homotopyPullbackSnd f g) ≫
      (HomotopyCategory.quotient C (.up ℤ)).map g := by
  simpa only [← Functor.map_comp] using
    HomotopyCategory.eq_of_homotopy _ _ (homotopyPullbackProjectionHomotopy f g)

/-- The literal weak projection has a locally perfect source on every scheme;
no quasi-compactness or termwise quasicoherence is supplied. -/
theorem actual_local_perfect_projection {X : Scheme.{u}} {A B T : Complex X}
    (hA : locallyPerfect X A) (hB : locallyPerfect X B) (hT : locallyPerfect X T)
    (f : A ⟶ T) (g : B ⟶ T) [QuasiIso g] :
    locallyPerfect X (homotopyPullback f g) ∧
      ∀ n : ℤ, IsIso (homologyMap (homotopyPullbackFst f g) n) := by
  have := quasiIso_homotopyPullbackFst f g
  exact ⟨locallyPerfect_homotopyPullback hA hB hT f g, fun _ => inferInstance⟩

/-- The source used for strict rectification stays in the original strict
model, and the identity opposite leg makes its original first projection weak. -/
theorem actual_strict_identity_leg {X : Scheme.{u}} {A P : Complex X}
    (hA : strictPerfect X A) (hP : strictPerfect X P) (f : A ⟶ P) :
    strictPerfect X (homotopyPullback f (𝟙 P)) ∧
      ∀ n : ℤ, IsIso (homologyMap (homotopyPullbackFst f (𝟙 P)) n) := by
  have := quasiIso_homotopyPullbackFst f (𝟙 P)
  exact ⟨strictPerfect_homotopyPullback hA hP hP f (𝟙 P), fun _ => inferInstance⟩

end Quillen.Tests.HomotopyPullback
