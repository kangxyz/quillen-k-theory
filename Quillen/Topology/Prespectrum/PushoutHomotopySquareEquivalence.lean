/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.PushoutArrowHomotopy
public import Quillen.Topology.Prespectrum.PushoutHomotopySquare
public import Quillen.Topology.Prespectrum.PushoutWeakEquivalence

/-!
# Weak comparison of the original whole-track reduced-pushout map

The existing mapOfHomotopies factors literally through two strict vertex maps and two actual
arrow-change homotopy equivalences. Both complete supplied square tracks are retained. Complete
weak equivalences at all three original vertices and HEP at all six actual chosen points therefore
imply complete weakness of the original map, and positive levels give original stable equivalence.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.HomotopyPushout

variable {A B C A' B' C' : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))

/-- The original reduced-pushout map factors on both endpoints and every original cylinder value,
with the complete first and reversed second supplied tracks retained in the middle factors. -/
theorem mapOfHomotopies_factor :
    mapOfHomotopies f g f' g' a b c Hf Hg =
      map f g (f ≫ b) (g ≫ c) (𝟙 A) b c (by simp) (by simp) ≫
      leftHomotopyMap Hf (g ≫ c) ≫ rightHomotopyMap (a ≫ f') Hg ≫
      map (a ≫ f') (a ≫ g') f' g' a (𝟙 B') (𝟙 C') (by simp) (by simp) := by
  apply hom_ext
  · apply Hom.ext; funext n; ext y; rfl
  · apply Hom.ext; funext n; ext z; rfl
  · intro n s x
    let m := map (a ≫ f') (a ≫ g') f' g' a (𝟙 B') (𝟙 C') (by simp) (by simp)
    have h₁ : (((Hf.postcomp (inl (a ≫ f') (g ≫ c))).trans
        (glue (a ≫ f') (g ≫ c))).postcomp (rightHomotopyMap (a ≫ f') Hg)) =
        (Hf.postcomp (inl (a ≫ f') (a ≫ g'))).trans
          ((glue (a ≫ f') (a ≫ g')).trans (Hg.symm.postcomp (inr (a ≫ f') (a ≫ g')))) := by
      rw [Homotopy.postcomp_trans]
      rw [show (glue (a ≫ f') (g ≫ c)).postcomp (rightHomotopyMap (a ≫ f') Hg) =
        (glue (a ≫ f') (a ≫ g')).trans (Hg.symm.postcomp (inr (a ≫ f') (a ≫ g')))
        from glue_desc _ _ _ _ _]
      congr 1
    have h₂ : (((Hf.postcomp (inl (a ≫ f') (a ≫ g'))).trans
        ((glue (a ≫ f') (a ≫ g')).trans
          (Hg.symm.postcomp (inr (a ≫ f') (a ≫ g'))))).postcomp m) =
        mapSquareHomotopy f g f' g' a b c Hf Hg := by
      rw [Homotopy.postcomp_trans, Homotopy.postcomp_trans]
      rfl
    exact (congrArg (fun J ↦ J.level n (s, x))
      ((congrArg (fun J ↦ J.postcomp m) h₁).trans h₂)).symm

/-- Complete weak vertex maps give complete weakness of the unchanged whole-track pushout map,
under genuine HEP of its six chosen points. -/
theorem mapOfHomotopies_level_isWeakHomotopyEquivalence (n : ℕ)
    (hA : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point n))))
    (hB : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point n))))
    (hC : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point n))))
    (hA' : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A'.point n))))
    (hB' : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B'.point n))))
    (hC' : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C'.point n))))
    (ha : IsWeakHomotopyEquivalence (a.map n)) (hb : IsWeakHomotopyEquivalence (b.map n))
    (hc : IsWeakHomotopyEquivalence (c.map n)) :
    IsWeakHomotopyEquivalence ((mapOfHomotopies f g f' g' a b c Hf Hg).map n) := by
  have h₁ := map_level_isWeakHomotopyEquivalence f g (f ≫ b) (g ≫ c) (𝟙 A) b c
    (by simp) (by simp) n hA hB hC hA hB' hC' (isWeakHomotopyEquivalence_id _) hb hc
  have h₂ := map_level_isWeakHomotopyEquivalence (a ≫ f') (a ≫ g') f' g' a (𝟙 B') (𝟙 C')
    (by simp) (by simp) n hA hB' hC' hA' hB' hC' ha
    (isWeakHomotopyEquivalence_id _) (isWeakHomotopyEquivalence_id _)
  rw [mapOfHomotopies_factor]
  exact h₂.comp ((isWeakHomotopyEquivalence_of_homotopyEquiv
    (rightHomotopyMapLevelEquiv (a ≫ f') Hg n)).comp
      ((isWeakHomotopyEquivalence_of_homotopyEquiv
        (leftHomotopyMapLevelEquiv Hf (g ≫ c) n)).comp h₁))

/-- Positive-level complete weak vertex maps preserve the original whole-track pushout stable
map, with HEP at each of the six actual positive-level points. -/
theorem mapOfHomotopies_isStableEquivalence_of_positiveLevel
    (hA : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point (n + 1)))))
    (hB : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point (n + 1)))))
    (hC : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point (n + 1)))))
    (hA' : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A'.point (n + 1)))))
    (hB' : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B'.point (n + 1)))))
    (hC' : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C'.point (n + 1)))))
    (ha : ∀ n, IsWeakHomotopyEquivalence (a.map (n + 1)))
    (hb : ∀ n, IsWeakHomotopyEquivalence (b.map (n + 1)))
    (hc : ∀ n, IsWeakHomotopyEquivalence (c.map (n + 1))) :
    IsStableEquivalence (mapOfHomotopies f g f' g' a b c Hf Hg) :=
  isStableEquivalence_of_positiveLevel _ fun n ↦
    mapOfHomotopies_level_isWeakHomotopyEquivalence f g f' g' a b c Hf Hg (n + 1)
      (hA n) (hB n) (hC n) (hA' n) (hB' n) (hC' n) (ha n) (hb n) (hc n)

end Quillen.LoopPrespectrum.HomotopyPushout
