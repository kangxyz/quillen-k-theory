/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.PushoutReduction
public import Quillen.Topology.DoubleMappingCylinder.WeakInvariance
public import Quillen.Topology.Prespectrum.PositiveLevelEquivalence

/-!
# Complete weak equivalence of original reduced homotopy-pushout maps

Complete weak equivalences on all three original vertices induce a complete weak equivalence of
the actual strict reduced-pushout map when all six chosen points have HEP. The literal reduction
maps identify this with the genuine ordinary double-cylinder comparison. Positive-level weakness
then gives equivalence on the unchanged signed stable groups.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.HomotopyPushout

variable {A B C A' B' C' : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

/-- Objectwise complete weak maps give the original reduced pushout weak map under genuine HEP
of its six specified points. -/
theorem map_level_isWeakHomotopyEquivalence (n : ℕ)
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
    IsWeakHomotopyEquivalence ((map f g f' g' a b c wf wg).map n) := by
  have wfₙ : TopCat.ofHom (f.map n) ≫ TopCat.ofHom (b.map n) =
      TopCat.ofHom (a.map n) ≫ TopCat.ofHom (f'.map n) := by
    ext x
    exact congrArg (fun h ↦ h.map n x) wf
  have wgₙ : TopCat.ofHom (g.map n) ≫ TopCat.ofHom (c.map n) =
      TopCat.ofHom (a.map n) ≫ TopCat.ofHom (g'.map n) := by
    ext x
    exact congrArg (fun h ↦ h.map n x) wg
  let m := DoubleCylinder.map (unreducedSquare f g n) (unreducedSquare f' g' n)
    (TopCat.ofHom (a.map n)) (TopCat.ofHom (b.map n)) (TopCat.ofHom (c.map n)) wfₙ wgₙ
  have hm : IsWeakHomotopyEquivalence m.hom :=
    DoubleCylinder.map_isWeakHomotopyEquivalence (unreducedSquare f g n)
      (unreducedSquare f' g' n) (TopCat.ofHom (a.map n)) (TopCat.ofHom (b.map n))
      (TopCat.ofHom (c.map n)) wfₙ wgₙ ha hb hc
  have hw : reduction f g n ≫ TopCat.ofHom ((map f g f' g' a b c wf wg).map n) =
      m ≫ reduction f' g' n := by
    apply (unreducedSquare f g n).hom_ext
    · ext ⟨x, t⟩
      change (map f g f' g' a b c wf wg).map n
          (reduction f g n (unreducedCylinder f g n (x, t))) =
        reduction f' g' n (m (unreducedCylinder f g n (x, t)))
      rw [reduction_cylinder]
      rw [show m (unreducedCylinder f g n (x, t)) =
        unreducedCylinder f' g' n (a.map n x, t) from
          DoubleCylinder.map_cylinder_apply (unreducedSquare f g n) (unreducedSquare f' g' n)
            (TopCat.ofHom (a.map n)) (TopCat.ofHom (b.map n)) (TopCat.ofHom (c.map n))
            wfₙ wgₙ x t]
      rw [reduction_cylinder]
      rfl
    · ext z
      cases z with
      | inl y =>
        change (map f g f' g' a b c wf wg).map n
            (reduction f g n (unreducedEnd f g n (Sum.inl y))) =
          reduction f' g' n (m (unreducedEnd f g n (Sum.inl y)))
        rw [reduction_end]
        rw [show m (unreducedEnd f g n (Sum.inl y)) =
          unreducedEnd f' g' n (Sum.inl (b.map n y)) from
            DoubleCylinder.map_left (unreducedSquare f g n) (unreducedSquare f' g' n)
              (TopCat.ofHom (a.map n)) (TopCat.ofHom (b.map n)) (TopCat.ofHom (c.map n))
              wfₙ wgₙ y]
        rw [reduction_end]
        rfl
      | inr z =>
        change (map f g f' g' a b c wf wg).map n
            (reduction f g n (unreducedEnd f g n (Sum.inr z))) =
          reduction f' g' n (m (unreducedEnd f g n (Sum.inr z)))
        rw [reduction_end]
        rw [show m (unreducedEnd f g n (Sum.inr z)) =
          unreducedEnd f' g' n (Sum.inr (c.map n z)) from
            DoubleCylinder.map_right (unreducedSquare f g n) (unreducedSquare f' g' n)
              (TopCat.ofHom (a.map n)) (TopCat.ofHom (b.map n)) (TopCat.ofHom (c.map n))
              wfₙ wgₙ z]
        rw [reduction_end]
        rfl
  have hs := isWeakHomotopyEquivalence_of_homotopyEquiv (reductionHomotopyEquiv f g n hA hB hC)
  have ht := isWeakHomotopyEquivalence_of_homotopyEquiv
    (reductionHomotopyEquiv f' g' n hA' hB' hC')
  have h := ht.comp hm
  change IsWeakHomotopyEquivalence ((m ≫ reduction f' g' n).hom) at h
  rw [← hw] at h
  exact h.of_comp_left hs

/-- Positive-level complete weak side maps preserve the actual strict reduced-pushout stable map,
with HEP at each of the six actual positive-level points. -/
theorem map_isStableEquivalence_of_positiveLevel
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
    IsStableEquivalence (map f g f' g' a b c wf wg) :=
  isStableEquivalence_of_positiveLevel _ fun n ↦
    map_level_isWeakHomotopyEquivalence f g f' g' a b c wf wg (n + 1)
      (hA n) (hB n) (hC n) (hA' n) (hB' n) (hC' n) (ha n) (hb n) (hc n)

end Quillen.LoopPrespectrum.HomotopyPushout
