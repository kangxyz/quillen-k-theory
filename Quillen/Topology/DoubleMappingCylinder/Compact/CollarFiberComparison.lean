/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.DoubleMappingCylinder.Compact.CollarCoordinates
public import Quillen.Topology.DoubleMappingCylinder.Compact.CollarFibers

/-! # The original edge hypotheses imply compact HELP on collar comparison fibers

Endpoint and interior fibers are identified by actual embedding charts.
The comparison becomes the identity or the literal original attaching-fiber
map, with no asserted HLP for a collar and no quotient/fiber interchange.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.DoubleCylinder

private def fiberCongr {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (p : C(X, Y)) {y z : Y} (h : y = z) : {x : X // p x = y} ≃ₜ {x : X // p x = z} :=
  Homeomorph.setCongr (by rw [h])

private theorem compactHELP_of_homeomorphs
    {X X' Y Y' : Type u} [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (e : X' ≃ₜ X) (d : Y ≃ₜ Y') (f : C(X, Y)) (g : C(X', Y'))
    (w : (d.toHomotopyEquiv.toFun.comp f).comp e.toHomotopyEquiv.toFun = g)
    (hg : CompactHomotopyExtensionLiftingProperty g) :
    CompactHomotopyExtensionLiftingProperty f := by
  have h : CompactHomotopyExtensionLiftingProperty
      ((d.toHomotopyEquiv.toFun.comp f).comp e.toHomotopyEquiv.toFun) := by rw [w]; exact hg
  exact (h.cancel_first (compactHELP_of_homotopyEquiv e.toHomotopyEquiv)).cancel_second
    (compactHELP_of_homotopyEquiv d.toHomotopyEquiv)

variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (Quillen.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') (cut : unitInterval)

/-- The original left attaching square on its actual strict fibers. -/
def leftAttachingFiberMap (y : A') : C({x : A // a x = y},{x : B // b x = f' y}) where
  toFun x := ⟨f x.val,(ConcreteCategory.congr_hom wf x.val).trans (congrArg f' x.property)⟩
  continuous_toFun := by fun_prop

/-- The original right attaching square on its actual strict fibers. -/
def rightAttachingFiberMap (y : A') : C({x : A // a x = y},{x : C // c x = g' y}) where
  toFun x := ⟨g x.val,(ConcreteCategory.congr_hom wg x.val).trans (congrArg g' x.property)⟩
  continuous_toFun := by fun_prop

theorem leftCollarComparisonFiber_end_compactHELP (hcut : 0 < cut) (y : B') :
    CompactHomotopyExtensionLiftingProperty
      (leftCollarComparisonFiber sq sq' a b c wf wg cut hcut
        (leftCollarInclusion f' g' sq' cut hcut y)) := by
  let pt := leftCollarInclusion f' g' sq' cut hcut y
  let es := leftCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y
  let et := (HomotopyPullback.strictPullbackFiberHomeomorph b.hom
    (leftCollarProjection f' g' sq' cut hcut).hom pt).trans
      (fiberCongr b.hom (leftCollarProjection_end f' g' sq' cut hcut y))
  apply compactHELP_of_homeomorphs es et _ (ContinuousMap.id _)
  · apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    change leftCollarProjection f g sq cut hcut (es z).val = z.val
    rw [leftCollarEndFiberHomeomorph_val,leftCollarProjection_end]
  · exact compactHELP_of_homotopyEquiv (ContinuousMap.HomotopyEquiv.refl _)

theorem rightCollarComparisonFiber_end_compactHELP (hcut : cut < 1) (y : C') :
    CompactHomotopyExtensionLiftingProperty
      (rightCollarComparisonFiber sq sq' a b c wf wg cut hcut
        (rightCollarInclusion f' g' sq' cut hcut y)) := by
  let pt := rightCollarInclusion f' g' sq' cut hcut y
  let es := rightCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y
  let et := (HomotopyPullback.strictPullbackFiberHomeomorph c.hom
    (rightCollarProjection f' g' sq' cut hcut).hom pt).trans
      (fiberCongr c.hom (rightCollarProjection_end f' g' sq' cut hcut y))
  apply compactHELP_of_homeomorphs es et _ (ContinuousMap.id _)
  · apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    change rightCollarProjection f g sq cut hcut (es z).val = z.val
    rw [rightCollarEndFiberHomeomorph_val,rightCollarProjection_end]
  · exact compactHELP_of_homotopyEquiv (ContinuousMap.HomotopyEquiv.refl _)

theorem leftCollarComparisonFiber_interior_compactHELP (hcut : 0 < cut)
    (y : A') (t : OpenInterval) (ht : t.val < cut)
    (hf : CompactHomotopyExtensionLiftingProperty (leftAttachingFiberMap a b wf y)) :
    CompactHomotopyExtensionLiftingProperty
      (leftCollarComparisonFiber sq sq' a b c wf wg cut hcut (leftInteriorPoint sq' cut y t ht))
        := by
  let pt := leftInteriorPoint sq' cut y t ht
  let es := leftCollarInteriorFiberHomeomorph sq sq' a b c wf wg cut y t ht
  let et := (HomotopyPullback.strictPullbackFiberHomeomorph b.hom
    (leftCollarProjection f' g' sq' cut hcut).hom pt).trans
      (fiberCongr b.hom (leftCollarProjection_apply_cylinder f' g' sq' cut hcut y (ULift.up
        t.val) ht))
  apply compactHELP_of_homeomorphs es et _ (leftAttachingFiberMap a b wf y) _ hf
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact leftCollarProjection_apply_cylinder f g sq cut hcut z.val (ULift.up t.val) ht

theorem rightCollarComparisonFiber_interior_compactHELP (hcut : cut < 1)
    (y : A') (t : OpenInterval) (ht : cut < t.val)
    (hg : CompactHomotopyExtensionLiftingProperty (rightAttachingFiberMap a c wg y)) :
    CompactHomotopyExtensionLiftingProperty
      (rightCollarComparisonFiber sq sq' a b c wf wg cut hcut (rightInteriorPoint sq' cut y t
        ht)) := by
  let pt := rightInteriorPoint sq' cut y t ht
  let es := rightCollarInteriorFiberHomeomorph sq sq' a b c wf wg cut y t ht
  let et := (HomotopyPullback.strictPullbackFiberHomeomorph c.hom
    (rightCollarProjection f' g' sq' cut hcut).hom pt).trans
      (fiberCongr c.hom (rightCollarProjection_apply_cylinder f' g' sq' cut hcut y (ULift.up
        t.val) ht))
  apply compactHELP_of_homeomorphs es et _ (rightAttachingFiberMap a c wg y) _ hg
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact rightCollarProjection_apply_cylinder f g sq cut hcut z.val (ULift.up t.val) ht

/-- Every original left-collar comparison fiber has full compact HELP,
from the actual original edge fibers alone. -/
theorem leftCollarComparisonFiber_compactHELP (hcut : 0 < cut)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingFiberMap a b wf y))
    (y : LeftCollar f' g' sq' cut) :
    CompactHomotopyExtensionLiftingProperty (leftCollarComparisonFiber sq sq' a b c wf wg cut
      hcut y) := by
  by_cases hy : height f' g' sq' y.val = 0
  · obtain ⟨z,hz⟩ := height_eq_zero_range f' g' sq' y.val hy
    have he : y = leftCollarInclusion f' g' sq' cut hcut z := Subtype.ext hz.symm
    subst y
    exact leftCollarComparisonFiber_end_compactHELP sq sq' a b c wf wg cut hcut z
  · have hp : 0 < height f' g' sq' y.val :=
      lt_of_le_of_ne (height f' g' sq' y.val).property.1 (Ne.symm hy)
    have hl : height f' g' sq' y.val < 1 := lt_of_lt_of_le y.property cut.property.2
    obtain ⟨z,hz⟩ := interior_surjective f' g' sq' y.val ⟨hp,hl⟩
    have ht : z.2.val < cut := by
      have hh := y.property
      change height f' g' sq' y.val < cut at hh
      rw [← hz,height_cylinder] at hh
      exact hh
    have he : y = leftInteriorPoint sq' cut z.1 z.2 ht := Subtype.ext hz.symm
    subst y
    exact leftCollarComparisonFiber_interior_compactHELP sq sq' a b c wf wg cut hcut z.1 z.2 ht
      (hf z.1)

/-- The corresponding complete right-collar result. -/
theorem rightCollarComparisonFiber_compactHELP (hcut : cut < 1)
    (hg : ∀ y : A',CompactHomotopyExtensionLiftingProperty (rightAttachingFiberMap a c wg y))
    (y : RightCollar f' g' sq' cut) :
    CompactHomotopyExtensionLiftingProperty (rightCollarComparisonFiber sq sq' a b c wf wg cut
      hcut y) := by
  by_cases hy : height f' g' sq' y.val = 1
  · obtain ⟨z,hz⟩ := height_eq_one_range f' g' sq' y.val hy
    have he : y = rightCollarInclusion f' g' sq' cut hcut z := Subtype.ext hz.symm
    subst y
    exact rightCollarComparisonFiber_end_compactHELP sq sq' a b c wf wg cut hcut z
  · have hp : 0 < height f' g' sq' y.val := lt_of_le_of_lt cut.property.1 y.property
    have hl : height f' g' sq' y.val < 1 := lt_of_le_of_ne (height f' g' sq' y.val).property.2 hy
    obtain ⟨z,hz⟩ := interior_surjective f' g' sq' y.val ⟨hp,hl⟩
    have ht : cut < z.2.val := by
      have hh := y.property
      change cut < height f' g' sq' y.val at hh
      rw [← hz,height_cylinder] at hh
      exact hh
    have he : y = rightInteriorPoint sq' cut z.1 z.2 ht := Subtype.ext hz.symm
    subst y
    exact rightCollarComparisonFiber_interior_compactHELP sq sq' a b c wf wg cut hcut z.1 z.2 ht
      (hg z.1)

/-- The original left collar is a compact-HELP quasifibration at every point,
using only actual endpoint lifting and original edge-fiber HELP. -/
theorem leftCollar_strictFiberInclusion_compactHELP_of_edge (hcut : 0 < cut)
    (hb : HomotopyLiftingProperty b.hom)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingFiberMap a b wf y))
    (y : LeftCollar f' g' sq' cut) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y) :=
  leftCollar_strictFiberInclusion_compactHELP sq sq' a b c wf wg cut hcut hb y
    (leftCollarComparisonFiber_compactHELP sq sq' a b c wf wg cut hcut hf y)

/-- The matching statement for the original right collar and its original fibers. -/
theorem rightCollar_strictFiberInclusion_compactHELP_of_edge (hcut : cut < 1)
    (hc : HomotopyLiftingProperty c.hom)
    (hg : ∀ y : A',CompactHomotopyExtensionLiftingProperty (rightAttachingFiberMap a c wg y))
    (y : RightCollar f' g' sq' cut) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y) :=
  rightCollar_strictFiberInclusion_compactHELP sq sq' a b c wf wg cut hcut hc y
    (rightCollarComparisonFiber_compactHELP sq sq' a b c wf wg cut hcut hg y)

end Quillen.DoubleCylinder
