/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.CategoryTheory.TheoremB.NormalizedBridgeWeakBaseChange

/-!
# Regressions for actual bridge charts and arbitrary-parameter base changes

The source and target coordinates are the original maps, the overlap is a
genuine two-collar pushout, and all stored vertical paths survive injective
base transport. Final consumers require no compactness of the new parameter.
-/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open Quillen Quillen.TheoremB Quillen.TheoremB.FiberwiseBridgeSourceCharts
open Quillen.FiberwiseMappingPath
open scoped Topology unitInterval
universe u

section Charts
variable {A B C M N Z : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {lM : A ⊗ TopCat.I ⟶ M} {cM : B ⟶ M}
  {lN : A ⊗ TopCat.I ⟶ N} {cN : C ⟶ N}
  (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f lM cM)
  (sqN : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) g lN cN)
  {m : M ⟶ Z} {n : N ⟶ Z}
  (sq : IsPushout (TopCat.ι₀ ≫ lM) (TopCat.ι₀ ≫ lN) m n)
  (cut : unitInterval) (hcut : 0 < cut)

example (x : MappingCylinderSourceCollar.Collar sqM cut) :
    (sideCollar sqM sq cut x).val = m x.val := rfl

example (x : N) : (sideEnd sqM sq cut hcut x).val = n x := rfl

example : IsPushout (MappingCylinderSourceCollar.source sqM cut hcut) (TopCat.ι₀ ≫ lN)
    (sideCollar sqM sq cut) (sideEnd sqM sq cut hcut) := side_isPushout sqM sq cut hcut

example : IsPushout (MappingCylinderSourceCollar.source sqM cut hcut)
    (MappingCylinderSourceCollar.source sqN cut hcut)
    (intersectionLeft sqM sq cut hcut sqN) (intersectionRight sqM sq cut hcut sqN) :=
  intersection_isPushout sqM sq cut hcut sqN

example : sideSet sqM sq cut ∪ sideSet sqN sq.flip cut = Set.univ := side_cover sqM sq cut hcut sqN

example : m ⁻¹' intersectionSet sqM sq cut sqN = MappingCylinderSourceCollar.collarSet sqM cut :=
  intersection_preimage_left sqM sq cut hcut sqN

example (x : MappingCylinderSourceCollar.Collar sqM cut) (t : TopCat.I) :
    (intersectionStrongDeformationRetract sqM sq cut hcut sqN).H
      (intersectionLeft sqM sq cut hcut sqN x,t) = intersectionLeft sqM sq cut hcut sqN x :=
  ConcreteCategory.congr_hom (intersectionStrongDeformationRetract sqM sq cut hcut sqN).fixed (x,t)

example {T : TopCat.{u}} (b : B ⟶ T) (c : C ⟶ T) (w : f ≫ b = g ≫ c)
    {D : Type u} [TopologicalSpace D] (a : C(D,T))
    (hs : IsWeakHomotopyEquivalence
      (baseChangedMap (TheoremA.mappingCylinderProjection sqN ≫ c).hom (TopCat.ι₀ ≫ lN).hom a)) :
    IsWeakHomotopyEquivalence (baseChangedMap (FiberwiseBridge.projection sqM sqN sq b c w).hom m.hom a) :=
  left_baseChange_isWeakHomotopyEquivalence sqM sqN sq a b c w hs
end Charts

section Paths
variable {E F B T : Type u} [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace B] [TopologicalSpace T]
  (q : C(F,B)) (f : C(E,F)) (j : C(B,T)) (hj : Function.Injective j)

example (x : Space (j.comp q) f) (t : unitInterval) :
    (injectiveBaseHomeomorph q f j hj x).val.2 t = x.val.2 t := rfl

example (x : Space (j.comp q) f) : (injectiveBaseHomeomorph q f j hj x).val.1 = x.val.1 := rfl

example (h : CubicalSubdivision.BoundaryLifting (endpoint q f))
    (n : ℕ) (a : C(CubicalSubdivision.Boundary n,Space (j.comp q) f))
    (b : C(CubicalSubdivision.Cube n,F)) (hab : ∀ x,endpoint (j.comp q) f (a x) = b x.val) :
    ∃ l : C(CubicalSubdivision.Cube n,Space (j.comp q) f),
      (∀ x : CubicalSubdivision.Boundary n,l x.val = a x) ∧ (endpoint (j.comp q) f).comp l = b :=
  endpoint_boundaryLifting_of_injective_base q f j hj h n a b hab
end Paths

section Normalized
variable {T : TopCat.{u}} {U V : Set T} (d : NormalizedFibrationSpan.Data T U V)
  [T2Space T] {D : Type u} [TopologicalSpace D] (a : C(D,T))

example (hp1 : HomotopyLiftingProperty d.p1.hom)
    (hR1 : HomotopyLiftingProperty (d.k1 ≫ d.q1).hom)
    (hf1 : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (d.k1 ≫ d.q1).hom d.q1.hom d.k1.hom rfl t)) :
    IsWeakHomotopyEquivalence (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i0.hom a) := by
  apply d.bridgeEnd0_baseChange_isWeak_of_closedGraphs hp1 hR1 _ hf1 a
  intro S _ _ _ b
  exact isClosed_eq (b.continuous.comp continuous_fst) continuous_snd

example (hp0 : HomotopyLiftingProperty d.p0.hom)
    (hR0 : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
    (hf0 : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (d.k0 ≫ d.q0).hom d.q0.hom d.k0.hom rfl t)) :
    IsWeakHomotopyEquivalence (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i1.hom a) := by
  apply d.bridgeEnd1_baseChange_isWeak_of_closedGraphs hp0 hR0 _ hf0 a
  intro S _ _ _ b
  exact isClosed_eq (b.continuous.comp continuous_fst) continuous_snd

example (x : BaseChangedSource d.normalized.bridgeBase.hom d.normalized.i0.hom a) :
    (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i0.hom a x).val =
      (x.val.1,d.normalized.i0 x.val.2) := rfl

example (x : BaseChangedSource d.normalized.bridgeBase.hom d.normalized.i1.hom a) :
    (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i1.hom a x).val =
      (x.val.1,d.normalized.i1 x.val.2) := rfl
end Normalized
