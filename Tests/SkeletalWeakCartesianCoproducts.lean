/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.CategoryTheory.TheoremB.SkeletalWeakCartesianCoproducts

/-!
# Weak fixed-target coproduct regression consumers

Actual arbitrary coproduct cocones, arbitrary summand topologies and an
empty index type are admitted. Coordinate checks retain the genuine cofan
injections and the entire original constant comparison path.
-/
noncomputable section
open CategoryTheory Limits
open Quillen Quillen.TheoremB.SkeletalCartesian
open scoped Topology unitInterval
universe u

section Sigma
variable {ι : Type u} {X A : ι → Type u} [∀ i,TopologicalSpace (X i)] [∀ i,TopologicalSpace (A i)]
  {E T : Type u} [TopologicalSpace E] [TopologicalSpace T]
  (q : C(E,T)) (s : ∀ i,C(A i,T)) (p : ∀ i,C(X i,A i)) (t : ∀ i,C(X i,E))
  (w : ∀ i,q.comp (t i) = (s i).comp (p i))

example (h : ∀ i,WeakCartesian (p i) q (t i) (s i) (w i)) :
    WeakCartesian (sigmaMap p) q (ContinuousMap.sigma t) (ContinuousMap.sigma s)
      (sigmaFixedSquare q s p t w) := weakCartesianSigmaFixedTarget q s p t w h

example (i : ι) (x : X i) (τ : unitInterval) :
    (HomotopyPullback.comparison q (ContinuousMap.sigma s) (sigmaMap p) (ContinuousMap.sigma t)
      (sigmaFixedSquare q s p t w) ⟨i,x⟩).val.2.2 τ = s i (p i x) := rfl

example (i : ι) (x : X i) :
    (HomotopyPullback.comparison q (ContinuousMap.sigma s) (sigmaMap p) (ContinuousMap.sigma t)
      (sigmaFixedSquare q s p t w) ⟨i,x⟩).val.1 = ⟨i,p i x⟩ := rfl
end Sigma

section EmptyIndex
variable {X A : PEmpty.{u+1} → Type u} [∀ i,TopologicalSpace (X i)] [∀ i,TopologicalSpace (A i)]
  {E T : Type u} [TopologicalSpace E] [TopologicalSpace T]
  (q : C(E,T)) (s : ∀ i,C(A i,T)) (p : ∀ i,C(X i,A i)) (t : ∀ i,C(X i,E))
  (w : ∀ i,q.comp (t i) = (s i).comp (p i))

example : WeakCartesian (sigmaMap p) q (ContinuousMap.sigma t) (ContinuousMap.sigma s)
    (sigmaFixedSquare q s p t w) :=
  weakCartesianSigmaFixedTarget q s p t w (fun i ↦ nomatch i)
end EmptyIndex

section Colimits
variable {ι : Type u} (W A : ι → TopCat.{u}) (cW : Cofan W) (cA : Cofan A)
  (hW : IsColimit cW) (hA : IsColimit cA)
  {E T : TopCat.{u}} (q : E ⟶ T)
  (p : cW.pt ⟶ cA.pt) (t : cW.pt ⟶ E) (s : cA.pt ⟶ T)
  (wtotal : t ≫ q = p ≫ s)
  (ps : ∀ i,W i ⟶ A i) (ts : ∀ i,W i ⟶ E) (ss : ∀ i,A i ⟶ T)
  (ws : ∀ i,ts i ≫ q = ps i ≫ ss i)
  (wp : ∀ i,cW.inj i ≫ p = ps i ≫ cA.inj i)
  (wt : ∀ i,cW.inj i ≫ t = ts i)
  (wb : ∀ i,cA.inj i ≫ s = ss i)

include hW hA wp wt wb in
example (h : ∀ i,WeakCartesian (ps i).hom q.hom (ts i).hom (ss i).hom
    (congrArg TopCat.Hom.hom (ws i))) :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison q.hom s.hom p.hom t.hom (congrArg TopCat.Hom.hom wtotal)) :=
  weakCartesianCofanFixedTarget W A cW cA hW hA q p t s wtotal ps ts ss ws wp wt wb h

include hW hA in
example (hp : ∀ i,ps i ≫ cA.inj i = cW.inj i ≫ p)
    (h : ∀ i,WeakCartesian (ps i).hom q.hom (cW.inj i ≫ t).hom (cA.inj i ≫ s).hom
      (congrArg TopCat.Hom.hom (cofanFixedSquare W A cW cA q p t s wtotal ps i (hp i)))) :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison q.hom s.hom p.hom t.hom (congrArg TopCat.Hom.hom wtotal)) :=
  weakCartesianCofanFixedTargetOfInclusions W A cW cA hW hA q p t s wtotal ps hp h

example (i : ι) (x : W i) : cofanHomeomorph W cW hW ⟨i,x⟩ = cW.inj i x :=
  cofanHomeomorph_apply W cW hW i x

example (z : cW.pt) (τ : unitInterval) :
    (HomotopyPullback.comparison q.hom s.hom p.hom t.hom (congrArg TopCat.Hom.hom wtotal) z).val.2.2 τ =
      s (p z) := rfl
end Colimits
